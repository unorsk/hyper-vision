import HyperVision.Geometry
import HyperVision.Color

/-!
# Screen buffer and drawing

`Screen` is a flat, row-major cell buffer whose size invariant is carried as a
proof. Views draw through `DrawM`, a monad whose every value carries a proof that
it never changes a cell outside the current viewport's clip rectangle: clipping
is guaranteed by construction, for library and user widgets alike.
-/

namespace HyperVision

/-- One character cell. -/
structure Cell where
  ch : Char := ' '
  attr : Attr := ⟨.lightGray, .black⟩
deriving DecidableEq, Inhabited, Repr

/-- Row-major index of `(x, y)` in a `w × h` grid, if the position lies on it. -/
def gridIndex? (w h : Nat) (x y : Int) : Option Nat :=
  if 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < h then some (y.toNat * w + x.toNat) else none

theorem gridIndex?_lt {w h i : Nat} {x y : Int} (hi : gridIndex? w h x y = some i) : i < w * h := by
  unfold gridIndex? at hi
  split at hi
  · next hb =>
    obtain ⟨hx0, hxw, hy0, hyh⟩ := hb
    cases hi
    have : (y.toNat + 1) * w ≤ h * w := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this
    rw [Nat.mul_comm w h]
    omega
  · cases hi

/-- Distinct positions have distinct indices. -/
theorem gridIndex?_inj {w h i : Nat} {x y x' y' : Int} (h₁ : gridIndex? w h x y = some i)
    (h₂ : gridIndex? w h x' y' = some i) : x = x' ∧ y = y' := by
  unfold gridIndex? at h₁ h₂
  split at h₁ <;> split at h₂ <;> simp only [Option.some.injEq, reduceCtorEq] at h₁ h₂
  next hb hb' =>
    have hw : 0 < w := by omega
    have heq := h₁.trans h₂.symm
    have hm := congrArg (· % w) heq
    have hd := congrArg (· / w) heq
    simp only [Nat.add_comm (_ * w), Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hw] at hm hd
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hm
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)] at hd
    omega

theorem gridIndex?_isSome {w h : Nat} {x y : Int} :
    (gridIndex? w h x y).isSome ↔ 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < h := by
  unfold gridIndex?; split <;> simp_all

/-- A `width × height` grid of cells, stored row-major. -/
structure Screen where
  width : Nat
  height : Nat
  cells : Array Cell
  size_eq : cells.size = width * height

namespace Screen

/-- A screen filled with `c`. -/
def new (width height : Nat) (c : Cell := {}) : Screen :=
  ⟨width, height, Array.replicate (width * height) c, Array.size_replicate⟩

instance : Inhabited Screen := ⟨new 0 0⟩

/-- The cell at `(x, y)`, if that position is on the screen. -/
def get? (s : Screen) (x y : Int) : Option Cell :=
  (gridIndex? s.width s.height x y).bind (s.cells[·]?)

/-- Applies `f` to the cell at `(x, y)`; positions off the screen are ignored. -/
def modify (s : Screen) (x y : Int) (f : Cell → Cell) : Screen :=
  match gridIndex? s.width s.height x y with
  | some i => ⟨s.width, s.height, s.cells.modify i f, by simp [s.size_eq]⟩
  | none => s

def set (s : Screen) (x y : Int) (c : Cell) : Screen := s.modify x y fun _ => c

/-- Applies `f` to every cell. -/
def map (s : Screen) (f : Cell → Cell) : Screen :=
  ⟨s.width, s.height, s.cells.map f, by simp [s.size_eq]⟩

def bounds (s : Screen) : Rect := ⟨0, 0, s.width, s.height⟩

/-- Whether `(x, y)` is a position on the screen. -/
def onScreen (s : Screen) (x y : Int) : Prop := 0 ≤ x ∧ x < s.width ∧ 0 ≤ y ∧ y < s.height

/-! ### Lemmas -/

@[simp] theorem width_modify (s : Screen) (x y : Int) (f : Cell → Cell) :
    (s.modify x y f).width = s.width := by
  unfold modify; split <;> rfl

@[simp] theorem height_modify (s : Screen) (x y : Int) (f : Cell → Cell) :
    (s.modify x y f).height = s.height := by
  unfold modify; split <;> rfl

@[simp] theorem width_set (s : Screen) (x y : Int) (c : Cell) : (s.set x y c).width = s.width :=
  width_modify ..
@[simp] theorem height_set (s : Screen) (x y : Int) (c : Cell) : (s.set x y c).height = s.height :=
  height_modify ..
@[simp] theorem width_map (s : Screen) (f : Cell → Cell) : (s.map f).width = s.width := rfl
@[simp] theorem height_map (s : Screen) (f : Cell → Cell) : (s.map f).height = s.height := rfl
@[simp] theorem width_new (w h : Nat) (c : Cell) : (new w h c).width = w := rfl
@[simp] theorem height_new (w h : Nat) (c : Cell) : (new w h c).height = h := rfl

theorem get?_isSome_iff (s : Screen) (x y : Int) : (s.get? x y).isSome ↔ s.onScreen x y := by
  unfold get? onScreen
  constructor
  · intro h
    cases hi : gridIndex? s.width s.height x y with
    | none => simp [hi] at h
    | some i => exact gridIndex?_isSome.1 (by simp [hi])
  · intro h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (gridIndex?_isSome.2 h)
    have : i < s.cells.size := s.size_eq ▸ gridIndex?_lt hi
    simp [hi, this]

theorem get?_eq_none_iff (s : Screen) (x y : Int) : s.get? x y = none ↔ ¬ s.onScreen x y := by
  rw [← get?_isSome_iff]; simp

/-- Reading back a modified cell. -/
theorem get?_modify (s : Screen) (x y x' y' : Int) (f : Cell → Cell) :
    (s.modify x y f).get? x' y' = if x' = x ∧ y' = y then (s.get? x' y').map f else s.get? x' y' := by
  unfold modify
  cases hi : gridIndex? s.width s.height x y with
  | none =>
    simp only
    split
    · next he =>
      obtain ⟨rfl, rfl⟩ := he
      simp [get?, hi]
    · rfl
  | some i =>
    simp only [get?]
    cases hj : gridIndex? s.width s.height x' y' with
    | none =>
      have : ¬ (x' = x ∧ y' = y) := by
        rintro ⟨rfl, rfl⟩
        simp [hi] at hj
      simp [this]
    | some j =>
      simp only [Option.bind_some, Array.getElem?_modify]
      by_cases hij : i = j
      · subst hij
        obtain ⟨rfl, rfl⟩ := gridIndex?_inj hj hi
        simp
      · have : ¬ (x' = x ∧ y' = y) := by
          rintro ⟨rfl, rfl⟩
          exact hij (Option.some.inj (hi.symm.trans hj))
        simp [hij, this]

theorem get?_modify_of_ne (s : Screen) {x y x' y' : Int} (f : Cell → Cell)
    (h : ¬ (x' = x ∧ y' = y)) : (s.modify x y f).get? x' y' = s.get? x' y' := by
  rw [get?_modify]; simp [h]

theorem get?_set (s : Screen) (x y x' y' : Int) (c : Cell) :
    (s.set x y c).get? x' y' =
      if x' = x ∧ y' = y then (s.get? x' y').map (fun _ => c) else s.get? x' y' :=
  get?_modify s x y x' y' _

theorem get?_new (w h : Nat) (c : Cell) (x y : Int) :
    (new w h c).get? x y = if 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < h then some c else none := by
  unfold get? new
  cases hi : gridIndex? w h x y with
  | none =>
    have := gridIndex?_isSome (w := w) (h := h) (x := x) (y := y)
    simp_all
  | some i =>
    have hb := (gridIndex?_isSome (w := w) (h := h) (x := x) (y := y)).1 (by simp [hi])
    simp [Array.getElem?_replicate, gridIndex?_lt hi, hb]

theorem get?_map (s : Screen) (f : Cell → Cell) (x y : Int) :
    (s.map f).get? x y = (s.get? x y).map f := by
  simp only [get?, map]
  cases gridIndex? s.width s.height x y with
  | none => rfl
  | some i => simp [Array.getElem?_map]

/-- Screens with the same dimensions and the same cells are equal. -/
theorem ext {s t : Screen} (hw : s.width = t.width) (hh : s.height = t.height)
    (hc : ∀ x y, s.get? x y = t.get? x y) : s = t := by
  obtain ⟨w, h, cs, hs⟩ := s
  obtain ⟨w', h', ct, ht⟩ := t
  simp only at hw hh
  subst hw hh
  have : cs = ct := by
    apply Array.ext (by omega)
    intro i hi₁ hi₂
    -- The cell with index `i` is at `(i % w, i / w)`.
    have hlt : i < w * h := hs ▸ hi₁
    have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hlt
    have h1 : i % w < w := Nat.mod_lt _ hw
    have h2 : i / w < h := Nat.div_lt_of_lt_mul hlt
    obtain ⟨a, ha⟩ : ∃ a, a = i % w := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = i / w := ⟨_, rfl⟩
    have hidx : gridIndex? w h (a : Int) (b : Int) = some i := by
      unfold gridIndex?
      split
      · simp only [Int.toNat_natCast, ha, hb, Nat.div_add_mod']
      · next hn => exact absurd ⟨by omega, by omega, by omega, by omega⟩ hn
    have := hc (a : Int) (b : Int)
    simp only [get?, hidx, Option.bind_some] at this
    rw [Array.getElem?_eq_getElem hi₁, Array.getElem?_eq_getElem hi₂] at this
    exact Option.some.inj this
  subst this
  rfl

end Screen

/-! ## Confinement -/

/-- `s'` has the dimensions of `s` and agrees with it everywhere outside `r`. -/
structure Screen.Confined (r : Rect) (s s' : Screen) : Prop where
  width_eq : s'.width = s.width
  height_eq : s'.height = s.height
  outside : ∀ x y, ¬ r.contains ⟨x, y⟩ → s'.get? x y = s.get? x y

namespace Screen.Confined

theorem refl (r : Rect) (s : Screen) : Confined r s s := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem trans {r : Rect} {s₁ s₂ s₃ : Screen} (h₁ : Confined r s₁ s₂) (h₂ : Confined r s₂ s₃) :
    Confined r s₁ s₃ :=
  ⟨h₂.width_eq.trans h₁.width_eq, h₂.height_eq.trans h₁.height_eq,
   fun x y hx => (h₂.outside x y hx).trans (h₁.outside x y hx)⟩

/-- Confinement to a smaller rectangle implies confinement to a larger one. -/
theorem mono {r r' : Rect} {s s' : Screen} (h : Confined r s s') (sub : r.Subset r') :
    Confined r' s s' :=
  ⟨h.width_eq, h.height_eq, fun x y hx => h.outside x y fun hr => hx (sub _ hr)⟩

end Screen.Confined

/-- The region a view draws into: where its local origin lies and what it may touch. -/
structure Viewport where
  origin : Point
  clip : Rect
deriving Inhabited, Repr

/--
A drawing action. Besides running, it carries a proof that it never changes the
screen outside the clip rectangle of the viewport it runs in (nor its dimensions).
-/
structure DrawM (α : Type) where
  run : Viewport → Screen → α × Screen
  confined : ∀ vp s, Screen.Confined vp.clip s (run vp s).2

namespace DrawM

instance : Monad DrawM where
  pure a := ⟨fun _ s => (a, s), fun vp s => .refl vp.clip s⟩
  bind m f :=
    ⟨fun vp s => (f (m.run vp s).1).run vp (m.run vp s).2,
     fun vp s => (m.confined vp s).trans ((f (m.run vp s).1).confined vp (m.run vp s).2)⟩

@[simp] theorem run_pure {α : Type} (a : α) (vp : Viewport) (s : Screen) :
    (pure a : DrawM α).run vp s = (a, s) := rfl

@[simp] theorem run_bind {α β : Type} (m : DrawM α) (f : α → DrawM β) (vp : Viewport) (s : Screen) :
    (m >>= f).run vp s = (f (m.run vp s).1).run vp (m.run vp s).2 := rfl

theorem ext {α : Type} {m₁ m₂ : DrawM α} (h : m₁.run = m₂.run) : m₁ = m₂ := by
  cases m₁; cases m₂; cases h; rfl

instance : LawfulMonad DrawM := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)

end DrawM

/-- Line-drawing character sets. -/
structure BoxChars where
  tl : Char
  tr : Char
  bl : Char
  br : Char
  horiz : Char
  vert : Char
deriving Inhabited, Repr

namespace BoxChars
def single : BoxChars := ⟨'┌', '┐', '└', '┘', '─', '│'⟩
def double : BoxChars := ⟨'╔', '╗', '╚', '╝', '═', '║'⟩
end BoxChars

namespace Draw

/-- The current viewport. -/
def viewport : DrawM Viewport := ⟨fun vp s => (vp, s), fun vp s => .refl vp.clip s⟩

/-- Runs a drawing action over the whole screen. -/
def run (s : Screen) (m : DrawM Unit) : Screen := (m.run ⟨Point.origin, s.bounds⟩ s).2

/-- The absolute position of local `(x, y)`. -/
def absolute (vp : Viewport) (x y : Int) : Point := ⟨vp.origin.x + x, vp.origin.y + y⟩

/-- Modifies the cell at local `(x, y)` if it is inside the clip rectangle. This is
the only primitive that changes the screen. -/
def modifyCell (x y : Int) (f : Cell → Cell) : DrawM Unit :=
  ⟨fun vp s =>
    let p := absolute vp x y
    ((), if vp.clip.contains p then s.modify p.x p.y f else s),
   fun vp s => by
    refine ⟨?_, ?_, fun x' y' hout => ?_⟩ <;> dsimp only <;> split
    · simp
    · rfl
    · simp
    · rfl
    · next hin =>
      apply Screen.get?_modify_of_ne
      rintro ⟨rfl, rfl⟩
      exact hout hin
    · rfl⟩

/--
Runs `m` in a viewport derived from the current one by `g`, which must not widen
the clip rectangle.
-/
def withViewport {α : Type} (g : Viewport → Viewport) (hg : ∀ vp, (g vp).clip.Subset vp.clip)
    (m : DrawM α) : DrawM α :=
  ⟨fun vp s => m.run (g vp) s, fun vp s => (m.confined (g vp) s).mono (hg vp)⟩

def putCell (x y : Int) (c : Cell) : DrawM Unit := modifyCell x y fun _ => c

def putChar (x y : Int) (ch : Char) (attr : Attr) : DrawM Unit := putCell x y ⟨ch, attr⟩

/-- Writes characters left to right starting at `(x, y)`. -/
def putChars (x y : Int) (cs : Array Char) (attr : Attr) : DrawM Unit := do
  for h : i in [0:cs.size] do
    putChar (x + i) y cs[i] attr

def putStr (x y : Int) (s : String) (attr : Attr) : DrawM Unit :=
  putChars x y s.toList.toArray attr

/-- Repeats `ch` `n` times horizontally. -/
def hline (x y : Int) (n : Nat) (ch : Char) (attr : Attr) : DrawM Unit := do
  for i in [0:n] do putChar (x + i) y ch attr

/-- Repeats `ch` `n` times vertically. -/
def vline (x y : Int) (n : Nat) (ch : Char) (attr : Attr) : DrawM Unit := do
  for i in [0:n] do putChar x (y + i) ch attr

def fill (r : Rect) (ch : Char) (attr : Attr) : DrawM Unit := do
  for j in [0:r.h] do hline r.x (r.y + j) r.w ch attr

/-- Draws a rectangular frame along the edges of `r`. -/
def box (r : Rect) (bc : BoxChars) (attr : Attr) : DrawM Unit := do
  if r.w < 2 || r.h < 2 then return
  hline (r.x + 1) r.y (r.w - 2) bc.horiz attr
  hline (r.x + 1) (r.bottom - 1) (r.w - 2) bc.horiz attr
  vline r.x (r.y + 1) (r.h - 2) bc.vert attr
  vline (r.right - 1) (r.y + 1) (r.h - 2) bc.vert attr
  putChar r.x r.y bc.tl attr
  putChar (r.right - 1) r.y bc.tr attr
  putChar r.x (r.bottom - 1) bc.bl attr
  putChar (r.right - 1) (r.bottom - 1) bc.br attr

/-- Applies `f` to the attribute of every cell in `r`. -/
def mapAttr (r : Rect) (f : Attr → Attr) : DrawM Unit := do
  for j in [0:r.h] do
    for i in [0:r.w] do
      modifyCell (r.x + i) (r.y + j) fun c => { c with attr := f c.attr }

/-- The attribute a drop shadow gives to a cell attribute `a`. -/
def shadowAttr (attr onBlack a : Attr) : Attr :=
  if a == attr then a else if a.bg == .black then onBlack else attr

/-- The two parts of the drop shadow of `r`: two columns to its right, one row below. -/
def shadowRects (r : Rect) : Rect × Rect :=
  (⟨r.right, r.y + 1, 2, r.h⟩, ⟨r.x + 2, r.bottom, r.w - 2, 1⟩)

/--
Turbo Vision's drop shadow: two columns to the right and one row below `r`.
Cells keep their characters; black backgrounds get `onBlack` instead.
-/
def shadow (r : Rect) (attr onBlack : Attr) : DrawM Unit := do
  mapAttr (shadowRects r).1 (shadowAttr attr onBlack)
  mapAttr (shadowRects r).2 (shadowAttr attr onBlack)

/-- The viewport of a sub-view at `r` (local coordinates). -/
def subViewport (r : Rect) (vp : Viewport) : Viewport :=
  let abs := r.translate vp.origin
  { origin := abs.origin, clip := vp.clip.intersect abs }

/-- Runs `m` with the local origin moved to `r.origin` and clipping narrowed to `r`. -/
def within {α : Type} (r : Rect) (m : DrawM α) : DrawM α :=
  withViewport (subViewport r) (fun vp => Rect.intersect_subset_left vp.clip _) m

/-- Runs `m` with clipping narrowed to `r` (local coordinates), keeping the origin. -/
def clip {α : Type} (r : Rect) (m : DrawM α) : DrawM α :=
  withViewport (fun vp => { vp with clip := vp.clip.intersect (r.translate vp.origin) })
    (fun vp => Rect.intersect_subset_left vp.clip _) m

end Draw

end HyperVision
