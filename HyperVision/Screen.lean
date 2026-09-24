import HyperVision.Geometry
import HyperVision.Color

/-!
# Screen buffer and drawing

`Screen` is a flat cell buffer whose size invariant is carried as a proof, so cell
access never needs a bounds check at runtime. Views draw through `DrawM`, which
translates local coordinates and clips against the current viewport.
-/

namespace HyperVision

/-- One character cell. -/
structure Cell where
  ch : Char := ' '
  attr : Attr := ⟨.lightGray, .black⟩
deriving BEq, Inhabited, Repr

/-- A `width × height` grid of cells, stored row-major. -/
structure Screen where
  width : Nat
  height : Nat
  cells : Array Cell
  size_eq : cells.size = width * height

namespace Screen

theorem index_lt {x y w h : Nat} (hx : x < w) (hy : y < h) : y * w + x < w * h := by
  have : (y + 1) * w ≤ h * w := Nat.mul_le_mul_right _ hy
  rw [Nat.succ_mul] at this
  rw [Nat.mul_comm w h]
  omega

/-- A screen filled with `c`. -/
def new (width height : Nat) (c : Cell := {}) : Screen :=
  ⟨width, height, Array.replicate (width * height) c, Array.size_replicate⟩

instance : Inhabited Screen := ⟨new 0 0⟩

/-- The cell at a valid position. -/
def get (s : Screen) (x : Fin s.width) (y : Fin s.height) : Cell :=
  s.cells[y.val * s.width + x.val]'(s.size_eq ▸ index_lt x.isLt y.isLt)

/-- The cell at an arbitrary position, if it is on screen. -/
def get? (s : Screen) (x y : Int) : Option Cell :=
  match x, y with
  | .ofNat cx, .ofNat cy =>
    if hx : cx < s.width then
      if hy : cy < s.height then some (s.get ⟨cx, hx⟩ ⟨cy, hy⟩) else none
    else none
  | _, _ => none

/-- Applies `f` to the cell at `(x, y)`; positions off screen are ignored. -/
def modify (s : Screen) (x y : Int) (f : Cell → Cell) : Screen :=
  match s, x, y with
  | ⟨w, h, cells, hs⟩, .ofNat cx, .ofNat cy =>
    if hx : cx < w then
      if hy : cy < h then
        have hi : cy * w + cx < cells.size := hs ▸ index_lt hx hy
        ⟨w, h, cells.set (cy * w + cx) (f cells[cy * w + cx]) hi, by simp [hs]⟩
      else ⟨w, h, cells, hs⟩
    else ⟨w, h, cells, hs⟩
  | s, _, _ => s

def set (s : Screen) (x y : Int) (c : Cell) : Screen := s.modify x y fun _ => c

def bounds (s : Screen) : Rect := ⟨0, 0, s.width, s.height⟩

end Screen

/-- The region a view draws into: where its local origin lies and what it may touch. -/
structure Viewport where
  origin : Point
  clip : Rect
deriving Inhabited, Repr

/-- The drawing monad. -/
abbrev DrawM := ReaderT Viewport (StateM Screen)

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

/-- Runs a drawing action over the whole screen. -/
def run (s : Screen) (m : DrawM Unit) : Screen :=
  (m.run ⟨Point.origin, s.bounds⟩).run s |>.2

/-- Modifies the cell at local `(x, y)` if it is inside the clip rectangle. -/
def modifyCell (x y : Int) (f : Cell → Cell) : DrawM Unit := do
  let vp ← read
  let p : Point := ⟨vp.origin.x + x, vp.origin.y + y⟩
  if vp.clip.contains p then
    modify fun s => s.modify p.x p.y f

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

/--
Turbo Vision's drop shadow: two columns to the right and one row below `r`.
Cells keep their characters; black backgrounds get `onBlack` instead.
-/
def shadow (r : Rect) (attr onBlack : Attr) : DrawM Unit := do
  let f (a : Attr) : Attr := if a == attr then a else if a.bg == .black then onBlack else attr
  mapAttr ⟨r.right, r.y + 1, 2, r.h⟩ f
  mapAttr ⟨r.x + 2, r.bottom, r.w - 2, 1⟩ f

/-- Runs `m` with the local origin moved to `r.origin` and clipping narrowed to `r`. -/
def within {α : Type} (r : Rect) (m : DrawM α) : DrawM α :=
  withReader (fun vp =>
    let abs := r.translate vp.origin
    { origin := abs.origin, clip := vp.clip.intersect abs }) m

/-- Runs `m` with clipping narrowed to `r` (local coordinates), keeping the origin. -/
def clip {α : Type} (r : Rect) (m : DrawM α) : DrawM α :=
  withReader (fun vp => { vp with clip := vp.clip.intersect (r.translate vp.origin) }) m

end Draw

end HyperVision
