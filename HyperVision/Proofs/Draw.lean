import HyperVision.Screen

/-!
# Drawing: correctness theorems

Every `DrawM` action is confined to its viewport's clip rectangle by construction
(`DrawM.confined`). This file adds

* a small reasoning framework (`DrawM.Sat`) for proving that an action relates
  the screen before and after by a preorder, closed under `pure`, bind and loops;
* nesting: a sub-view drawn with `Draw.within r` only touches `r`;
* drop shadows keep every character and never touch the shadowed rectangle;
* an exact specification of `Draw.hline` and `Draw.fill`: they paint every visible
  cell of their area with the given cell, and nothing else.
-/

namespace HyperVision

namespace DrawM

variable {α β σ : Type}

/-- `m` relates the screen before to the screen after by `R`, in every viewport. -/
def Sat (R : Viewport → Screen → Screen → Prop) (m : DrawM α) : Prop :=
  ∀ vp s, R vp s (m.run vp s).2

/-- `R` is reflexive and transitive (in every viewport). -/
structure IsPreorder (R : Viewport → Screen → Screen → Prop) : Prop where
  refl : ∀ vp s, R vp s s
  trans : ∀ vp s₁ s₂ s₃, R vp s₁ s₂ → R vp s₂ s₃ → R vp s₁ s₃

variable {R : Viewport → Screen → Screen → Prop}

theorem Sat.pure (hR : IsPreorder R) (a : α) : Sat R (Pure.pure a : DrawM α) :=
  fun vp s => hR.refl vp s

theorem Sat.bind (hR : IsPreorder R) {m : DrawM α} {f : α → DrawM β} (hm : Sat R m)
    (hf : ∀ a, Sat R (f a)) : Sat R (m >>= f) :=
  fun vp s => hR.trans vp _ _ _ (hm vp s) (hf _ vp _)

theorem Sat.mono {R' : Viewport → Screen → Screen → Prop} {m : DrawM α} (h : Sat R m)
    (hR : ∀ vp s s', R vp s s' → R' vp s s') : Sat R' m :=
  fun vp s => hR vp s _ (h vp s)

theorem Sat.forIn_list (hR : IsPreorder R) (l : List β) (init : σ)
    {body : β → σ → DrawM (ForInStep σ)} (h : ∀ b ∈ l, ∀ x, Sat R (body b x)) :
    Sat R (forIn l init body) := by
  induction l generalizing init with
  | nil => exact Sat.pure hR init
  | cons a as ih =>
    rw [List.forIn_cons]
    refine Sat.bind hR (h a (List.mem_cons_self ..) init) fun step => ?_
    cases step with
    | done b => exact Sat.pure hR b
    | yield b => exact ih b fun b' hb' x => h b' (List.mem_cons_of_mem _ hb') x

theorem Sat.forIn_range (hR : IsPreorder R) (n : Nat) (init : σ)
    {body : Nat → σ → DrawM (ForInStep σ)} (h : ∀ i < n, ∀ x, Sat R (body i x)) :
    Sat R (forIn [:n] init body) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine Sat.forIn_list hR _ init fun b hb x => h b ?_ x
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hb
  simp [Std.Legacy.Range.size] at hi ⊢
  omega

end DrawM

open DrawM

/-! ## Relations -/

/-- The screen keeps its dimensions and every character. -/
def SameChars (_ : Viewport) (s s' : Screen) : Prop :=
  s'.width = s.width ∧ s'.height = s.height ∧
    ∀ x y, (s'.get? x y).map (·.ch) = (s.get? x y).map (·.ch)

theorem SameChars.isPreorder : IsPreorder SameChars where
  refl _ _ := ⟨rfl, rfl, fun _ _ => rfl⟩
  trans _ _ _ _ h₁ h₂ :=
    ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun x y => (h₂.2.2 x y).trans (h₁.2.2 x y)⟩

/-- Only cells satisfying `P` (which may depend on the viewport) change. -/
def ChangesOnly (P : Viewport → Point → Prop) (vp : Viewport) (s s' : Screen) : Prop :=
  s'.width = s.width ∧ s'.height = s.height ∧ ∀ x y, ¬ P vp ⟨x, y⟩ → s'.get? x y = s.get? x y

theorem ChangesOnly.isPreorder (P : Viewport → Point → Prop) : IsPreorder (ChangesOnly P) where
  refl _ _ := ⟨rfl, rfl, fun _ _ _ => rfl⟩
  trans _ _ _ _ h₁ h₂ :=
    ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun x y hp => (h₂.2.2 x y hp).trans (h₁.2.2 x y hp)⟩

theorem ChangesOnly.mono {P Q : Viewport → Point → Prop} (h : ∀ vp p, P vp p → Q vp p)
    {vp : Viewport} {s s' : Screen} (hc : ChangesOnly P vp s s') : ChangesOnly Q vp s s' :=
  ⟨hc.1, hc.2.1, fun x y hq => hc.2.2 x y fun hp => hq (h vp _ hp)⟩

namespace Draw

/-! ## Primitive facts -/

theorem modifyCell_sameChars {x y : Int} {f : Cell → Cell} (hf : ∀ c, (f c).ch = c.ch) :
    Sat SameChars (modifyCell x y f) := by
  intro vp s
  refine ⟨(modifyCell x y f).confined vp s |>.width_eq, (modifyCell x y f).confined vp s |>.height_eq,
    fun x' y' => ?_⟩
  simp only [modifyCell]
  split
  · rw [Screen.get?_modify]
    split <;> simp [Option.map_map, Function.comp_def, hf]
  · rfl

theorem modifyCell_changesOnly {P : Viewport → Point → Prop} {x y : Int} {f : Cell → Cell}
    (hP : ∀ vp, P vp (absolute vp x y)) : Sat (ChangesOnly P) (modifyCell x y f) := by
  intro vp s
  refine ⟨(modifyCell x y f).confined vp s |>.width_eq, (modifyCell x y f).confined vp s |>.height_eq,
    fun x' y' hn => ?_⟩
  simp only [modifyCell]
  split
  · apply Screen.get?_modify_of_ne
    rintro ⟨rfl, rfl⟩
    exact hn (hP vp)
  · rfl

/-! ## Nesting -/

/-- A sub-view drawn with `within r` only touches the visible part of `r`. -/
theorem within_confined {α : Type} (r : Rect) (m : DrawM α) (vp : Viewport) (s : Screen) :
    Screen.Confined (vp.clip.intersect (r.translate vp.origin)) s ((within r m).run vp s).2 :=
  m.confined (subViewport r vp) s

/-- Nested sub-views (e.g. a control inside a window's interior) stay inside both. -/
theorem within_within_confined {α : Type} (r₁ r₂ : Rect) (m : DrawM α) (vp : Viewport)
    (s : Screen) :
    let outer := r₁.translate vp.origin
    Screen.Confined ((vp.clip.intersect outer).intersect (r₂.translate outer.origin)) s
      ((within r₁ (within r₂ m)).run vp s).2 :=
  m.confined (subViewport r₂ (subViewport r₁ vp)) s

/-- `Draw.run` keeps the screen's dimensions. -/
theorem run_width (s : Screen) (m : DrawM Unit) : (run s m).width = s.width :=
  (m.confined _ s).width_eq

theorem run_height (s : Screen) (m : DrawM Unit) : (run s m).height = s.height :=
  (m.confined _ s).height_eq

/-! ## Shadows -/

/-- A drop shadow never changes a character: it only darkens attributes. -/
theorem mapAttr_sameChars (r : Rect) (f : Attr → Attr) : Sat SameChars (mapAttr r f) := by
  unfold mapAttr
  refine Sat.bind SameChars.isPreorder ?_ fun _ => Sat.pure SameChars.isPreorder _
  refine Sat.forIn_range SameChars.isPreorder _ _ fun j _ _ => ?_
  refine Sat.bind SameChars.isPreorder ?_ fun _ => Sat.pure SameChars.isPreorder _
  refine Sat.forIn_range SameChars.isPreorder _ _ fun i _ _ => ?_
  exact Sat.bind SameChars.isPreorder (modifyCell_sameChars fun _ => rfl)
    fun _ => Sat.pure SameChars.isPreorder _

theorem shadow_sameChars (r : Rect) (attr onBlack : Attr) :
    Sat SameChars (shadow r attr onBlack) :=
  Sat.bind SameChars.isPreorder (mapAttr_sameChars _ _) fun _ => mapAttr_sameChars _ _

/-- `mapAttr r f` only changes cells inside `r`. -/
theorem mapAttr_changesOnly (r : Rect) (f : Attr → Attr) :
    Sat (ChangesOnly fun vp p => (r.translate vp.origin).contains p) (mapAttr r f) := by
  have hR := ChangesOnly.isPreorder fun vp p => (r.translate vp.origin).contains p
  unfold mapAttr
  refine Sat.bind hR ?_ fun _ => Sat.pure hR _
  refine Sat.forIn_range hR _ _ fun j hj _ => ?_
  refine Sat.bind hR ?_ fun _ => Sat.pure hR _
  refine Sat.forIn_range hR _ _ fun i hi _ => ?_
  refine Sat.bind hR (modifyCell_changesOnly fun vp => ?_) fun _ => Sat.pure hR _
  simp only [Rect.contains_iff, Rect.translate, absolute]
  omega

/-- The points a drop shadow of `r` may affect, in absolute coordinates. -/
def shadowArea (r : Rect) (vp : Viewport) (p : Point) : Prop :=
  ((shadowRects r).1.translate vp.origin).contains p ∨
    ((shadowRects r).2.translate vp.origin).contains p

theorem shadow_changesOnly (r : Rect) (attr onBlack : Attr) :
    Sat (ChangesOnly (shadowArea r)) (shadow r attr onBlack) := by
  have hR := ChangesOnly.isPreorder (shadowArea r)
  refine Sat.bind hR ?_ fun _ => ?_
  · exact (mapAttr_changesOnly _ _).mono fun _ _ _ h => h.mono fun _ _ hp => Or.inl hp
  · exact (mapAttr_changesOnly _ _).mono fun _ _ _ h => h.mono fun _ _ hp => Or.inr hp

/-- The shadow area never overlaps the rectangle casting the shadow. -/
theorem shadowArea_disjoint (r : Rect) (vp : Viewport) (p : Point)
    (hp : (r.translate vp.origin).contains p) : ¬ shadowArea r vp p := by
  simp only [shadowArea, shadowRects, Rect.contains_iff, Rect.translate, Rect.right,
    Rect.bottom] at hp ⊢
  omega

/-- A window's drop shadow never changes the window itself. -/
theorem shadow_keeps_rect (r : Rect) (attr onBlack : Attr) (vp : Viewport) (s : Screen)
    (p : Point) (hp : (r.translate vp.origin).contains p) :
    ((shadow r attr onBlack).run vp s).2.get? p.x p.y = s.get? p.x p.y :=
  (shadow_changesOnly r attr onBlack vp s).2.2 p.x p.y (shadowArea_disjoint r vp ⟨p.x, p.y⟩ hp)

/-! ## Painting -/

/--
`m` paints exactly the visible cells of the area `A` (which may depend on the
viewport) with `c`: those cells become `c` (where they are on the screen), and
every other cell keeps its content.
-/
def Paints (A : Viewport → Point → Prop) (c : Cell) (m : DrawM Unit) : Prop :=
  ∀ vp s x y,
    (A vp ⟨x, y⟩ ∧ vp.clip.contains ⟨x, y⟩ →
      (m.run vp s).2.get? x y = (s.get? x y).map fun _ => c) ∧
    (¬ (A vp ⟨x, y⟩ ∧ vp.clip.contains ⟨x, y⟩) → (m.run vp s).2.get? x y = s.get? x y)

theorem Paints.pure {c : Cell} : Paints (fun _ _ => False) c (Pure.pure ()) :=
  fun _ _ _ _ => ⟨fun h => h.1.elim, fun _ => rfl⟩

theorem Paints.congr {A B : Viewport → Point → Prop} {c : Cell} {m : DrawM Unit}
    (h : Paints A c m) (hAB : ∀ vp p, A vp p ↔ B vp p) : Paints B c m := by
  intro vp s x y
  simpa only [hAB] using h vp s x y

/-- Painting `A` then `B` with the same cell paints `A ∪ B`. -/
theorem Paints.bind {A B : Viewport → Point → Prop} {c : Cell} {m n : DrawM Unit}
    (hm : Paints A c m) (hn : Paints B c n) :
    Paints (fun vp p => A vp p ∨ B vp p) c (m >>= fun _ => n) := by
  intro vp s x y
  simp only [DrawM.run_bind]
  have hmx := hm vp s x y
  have hnx := hn vp (m.run vp s).2 x y
  by_cases hc : vp.clip.contains ⟨x, y⟩ <;> by_cases hA : A vp ⟨x, y⟩ <;>
    by_cases hB : B vp ⟨x, y⟩ <;> simp_all <;> cases s.get? x y <;> rfl

theorem putCell_paints (x y : Int) (c : Cell) :
    Paints (fun vp p => p = absolute vp x y) c (putCell x y c) := by
  intro vp s x' y'
  simp only [putCell, modifyCell]
  generalize absolute vp x y = a
  obtain ⟨ax, ay⟩ := a
  simp only [Point.mk.injEq]
  by_cases hc : vp.clip.contains ⟨ax, ay⟩ <;> by_cases hx : x' = ax <;> by_cases hy : y' = ay <;>
    simp_all [Screen.get?_modify]

/-- The loop body that runs `body i` and continues. -/
abbrev loopBody (body : Nat → DrawM Unit) (i : Nat) (_ : PUnit) : DrawM (ForInStep PUnit) :=
  body i >>= fun _ => Pure.pure (ForInStep.yield PUnit.unit)

/-- A loop painting `A i` in iteration `i` paints the union over `i < n`. -/
theorem Paints.forIn_range {A : Nat → Viewport → Point → Prop} {c : Cell} (n : Nat)
    {body : Nat → DrawM Unit} (h : ∀ i, Paints (A i) c (body i)) :
    Paints (fun vp p => ∃ i < n, A i vp p) c
      (forIn [:n] PUnit.unit (loopBody body) >>= fun _ => Pure.pure ()) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  -- Generalize the start of the range.
  suffices ∀ k m, Paints (fun vp p => ∃ i, k ≤ i ∧ i < k + m ∧ A i vp p) c
      (forIn (List.range' k m 1) PUnit.unit (loopBody body) >>= fun _ => Pure.pure ()) by
    refine (this 0 n).congr fun vp p => ?_
    constructor
    · rintro ⟨i, -, hi, ha⟩; exact ⟨i, by omega, ha⟩
    · rintro ⟨i, hi, ha⟩; exact ⟨i, by omega, by omega, ha⟩
  intro k m
  induction m generalizing k with
  | zero =>
    refine (Paints.pure).congr fun vp p => ?_
    constructor
    · intro h; exact h.elim
    · rintro ⟨i, h₁, h₂, -⟩; omega
  | succ m ih =>
    have step := Paints.bind (h k) (ih (k + 1))
    have heq : (forIn (List.range' k (m + 1) 1) PUnit.unit (loopBody body) >>= fun _ => Pure.pure ()) =
        (body k >>= fun _ =>
          forIn (List.range' (k + 1) m 1) PUnit.unit (loopBody body) >>= fun _ => Pure.pure ()) := by
      rw [List.range'_succ, List.forIn_cons]
      exact DrawM.ext rfl
    rw [heq]
    refine step.congr fun vp p => ?_
    constructor
    · rintro (ha | ⟨i, h₁, h₂, ha⟩)
      · exact ⟨k, Nat.le_refl _, by omega, ha⟩
      · exact ⟨i, by omega, by omega, ha⟩
    · rintro ⟨i, h₁, h₂, ha⟩
      by_cases hik : i = k
      · subst hik; exact Or.inl ha
      · exact Or.inr ⟨i, by omega, by omega, ha⟩

/-- A painter changes only its area. -/
theorem Paints.changesOnly {A : Viewport → Point → Prop} {c : Cell} {m : DrawM Unit}
    (h : Paints A c m) : Sat (ChangesOnly A) m := fun vp s =>
  ⟨(m.confined vp s).width_eq, (m.confined vp s).height_eq,
   fun x y hn => (h vp s x y).2 fun hA => hn hA.1⟩

/-- `clip r m` changes only cells inside `r`, whatever `m` does. -/
theorem clip_changesOnly {α : Type} (r : Rect) (m : DrawM α) :
    Sat (ChangesOnly fun vp p => (r.translate vp.origin).contains p) (clip r m) := fun vp s =>
  let h := m.confined { vp with clip := vp.clip.intersect (r.translate vp.origin) } s
  ⟨h.width_eq, h.height_eq, fun x y hn => h.outside x y fun hc => hn (Rect.contains_intersect.1 hc).2⟩

/-- `hline x y n ch attr` paints the visible cells `(x + i, y)`, `i < n`, and nothing else. -/
theorem hline_paints (x y : Int) (n : Nat) (ch : Char) (attr : Attr) :
    Paints (fun vp p => ∃ i < n, p = absolute vp (x + i) y) ⟨ch, attr⟩ (hline x y n ch attr) :=
  Paints.forIn_range (A := fun i vp p => p = absolute vp (x + i) y) n
    (body := fun i => putChar (x + i) y ch attr) fun _ => putCell_paints _ _ _

/-- `fill r ch attr` paints exactly the visible part of `r` with `⟨ch, attr⟩`. -/
theorem fill_paints (r : Rect) (ch : Char) (attr : Attr) :
    Paints (fun vp p => (r.translate vp.origin).contains p) ⟨ch, attr⟩ (fill r ch attr) := by
  have h := Paints.forIn_range (A := fun j vp p => ∃ i < r.w, p = absolute vp (r.x + i) (r.y + j))
    (c := ⟨ch, attr⟩) r.h (body := fun j => hline r.x (r.y + j) r.w ch attr)
    fun j => hline_paints _ _ _ _ _
  refine h.congr fun vp p => ?_
  obtain ⟨px, py⟩ := p
  simp only [Rect.contains_iff, Rect.translate, absolute, Point.mk.injEq]
  constructor
  · rintro ⟨j, hj, i, hi, h₁, h₂⟩
    omega
  · intro h
    exact ⟨(py - vp.origin.y - r.y).toNat, by omega, (px - vp.origin.x - r.x).toNat, by omega,
      by omega, by omega⟩

end Draw

end HyperVision
