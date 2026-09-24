import HyperVision.Terminal

/-!
# Renderer correctness

A model of a terminal (`Term`: its cells, cursor and current attribute) and the
theorem that the differential renderer is correct: running `diffOps prev next`
on a terminal that shows `prev` leaves it showing exactly `next`. A full repaint
(first frame, or a resize) works from any terminal contents.

The model treats every screen cell as one terminal cell; after a wide or
zero-width character it lets the cursor move by `charAdvance`, which the diff
never relies on.
-/

namespace HyperVision.Terminal

/-- A model of the terminal. -/
structure Term where
  grid : Screen
  cursor : Nat × Nat
  attr : Attr

namespace Term

def apply (t : Term) : Op → Term
  | .reset => { t with grid := Screen.new t.grid.width t.grid.height, attr := default }
  | .moveTo x y => { t with cursor := (x, y) }
  | .setAttr a => { t with attr := a }
  | .put c =>
    { t with grid := t.grid.set t.cursor.1 t.cursor.2 ⟨c, t.attr⟩
             cursor := (t.cursor.1 + charAdvance c, t.cursor.2) }

/-- Runs a sequence of operations. -/
def run (t : Term) (ops : List Op) : Term := ops.foldl apply t

@[simp] theorem run_nil (t : Term) : t.run [] = t := rfl

@[simp] theorem run_cons (t : Term) (o : Op) (ops : List Op) :
    t.run (o :: ops) = (t.apply o).run ops := rfl

theorem run_append (t : Term) (l₁ l₂ : List Op) : t.run (l₁ ++ l₂) = (t.run l₁).run l₂ :=
  List.foldl_append ..

end Term

/-! ## The operations emitted for one cell -/

/-- The operations `diffCell` appends for position `q`. -/
def cellOps (prev : Option Screen) (next : Screen) (full : Bool) (st : DiffState)
    (q : Nat × Nat) : List Op :=
  match next.get? q.1 q.2 with
  | none => []
  | some c =>
    if unchanged prev full q.1 q.2 c then []
    else (if st.pos != some q then [.moveTo q.1 q.2] else []) ++
      (if st.attr != some c.attr then [.setAttr c.attr] else []) ++ [.put (printable c.ch)]

theorem diffCell_ops (prev : Option Screen) (next : Screen) (full : Bool) (st : DiffState)
    (q : Nat × Nat) :
    (diffCell prev next full st q).ops.toList = st.ops.toList ++ cellOps prev next full st q := by
  unfold diffCell cellOps
  cases hc : next.get? q.1 q.2 with
  | none => simp
  | some c =>
    simp only
    by_cases hu : unchanged prev full q.1 q.2 c
    · simp [hu]
    · by_cases hp : st.pos = some q <;> by_cases ha : st.attr = some c.attr <;> simp [hu, hp, ha]

/-! ## The invariant -/

/--
What holds after the diff has handled the positions in `D`: those show the new
cells; in an incremental update every other position still shows the old cell; and
the diff's knowledge of cursor and attribute is accurate.
-/
structure Inv (prev : Option Screen) (next : Screen) (full : Bool) (D : Nat → Nat → Prop)
    (st : DiffState) (t : Term) : Prop where
  width : t.grid.width = next.width
  height : t.grid.height = next.height
  done : ∀ x y : Nat, D x y → t.grid.get? x y = (next.get? x y).map Cell.shown
  rest : full = false → ∀ x y : Nat, ¬ D x y →
    t.grid.get? x y = (prev.bind (·.get? x y)).map Cell.shown
  pos : ∀ p, st.pos = some p → t.cursor = p
  attr : ∀ a, st.attr = some a → t.attr = a

/-- Screens of equal dimensions agree on which positions are on screen. -/
private theorem get?_none_of_dims {s s' : Screen} (hw : s.width = s'.width)
    (hh : s.height = s'.height) {x y : Int} (h : s'.get? x y = none) : s.get? x y = none := by
  rw [Screen.get?_eq_none_iff] at h ⊢
  simpa [Screen.onScreen, hw, hh] using h

private theorem isSome_of_dims {s s' : Screen} (hw : s.width = s'.width)
    (hh : s.height = s'.height) {x y : Int} (h : (s'.get? x y).isSome) : (s.get? x y).isSome := by
  rw [Screen.get?_isSome_iff] at h ⊢
  simpa [Screen.onScreen, hw, hh] using h

/-- Handling one position preserves the invariant, with that position now done. -/
theorem Inv.step {prev : Option Screen} {next : Screen} {full : Bool} {D : Nat → Nat → Prop}
    {st : DiffState} {t : Term} (h : Inv prev next full D st t) (q : Nat × Nat) :
    Inv prev next full (fun x y => D x y ∨ (x, y) = q) (diffCell prev next full st q)
      (t.run (cellOps prev next full st q)) := by
  obtain ⟨qx, qy⟩ := q
  unfold diffCell cellOps
  cases hc : next.get? qx qy with
  | none =>
    simp only [Term.run_nil]
    refine ⟨h.width, h.height, fun x y hd => ?_, fun hf x y hd => h.rest hf x y fun h' => hd (.inl h'),
      h.pos, h.attr⟩
    rcases hd with hd | hq
    · exact h.done x y hd
    · simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [hc, Option.map_none]
      exact get?_none_of_dims h.width h.height hc
  | some c =>
    simp only
    by_cases hu : unchanged prev full qx qy c
    · simp only [hu, ite_true, Term.run_nil]
      refine ⟨h.width, h.height, fun x y hd => ?_, fun hf x y hd => h.rest hf x y fun h' => hd (.inl h'),
        h.pos, h.attr⟩
      rcases hd with hd | hq
      · exact h.done x y hd
      · simp only [Prod.mk.injEq] at hq
        obtain ⟨rfl, rfl⟩ := hq
        by_cases hD : D x y
        · exact h.done x y hD
        · simp only [unchanged, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
          rw [h.rest hu.1 x y hD, hu.2, hc]
    · simp only [hu, ite_false, Bool.false_eq_true]
      -- The cursor is at `q` and the attribute is `c.attr` right before the `put`.
      have hon : (t.grid.get? qx qy).isSome := isSome_of_dims h.width h.height (by simp [hc])
      rw [Term.run_append, Term.run_append]
      generalize ht₁ : t.run (if st.pos != some (qx, qy) then [.moveTo qx qy] else []) = t₁
      have h₁ : t₁.grid = t.grid ∧ t₁.attr = t.attr ∧ t₁.cursor = (qx, qy) := by
        subst ht₁
        by_cases hp : st.pos = some (qx, qy)
        · simp [hp, h.pos _ hp]
        · simp [hp, Term.apply]
      generalize ht₂ : t₁.run (if st.attr != some c.attr then [.setAttr c.attr] else []) = t₂
      have h₂ : t₂.grid = t.grid ∧ t₂.attr = c.attr ∧ t₂.cursor = (qx, qy) := by
        subst ht₂
        by_cases ha : st.attr = some c.attr
        · simp [ha, h₁, h.attr _ ha]
        · simp [ha, Term.apply, h₁]
      simp only [Term.run_cons, Term.run_nil, Term.apply, h₂]
      refine ⟨by simp [h.width], by simp [h.height], fun x y hd => ?_, fun hf x y hd => ?_, ?_, ?_⟩
      · rw [Screen.get?_set]
        by_cases hq : (x : Int) = qx ∧ (y : Int) = qy
        · obtain ⟨hx, hy⟩ := hq
          have hx' : x = qx := by exact_mod_cast hx
          have hy' : y = qy := by exact_mod_cast hy
          subst hx' hy'
          obtain ⟨cell, hcell⟩ := Option.isSome_iff_exists.1 hon
          simp [hcell, hc, Cell.shown]
        · simp only [hq, ite_false]
          rcases hd with hd | hq'
          · exact h.done x y hd
          · simp only [Prod.mk.injEq] at hq'
            exact absurd ⟨by rw [hq'.1], by rw [hq'.2]⟩ hq
      · have hne : ¬ ((x : Int) = qx ∧ (y : Int) = qy) := by
          rintro ⟨hx, hy⟩
          exact hd (.inr (by simp only [Prod.mk.injEq]; exact ⟨by exact_mod_cast hx, by exact_mod_cast hy⟩))
        rw [Screen.get?_set]
        simp only [hne, ite_false]
        exact h.rest hf x y fun h' => hd (.inl h')
      · intro p hp
        by_cases hadv : charAdvance (printable c.ch) = 1
        · simp only [hadv, beq_self_eq_true, ite_true, Option.some.injEq] at hp
          subst hp
          simp [hadv]
        · simp [hadv] at hp
      · intro a ha
        cases ha
        rfl

/-- Handling a list of positions marks all of them done. -/
theorem Inv.fold {prev : Option Screen} {next : Screen} {full : Bool} (t₀ : Term)
    (L : List (Nat × Nat)) :
    ∀ (D : Nat → Nat → Prop) (st : DiffState), Inv prev next full D st (t₀.run st.ops.toList) →
      Inv prev next full (fun x y => D x y ∨ (x, y) ∈ L) (L.foldl (diffCell prev next full) st)
        (t₀.run (L.foldl (diffCell prev next full) st).ops.toList) := by
  induction L with
  | nil =>
    intro D st h
    simpa using h
  | cons q L ih =>
    intro D st h
    have h' := h.step q
    rw [← Term.run_append, ← diffCell_ops] at h'
    have := ih _ _ h'
    simp only [List.foldl_cons]
    refine ⟨this.width, this.height, fun x y hd => this.done x y ?_,
      fun hf x y hd => this.rest hf x y ?_, this.pos, this.attr⟩
    · rcases hd with hd | hd
      · exact .inl (.inl hd)
      · rcases List.mem_cons.1 hd with hq | hL
        · exact .inl (.inr hq)
        · exact .inr hL
    · rintro ((hD | hq) | hL)
      · exact hd (.inl hD)
      · exact hd (.inr (List.mem_cons.2 (.inl hq)))
      · exact hd (.inr (List.mem_cons_of_mem _ hL))

theorem mem_positions {w h x y : Nat} : (x, y) ∈ positions w h ↔ x < w ∧ y < h := by
  simp only [positions, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨b, hb, a, ha, rfl, rfl⟩; exact ⟨ha, hb⟩
  · rintro ⟨hx, hy⟩; exact ⟨y, hy, x, hx, rfl, rfl⟩

/--
**The renderer is correct.** If the terminal has the size of `next` and — unless a
full repaint is needed — shows `prev`, then after the operations of
`diffOps prev next` it shows exactly `next` (control characters as blanks).
-/
theorem diffOps_correct (prev : Option Screen) (next : Screen) (t : Term)
    (hw : t.grid.width = next.width) (hh : t.grid.height = next.height)
    (hprev : needsFull prev next = false → ∀ p, prev = some p → t.grid = p.map Cell.shown) :
    (t.run (diffOps prev next).toList).grid = next.map Cell.shown := by
  unfold diffOps
  generalize hfull : needsFull prev next = full
  let st₀ : DiffState := { ops := if full then #[.reset] else #[], pos := none, attr := none }
  have h₀ : Inv prev next full (fun _ _ => False) st₀ (t.run st₀.ops.toList) := by
    cases full with
    | true =>
      exact { width := by simp [st₀, Term.apply, hw], height := by simp [st₀, Term.apply, hh]
              done := fun _ _ h => h.elim, rest := fun h => by cases h
              pos := fun _ h => by simp [st₀] at h, attr := fun _ h => by simp [st₀] at h }
    | false =>
      have hrest : ∀ x y : Nat, t.grid.get? x y = (prev.bind (·.get? x y)).map Cell.shown := by
        intro x y
        cases hp : prev with
        | none => simp [hp, needsFull] at hfull
        | some p => simp [hprev hfull p hp, Screen.get?_map]
      exact { width := by simp [st₀, hw], height := by simp [st₀, hh]
              done := fun _ _ h => h.elim, rest := fun _ x y _ => by simpa [st₀] using hrest x y
              pos := fun _ h => by simp [st₀] at h, attr := fun _ h => by simp [st₀] at h }
  have hfin := Inv.fold t (positions next.width next.height) _ st₀ h₀
  refine Screen.ext (t := next.map Cell.shown) hfin.width hfin.height ?_
  intro x y
  rw [Screen.get?_map]
  by_cases hon : next.onScreen x y
  · obtain ⟨hx0, hxw, hy0, hyh⟩ := hon
    obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le hx0
    obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le hy0
    exact hfin.done x y (.inr (mem_positions.2 ⟨by exact_mod_cast hxw, by exact_mod_cast hyh⟩))
  · have hn := (Screen.get?_eq_none_iff next x y).2 hon
    rw [hn, Option.map_none]
    exact get?_none_of_dims hfin.width hfin.height hn

end HyperVision.Terminal
