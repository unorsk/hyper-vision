import HyperVision.Window

/-!
# Windows: focus and hit-testing theorems

* **Focus validity.** The keyboard focus of a window only ever rests on a control
  that can take it — never on a label, static text or a disabled button — and this
  is preserved by every key press and mouse event a window handles.
* Tab (`focusNext`) moves the focus to a focusable control whenever one exists.
* Frame hit-testing agrees with the frame's drawing: the close icon, zoom icon,
  resize corner and title bar react where they are drawn.
-/

namespace HyperVision

namespace ControlKind

variable {α : Type}

@[simp] theorem focusable_onFocus (k : ControlKind α) : k.onFocus.focusable = k.focusable := by
  cases k <;> rfl

@[simp] theorem focusable_cancelMouse (k : ControlKind α) :
    k.cancelMouse.focusable = k.focusable := by
  cases k <;> rfl

@[simp] theorem focusable_handleKey (k : ControlKind α) (s : Size) (e : KeyEvent) :
    (k.handleKey s e).1.focusable = k.focusable := by
  cases k <;> try rfl
  next b =>
    show Widget.focusable (Widget.handleKey b s e).1 = Widget.focusable b
    simp only [Widget.handleKey]
    split <;> rfl

@[simp] theorem focusable_handleMouse (k : ControlKind α) (s : Size) (e : MouseEvent) :
    (k.handleMouse s e).1.focusable = k.focusable := by
  cases k <;> try rfl
  next b =>
    show Widget.focusable (Widget.handleMouse b s e).1 = Widget.focusable b
    simp only [Widget.handleMouse, Button.handleMouse]
    split <;> (try split) <;> (try split) <;> rfl

theorem focusable_hotkey {k k' : ControlKind α} {c : Char} {r : Reply}
    (h : k.hotkey c = some (k', r)) : k'.focusable = k.focusable := by
  cases k with
  | label l =>
    simp only [hotkey, withWidget, Widget.hotkey] at h
    split at h
    · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨_, _, rfl, _⟩ := h
      rfl
    · cases h
  | button b =>
    simp only [hotkey, withWidget, Widget.hotkey] at h
    split at h
    · cases h; rfl
    · cases h
  | checkBoxes cb =>
    simp only [hotkey, withWidget, Widget.hotkey, Option.map_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    cases h; rfl
  | radioButtons rb =>
    simp only [hotkey, withWidget, Widget.hotkey, Option.map_eq_some_iff] at h
    obtain ⟨_, -, h⟩ := h
    cases h; rfl
  | _ => cases h

end ControlKind

namespace Window

variable {α : Type}

/-- The focus, if any, rests on a control that can take it. -/
def FocusValid (w : Window α) : Prop := ∀ i, w.focus = some i → w.focusable i = true

/-- Replacing control `i`'s kind by one of the same focusability keeps every
control's focusability. -/
theorem focusable_updateKind (w : Window α) (i : Nat) (k : ControlKind α)
    (hk : ∀ c ∈ w.controls[i]?, k.focusable = c.kind.focusable) (j : Nat) :
    (w.updateKind i k).focusable j = w.focusable j := by
  simp only [focusable, updateKind, Array.getElem?_modify]
  split
  · next hij =>
    subst hij
    cases hc : w.controls[i]? with
    | none => rfl
    | some c => simpa using hk c hc
  · rfl

theorem FocusValid.setFocus {w : Window α} (h : w.FocusValid) (i : Nat) : (w.setFocus i).FocusValid := by
  unfold Window.setFocus
  split
  · exact h
  · next hn =>
    intro j hj
    simp only [Option.some.injEq] at hj
    subst hj
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', not_or, Bool.not_eq_false] at hn
    obtain ⟨-, hf⟩ := hn
    simpa [focusable, Array.getElem?_modify, Function.comp_def] using hf

theorem FocusValid.focusNext {w : Window α} (h : w.FocusValid) (forward : Bool) :
    (w.focusNext forward).FocusValid := by
  unfold Window.focusNext
  dsimp only
  by_cases hn : w.controls.size = 0
  · simp only [hn, beq_self_eq_true, ite_true]; exact h
  · simp only [hn, beq_iff_eq, ite_false]
    split
    · exact h.setFocus _
    · exact h

theorem FocusValid.initFocus {w : Window α} (h : w.FocusValid) : w.initFocus.FocusValid := by
  unfold Window.initFocus
  split
  · exact h
  · split
    · exact h.setFocus _
    · exact h

theorem FocusValid.updateKind {w : Window α} (h : w.FocusValid) (i : Nat) (k : ControlKind α)
    (hk : ∀ c ∈ w.controls[i]?, k.focusable = c.kind.focusable) : (w.updateKind i k).FocusValid :=
  fun j hj => (focusable_updateKind w i k hk j).trans (h j hj)

theorem FocusValid.applyReply {w : Window α} (h : w.FocusValid) (i : Nat) (r : Reply) :
    (w.applyReply i r).1.FocusValid := by
  unfold Window.applyReply
  split
  · exact h
  · exact h
  · split <;> exact h
  · split
    · exact h.setFocus _
    · exact h
  · exact h

theorem FocusValid.dispatchHotkey {w : Window α} (h : w.FocusValid) {ch : Char}
    {res : Window α × WindowReply α} (hres : w.dispatchHotkey ch = some res) : res.1.FocusValid := by
  unfold Window.dispatchHotkey at hres
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some hres
  cases hc : w.controls[i]? with
  | none => simp [hc] at hi
  | some c =>
    cases hk : c.kind.hotkey ch with
    | none => simp [hc, hk] at hi
    | some kr =>
      obtain ⟨k, r⟩ := kr
      simp only [hc, hk, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hi
      rw [← hi]
      refine ((h.updateKind i k ?_).setFocus i).applyReply i r
      intro c' hc'
      rw [hc] at hc'
      cases hc'
      exact ControlKind.focusable_hotkey hk

theorem FocusValid.keyToFocus {w : Window α} (h : w.FocusValid) (k : KeyEvent) :
    (w.keyToFocus k).1.FocusValid := by
  unfold Window.keyToFocus
  split
  · next i c hi hc =>
    refine (h.updateKind i _ fun c' hc' => ?_).applyReply i _
    simp only [Window.focused?, hi, Option.bind_some] at hc
    rw [hc] at hc'
    cases hc'
    exact ControlKind.focusable_handleKey _ _ _
  · exact h

theorem FocusValid.keyFallback {w : Window α} (h : w.FocusValid) (k : KeyEvent) :
    (w.keyFallback k).1.FocusValid := by
  unfold Window.keyFallback
  dsimp only
  split
  · next res hres =>
    obtain ⟨ch, -, hch⟩ := Option.bind_eq_some_iff.1 hres
    exact h.dispatchHotkey hch
  · exact h.focusNext _
  · split <;> exact h
  · split <;> exact h
  · exact h

/-- **Focus stays valid** under every key press a window handles. -/
theorem FocusValid.handleKey {w : Window α} (h : w.FocusValid) (k : KeyEvent) :
    (w.handleKey k).1.FocusValid := by
  have hk := h.keyToFocus k
  unfold Window.handleKey
  generalize w.keyToFocus k = p at hk ⊢
  obtain ⟨w', r⟩ := p
  cases r <;> simp only at hk ⊢
  · exact hk.keyFallback k
  all_goals exact hk

/-- **Focus stays valid** under every mouse event delivered to a control. -/
theorem FocusValid.mouseControl {w : Window α} (h : w.FocusValid) (i : Nat) (e : MouseEvent) :
    (w.mouseControl i e).1.FocusValid := by
  unfold Window.mouseControl
  dsimp only
  have h' : (if e.action == .press then w.setFocus i else w).FocusValid := by
    split
    · exact h.setFocus i
    · exact h
  generalize (if e.action == .press then w.setFocus i else w) = w' at h' ⊢
  split
  · next c hc =>
    refine (h'.updateKind i _ fun c' hc' => ?_).applyReply i _
    rw [hc] at hc'
    cases hc'
    exact ControlKind.focusable_handleMouse _ _ _
  · exact h'

theorem FocusValid.cancelMouse {w : Window α} (h : w.FocusValid) (i : Nat) :
    (w.cancelMouse i).FocusValid := by
  intro j hj
  have hf := h j (by simpa [Window.cancelMouse] using hj)
  unfold focusable at hf ⊢
  simp only [Window.cancelMouse, Array.getElem?_modify]
  split
  · cases hc : w.controls[j]? <;> simp_all
  · exact hf

/-- A window without focus trivially has a valid focus. -/
theorem focusValid_of_none {w : Window α} (h : w.focus = none) : w.FocusValid := by
  intro i hi; simp [h] at hi

/-- Tab reaches a focusable control whenever the window has one. -/
theorem focusNext_focusable (w : Window α) (forward : Bool) (i : Nat) (hi : w.focusable i = true) :
    ∃ j, (w.focusNext forward).focus = some j ∧ (w.focusNext forward).focusable j = true := by
  have hlt : i < w.controls.size := by
    unfold focusable at hi
    cases hc : w.controls[i]? with
    | none => simp [hc] at hi
    | some _ => exact (Array.getElem?_eq_some_iff.1 hc).1
  unfold Window.focusNext
  dsimp only
  have hn : w.controls.size ≠ 0 := by omega
  simp only [beq_iff_eq, hn, ite_false]
  split
  · next j hj =>
    have hjf := List.find?_some hj
    unfold Window.setFocus
    split
    · next hs =>
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hs
      rcases hs with hs | hs
      · exact ⟨j, hs, hjf⟩
      · simp [hjf] at hs
    · refine ⟨j, rfl, ?_⟩
      simp only [focusable, Array.getElem?_modify, ite_true]
      unfold focusable at hjf
      cases hc : w.controls[j]? with
      | none => simp [hc] at hjf
      | some c => simpa [hc] using hjf
  · next hnone =>
    exfalso
    have := List.find?_eq_none.1 hnone i (mem_cyclicOrder.2 hlt)
    simp [hi] at this

/-! ### Frame hit-testing -/

/-- The close icon `[■]` is drawn at columns 2‥4 of the title bar; its centre closes. -/
theorem frameHit_close (w : Window α) (hc : w.flags.close = true) : w.frameHit ⟨3, 0⟩ = .close := by
  simp [frameHit, hc]

/-- The zoom icon `[↑]` is drawn at columns `w-5‥w-3`; its centre zooms. -/
theorem frameHit_zoom (w : Window α) (hz : w.flags.zoom = true) (hw : 10 ≤ w.bounds.w) :
    w.frameHit ⟨(w.bounds.w : Int) - 4, 0⟩ = .zoom := by
  unfold frameHit
  simp only [beq_self_eq_true, ite_true, hz, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
  split
  · omega
  · split
    · rfl
    · omega

/-- The resize corner `─┘` is drawn at the bottom-right; it starts a resize. -/
theorem frameHit_resize (w : Window α) (hg : w.flags.grow = true) (hh : 2 ≤ w.bounds.h) :
    w.frameHit ⟨(w.bounds.w : Int) - 1, (w.bounds.h : Int) - 1⟩ = .resize := by
  unfold frameHit
  simp only [beq_iff_eq, hg, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  split
  · omega
  · split
    · rfl
    · next hn => exact absurd ⟨trivial, by omega⟩ hn

/-- Pressing on the title bar between the icons starts moving the window. -/
theorem frameHit_move (w : Window α) (hm : w.flags.move = true) (x : Int) (h₁ : 5 ≤ x)
    (h₂ : x < (w.bounds.w : Int) - 5) : w.frameHit ⟨x, 0⟩ = .move := by
  unfold frameHit
  simp only [beq_self_eq_true, ite_true, hm, Bool.and_eq_true, decide_eq_true_eq]
  split
  · omega
  · split
    · omega
    · rfl

end Window

end HyperVision
