import HyperVision.Control

/-!
# List boxes: correctness theorems

* **Focus.** After every key press and mouse event the focused item is an item of the
  list (or the list is empty), and it lies in a row on screen.
* **Navigation.** `Down` and `Up` move the focus by exactly one item, unless it is
  already at the end of the list.
* **Reading back.** `ListBox.focused?` only ever names an existing item, so a program
  can index the array it built the list from.
-/

namespace HyperVision

namespace ListBox

/-- The invariant of a list box shown at size `s`: the focus is on an item (or on the
first row of an empty list) and it is visible. -/
def Valid (l : ListBox) (s : Size) : Prop :=
  l.focused < max l.items.size 1 ∧ l.top ≤ l.focused ∧ l.focused < l.top + rows s

/-- The invariant does not depend on the scroll bar's mouse state. -/
@[simp] theorem valid_scrollGrab (l : ListBox) (s : Size) (g : Option Bool) :
    ({ l with scrollGrab := g } : ListBox).Valid s ↔ l.Valid s := Iff.rfl

theorem valid_focusItem (l : ListBox) (s : Size) (i : Int) : (l.focusItem s i).Valid s := by
  unfold focusItem Valid rows clampInt
  dsimp only
  split <;> (try split) <;> omega

theorem valid_adjust (l : ListBox) (s : Size) : (l.adjust s).Valid s := valid_focusItem _ _ _

/-- **The focus stays on a visible item** under every key press. -/
theorem valid_handleKey (l : ListBox) (s : Size) (k : KeyEvent) : (l.handleKey s k).1.Valid s := by
  unfold handleKey
  dsimp only
  split
  · exact valid_adjust l s
  · split <;> (try split) <;> first | exact valid_focusItem _ _ _ | exact valid_adjust l s

/-- **The focus stays on a visible item** under every mouse event. -/
theorem valid_handleMouse (l : ListBox) (s : Size) (m : MouseEvent) :
    (l.handleMouse s m).1.Valid s := by
  unfold handleMouse
  dsimp only
  split
  · exact valid_focusItem _ _ _
  · exact valid_focusItem _ _ _
  · split
    · split
      · exact valid_adjust l s
      · exact (valid_scrollGrab _ _ _).2 (valid_focusItem _ _ _)
    · split
      · split <;> exact valid_focusItem _ _ _
      · exact valid_adjust l s
  · split
    · exact valid_focusItem _ _ _
    · exact valid_adjust l s
    · split
      · exact valid_focusItem _ _ _
      · split <;> exact valid_focusItem _ _ _
  · exact valid_adjust l s
  · exact valid_adjust l s

/-- Hence a list box never shows a focus outside its items, whatever arrives. -/
theorem focused_lt_handleKey (l : ListBox) (s : Size) (k : KeyEvent) (h : 0 < l.items.size) :
    (l.handleKey s k).1.focused < (l.handleKey s k).1.items.size := by
  have := (valid_handleKey l s k).1
  have hs : (l.handleKey s k).1.items = l.items := by
    unfold handleKey; dsimp only; split
    · rfl
    · split <;> (try split) <;> rfl
  rw [hs] at this ⊢
  omega

/-- `Down` moves the focus to the next item, unless it is on the last one. -/
theorem focused_down (l : ListBox) (s : Size) (h : (l.adjust s).focused + 1 < l.items.size) :
    (l.handleKey s (KeyEvent.plain .down)).1.focused = (l.adjust s).focused + 1 := by
  have hs : (l.adjust s).items.size = l.items.size := rfl
  simp only [handleKey, KeyEvent.plain, Bool.false_eq_true, ↓reduceIte,
    focusItem, clampInt]
  omega

/-- `Up` moves the focus to the previous item, unless it is on the first one. -/
theorem focused_up (l : ListBox) (s : Size) (h : 0 < (l.adjust s).focused) :
    (l.handleKey s (KeyEvent.plain .up)).1.focused = (l.adjust s).focused - 1 := by
  have := (valid_adjust l s).1
  have hs : (l.adjust s).items.size = l.items.size := rfl
  simp only [handleKey, KeyEvent.plain, Bool.false_eq_true, ↓reduceIte,
    focusItem, clampInt]
  omega

theorem focused?_lt {l : ListBox} {i : Nat} (h : l.focused? = some i) : i < l.items.size := by
  unfold focused? at h
  split at h <;> simp_all

/-- New items keep the focus on an item. -/
theorem setItems_focused_lt (l : ListBox) (items : Array String) (h : 0 < items.size) :
    (l.setItems items).focused < items.size := by
  simp only [setItems]
  omega

end ListBox

theorem Control.listFocused?_lt {α : Type} {c : Control α} {i : Nat} (h : c.listFocused? = some i) :
    ∃ l, c.kind = .listBox l ∧ i < l.items.size := by
  unfold Control.listFocused? at h
  split at h
  · exact ⟨_, ‹_›, ListBox.focused?_lt h⟩
  · simp at h

end HyperVision
