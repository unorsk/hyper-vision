import HyperVision.App

/-!
# Menus and drop-down lists: hit-testing theorems

Hit-testing agrees with the layout used for drawing:

* clicking anywhere on the drawn title of menu `i` in the menu bar (including its
  padding blanks) selects menu `i`;
* clicking a drawn row of a drop-down list selects the item shown on that row;
* keyboard navigation in a drop-down box never lands on a separator.
-/

namespace HyperVision

namespace MenuBar

variable {α : Type}

/-- Width of the title of menu `j` (0 past the end). -/
def titleWidth (menus : Array (Menu α)) (j : Nat) : Nat := (menus[j]?.map (·.title.width)).getD 0

theorem itemX_eq (menus : Array (Menu α)) (i : Nat) :
    itemX menus i = 1 + (menus.toList.take i).foldl (fun acc m => acc + m.title.width + 2) 0 := by
  unfold itemX
  rw [← Array.foldl_toList, Array.toList_extract, List.extract_eq_take_drop]
  simp

theorem itemX_succ (menus : Array (Menu α)) {j : Nat} (hj : j < menus.size) :
    itemX menus (j + 1) = itemX menus j + titleWidth menus j + 2 := by
  rw [itemX_eq, itemX_eq, List.take_add_one, List.foldl_append]
  have : menus.toList[j]? = some menus[j] := by simp [hj]
  simp [this, titleWidth, hj]
  omega

/-- Titles are laid out left to right without overlap. -/
theorem itemX_end_le (menus : Array (Menu α)) {j i : Nat} (hji : j < i) (hi : i ≤ menus.size) :
    itemX menus j + titleWidth menus j + 2 ≤ itemX menus i := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hji with h | rfl
    · have := ih h (by omega)
      rw [itemX_succ menus (by omega)]
      omega
    · rw [itemX_succ menus (by omega)]
      exact Nat.le_refl _

/-- **Clicking a menu title opens that menu**: every column of the drawn title
`" title "` of menu `i` hits menu `i`. -/
theorem itemAt?_title (menus : Array (Menu α)) {i : Nat} (hi : i < menus.size) {x : Int}
    (hx₁ : (itemX menus i : Int) ≤ x) (hx₂ : x < itemX menus i + titleWidth menus i + 2) :
    itemAt? menus x = some i := by
  unfold itemAt?
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨?_, i, by simpa using hi, by simp, fun j hj => ?_⟩
  · simp only [titleWidth, Array.getElem?_eq_getElem hi, Option.map_some, Option.getD_some] at hx₂
    simp [hi]
    omega
  · have hj' : j < i := by simpa using hj
    have := itemX_end_le menus hj' (by omega)
    simp only [titleWidth, Array.getElem?_eq_getElem (show j < menus.size by omega), Option.map_some,
      Option.getD_some] at this
    simp [show j < menus.size by omega]
    omega

/-- Keyboard navigation (`Up`/`Down`) never highlights a separator, as long as the box
has an item that is not one. -/
theorem step_not_separator (items : Array (MenuItem α)) (i : Nat) (forward : Bool)
    (h : ∃ j, ∃ hj : j < items.size, items[j].isSeparator = false) :
    (items[step items i forward]?.map (·.isSeparator)) = some false := by
  obtain ⟨j, hj, hsep⟩ := h
  have hn : items.size ≠ 0 := by omega
  unfold step
  simp only [beq_iff_eq, hn, ite_false]
  cases hf : (cyclicOrder items.size i forward).find?
      (fun j => !((items[j]?.map (·.isSeparator)).getD true)) with
  | some k =>
    have := List.find?_some hf
    simp only [Option.getD_some]
    cases hk : items[k]? with
    | none => simp [hk] at this
    | some it => simp_all
  | none =>
    have := List.find?_eq_none.1 hf j (mem_cyclicOrder.2 hj)
    simp [hj, hsep] at this

end MenuBar

namespace Popup

/-- **Clicking a row of a drop-down list selects the item drawn on that row.** Row `r`
of the list (drawn at `rect.y + 1 + r`) shows item `top + r`. -/
theorem itemAt?_row (p : Popup) {x : Int} {r : Nat} (hx₁ : p.rect.x < x) (hx₂ : x < p.rect.right - 1)
    (hr : r < p.listHeight) (hi : p.top + r < p.items.size) :
    p.itemAt? ⟨x, p.rect.y + 1 + r⟩ = some (p.top + r) := by
  unfold itemAt?
  dsimp only
  split
  · simp; omega
  · next hc => exfalso; apply hc; simp; omega

/-- Clicks outside the list rows never select anything. -/
theorem itemAt?_outside (p : Popup) (pos : Point) (h : pos.y ≤ p.rect.y ∨ p.rect.y + 1 + p.listHeight ≤ pos.y) :
    p.itemAt? pos = none := by
  unfold itemAt?
  dsimp only
  split
  · next hc => simp at hc; omega
  · rfl

end Popup

end HyperVision
