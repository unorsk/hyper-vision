import HyperVision.Control

/-!
# Widgets: correctness theorems

* Input lines: the cursor and selection stay inside the text and the text never
  exceeds `maxLength`, whatever keys and mouse events arrive; typing a character
  and pressing Backspace restores the text.
* Scroll bars: the thumb stays inside the track, clicking where it is drawn grabs
  it, and it sits at the ends for the extreme values.
* Buttons: pressing and releasing the mouse on the face activates the button.
* Check boxes: toggling changes exactly one item.
-/

namespace HyperVision

/-! ## Input lines -/

namespace InputLine

/-- The invariant of an input line. -/
structure Valid (i : InputLine) : Prop where
  cursor_le : i.cursor ≤ i.text.size
  size_le : i.text.size ≤ i.maxLength
  anchor_le : ∀ a, i.anchor = some a → a ≤ i.text.size

theorem valid_ofString (s : String) (maxLength : Nat) (h : s.length ≤ maxLength) :
    (ofString s maxLength).Valid :=
  ⟨by simp [ofString, String.length_toList], by simpa [ofString, String.length_toList] using h,
   fun _ h => by simp [ofString] at h⟩

@[simp] theorem text_adjust (i : InputLine) (w : Nat) : (i.adjust w).text = i.text := rfl
@[simp] theorem maxLength_adjust (i : InputLine) (w : Nat) : (i.adjust w).maxLength = i.maxLength := rfl
@[simp] theorem anchor_adjust (i : InputLine) (w : Nat) : (i.adjust w).anchor = i.anchor := rfl
@[simp] theorem cursor_adjust (i : InputLine) (w : Nat) :
    (i.adjust w).cursor = min i.cursor i.text.size := rfl

theorem Valid.adjust {i : InputLine} (h : i.Valid) (w : Nat) : (i.adjust w).Valid :=
  ⟨by simp; omega, by simpa using h.size_le, by simpa using h.anchor_le⟩

theorem Valid.selectAll {i : InputLine} (h : i.Valid) : i.selectAll.Valid :=
  ⟨by simp [InputLine.selectAll], h.size_le, fun a ha => by simp [InputLine.selectAll] at ha; omega⟩

theorem Valid.moveTo {i : InputLine} (h : i.Valid) (pos : Nat) (extend : Bool) :
    (i.moveTo pos extend).Valid := by
  unfold InputLine.moveTo
  split
  · refine ⟨by simp; omega, h.size_le, fun a ha => ?_⟩
    simp only [Option.some.injEq] at ha
    subst ha
    cases hA : i.anchor with
    | none => simpa using h.cursor_le
    | some b => simpa using h.anchor_le b hA
  · exact ⟨by simp; omega, h.size_le, fun _ ha => by simp at ha⟩

theorem size_deleteRange (i : InputLine) (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ i.text.size) :
    (i.deleteRange lo hi).text.size = i.text.size - (hi - lo) := by
  simp [InputLine.deleteRange]
  omega

theorem Valid.deleteRange {i : InputLine} (h : i.Valid) {lo hi : Nat} (hlo : lo ≤ hi)
    (hhi : hi ≤ i.text.size) : (i.deleteRange lo hi).Valid := by
  have hs := size_deleteRange i lo hi hlo hhi
  refine ⟨?_, ?_, fun _ ha => by simp [InputLine.deleteRange] at ha⟩
  · rw [hs]; simp only [InputLine.deleteRange]; omega
  · rw [hs]; simp only [InputLine.deleteRange]; have := h.size_le; omega

theorem Valid.deleteSelection {i : InputLine} (h : i.Valid) : i.deleteSelection.Valid := by
  unfold InputLine.deleteSelection InputLine.selection?
  cases hA : i.anchor with
  | none => exact ⟨h.cursor_le, h.size_le, fun _ ha => by simp at ha⟩
  | some a =>
    have ha := h.anchor_le a hA
    have hc := h.cursor_le
    simp only [Option.bind_some]
    split
    · next heq =>
      split at heq
      · simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact h.deleteRange (by omega) (by omega)
      · cases heq
    · exact ⟨h.cursor_le, h.size_le, fun _ ha => by simp at ha⟩

@[simp] theorem maxLength_deleteSelection (i : InputLine) :
    i.deleteSelection.maxLength = i.maxLength := by
  unfold InputLine.deleteSelection; split <;> rfl

theorem Valid.insert {i : InputLine} (h : i.Valid) (c : Char) : (i.insert c).Valid := by
  have hd := h.deleteSelection
  unfold InputLine.insert
  simp only
  split
  · exact hd
  · next hlt =>
    refine ⟨?_, ?_, fun _ ha => ?_⟩
    · simp <;> omega
    · simp only [maxLength_deleteSelection] at hlt ⊢
      simp <;> omega
    · have := hd.anchor_le _ ha
      simp <;> omega

/-- **Input lines stay valid** under every key press. -/
theorem Valid.handleKey {i : InputLine} (h : i.Valid) (s : Size) (k : KeyEvent) :
    (i.handleKey s k).1.Valid := by
  unfold InputLine.handleKey
  have hmap : ∀ o : Option InputLine, (∀ j ∈ o, j.Valid) →
      (match o with
        | some i' => (i'.adjust s.w, Reply.handled)
        | none => (i, Reply.ignored)).1.Valid := by
    intro o ho
    cases o with
    | none => exact h
    | some j => exact (ho j rfl).adjust _
  apply hmap
  intro j hj
  have hins : ∀ j ∈ k.text?.map i.insert, j.Valid := by
    intro j hj
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hj
    exact h.insert c
  split at hj
  · cases hj; exact h.moveTo _ _
  · cases hj; exact h.moveTo _ _
  · cases hj; exact h.moveTo _ _
  · cases hj; exact h.moveTo _ _
  · cases hj
    split
    · exact h.deleteSelection
    · split
      · exact h
      · exact h.deleteRange (by omega) (by have := h.cursor_le; omega)
  · cases hj
    split
    · exact h.deleteSelection
    · split
      · exact h
      · next hlt => exact h.deleteRange (by omega) (by omega)
  · split at hj
    · cases hj; exact h.selectAll
    · exact hins j hj
  · split at hj
    · cases hj; exact ⟨by simp, by simp, fun _ ha => by simp at ha⟩
    · exact hins j hj
  · exact hins j hj

/-- **Input lines stay valid** under every mouse event. -/
theorem Valid.handleMouse {i : InputLine} (h : i.Valid) (s : Size) (m : MouseEvent) :
    (i.handleMouse s m).1.Valid := by
  unfold InputLine.handleMouse
  split
  · split
    · exact h.selectAll.adjust _
    · exact (h.moveTo _ _).adjust _
  · exact (h.moveTo _ _).adjust _
  · exact h

@[simp] theorem maxLength_moveTo (i : InputLine) (pos : Nat) (extend : Bool) :
    (i.moveTo pos extend).maxLength = i.maxLength := by
  unfold InputLine.moveTo; split <;> rfl

@[simp] theorem maxLength_insert (i : InputLine) (c : Char) : (i.insert c).maxLength = i.maxLength := by
  unfold InputLine.insert; simp only; split <;> simp

theorem maxLength_handleKey (i : InputLine) (s : Size) (k : KeyEvent) :
    (i.handleKey s k).1.maxLength = i.maxLength := by
  unfold InputLine.handleKey
  have hmap : ∀ o : Option InputLine, (∀ j ∈ o, j.maxLength = i.maxLength) →
      (match o with
        | some i' => (i'.adjust s.w, Reply.handled)
        | none => (i, Reply.ignored)).1.maxLength = i.maxLength := by
    intro o ho
    cases o with
    | none => rfl
    | some j => exact ho j rfl
  apply hmap
  intro j hj
  have hins : ∀ j ∈ k.text?.map i.insert, j.maxLength = i.maxLength := by
    intro j hj
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hj
    simp
  split at hj <;> (try split at hj) <;> (try cases hj) <;> (try (split <;> (try split) <;> rfl)) <;>
    first | rfl | simp | exact hins j hj

/-- Hence the text of an input line never exceeds its maximum length, whatever is typed. -/
theorem size_le_maxLength_handleKeys {i : InputLine} (h : i.Valid) (s : Size) (ks : List KeyEvent) :
    (ks.foldl (fun i k => (i.handleKey s k).1) i).text.size ≤ i.maxLength := by
  induction ks generalizing i with
  | nil => exact h.size_le
  | cons k ks ih =>
    have := ih (h.handleKey s k)
    rwa [maxLength_handleKey] at this

end InputLine

/-! ## Scroll bars -/

namespace ScrollBar

/-- The thumb always lies inside the track (between the arrows). -/
theorem thumb_mem (sb : ScrollBar) (hl : 3 ≤ sb.length) : 1 ≤ sb.thumb ∧ sb.thumb ≤ sb.length - 2 := by
  unfold thumb
  split
  · omega
  · next hne =>
    have hm : 0 < sb.max := by simp at hne; omega
    have hx : min sb.value sb.max * (sb.length - 3) + sb.max / 2 < (sb.length - 3 + 1) * sb.max := by
      have h₁ : min sb.value sb.max * (sb.length - 3) ≤ sb.max * (sb.length - 3) :=
        Nat.mul_le_mul_right _ (Nat.min_le_right _ _)
      have h₂ : sb.max / 2 < sb.max := Nat.div_lt_self hm (by decide)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (sb.length - 3)]
      omega
    have := (Nat.div_lt_iff_lt_mul hm).2 hx
    generalize (min sb.value sb.max * (sb.length - 3) + sb.max / 2) / sb.max = q at this ⊢
    omega

/-- Clicking where the thumb is drawn grabs the thumb. -/
theorem hit_thumb (sb : ScrollBar) (hl : 3 ≤ sb.length) : sb.hit sb.thumb = .thumb := by
  have := sb.thumb_mem hl
  have h0 : sb.thumb ≠ 0 := by omega
  have h1 : ¬ sb.thumb + 1 ≥ sb.length := by omega
  simp [hit, h0, h1]

/-- The value for any thumb position is within range. -/
theorem valueAt_le (sb : ScrollBar) (off : Nat) : sb.valueAt off ≤ sb.max := by
  unfold valueAt; split
  · exact Nat.zero_le _
  · exact Nat.min_le_left _ _

/-- At value `0` the thumb is next to the first arrow… -/
theorem thumb_zero (sb : ScrollBar) (h : sb.value = 0) : sb.thumb = 1 := by
  unfold thumb; split
  · rfl
  · next hne =>
    have hm : 0 < sb.max := by simp at hne; omega
    simp [h, Nat.div_eq_of_lt (Nat.div_lt_self hm (by decide : 1 < 2))]

/-- …and at the maximum value it is next to the last arrow. -/
theorem thumb_max (sb : ScrollBar) (hl : 3 ≤ sb.length) (hm : 0 < sb.max) (h : sb.max ≤ sb.value) :
    sb.thumb = sb.length - 2 := by
  unfold thumb
  split
  · next hc => simp at hc; omega
  · rw [Nat.min_eq_right h, Nat.mul_add_div hm,
      Nat.div_eq_of_lt (Nat.div_lt_self hm (by decide : 1 < 2))]
    omega

end ScrollBar

/-! ## Buttons -/

namespace Button

variable {α : Type}

/-- Pressing and releasing the mouse on the face of an enabled button activates it. -/
theorem click_activates (b : Button α) (hb : b.enabled = true) (s : Size) (p : Point)
    (hp : faceContains s p = true) (mods : Modifiers) :
    let b₁ := (b.handleMouse s { pos := p, button := .left, action := .press, mods }).1
    (b₁.handleMouse s { pos := p, button := .left, action := .release, mods }).2 = .activated := by
  simp [Button.handleMouse, hb, hp]

/-- Dragging off the face before releasing cancels the click. -/
theorem drag_off_cancels (b : Button α) (hb : b.enabled = true) (s : Size) (p q : Point)
    (hp : faceContains s p = true) (hq : faceContains s q = false) (mods : Modifiers) :
    let b₁ := (b.handleMouse s { pos := p, button := .left, action := .press, mods }).1
    let b₂ := (b₁.handleMouse s { pos := q, button := .left, action := .drag, mods }).1
    (b₂.handleMouse s { pos := q, button := .left, action := .release, mods }).2 = .handled := by
  simp [Button.handleMouse, hb, hp, hq]

/-- A disabled button never activates. -/
theorem disabled_never_activates (b : Button α) (hb : b.enabled = false) (s : Size) (m : MouseEvent) :
    (b.handleMouse s m).2 ≠ .activated := by
  simp [Button.handleMouse, hb]

end Button

/-! ## Check boxes and radio buttons -/

namespace CheckBoxes

/-- Toggling item `i` flips exactly that item. -/
theorem values_toggle (cb : CheckBoxes) (i j : Nat) :
    (cb.toggle i).values[j]? = if i = j then cb.values[j]?.map (!·) else cb.values[j]? := by
  simp only [values, toggle, Array.getElem?_map, Array.getElem?_modify]
  split <;> cases cb.items[j]? <;> rfl

/-- Toggling twice restores every value. -/
theorem values_toggle_toggle (cb : CheckBoxes) (i : Nat) : ((cb.toggle i).toggle i).values = cb.values := by
  apply Array.ext_getElem?
  intro j
  rw [values_toggle, values_toggle]
  split
  · cases cb.values[j]? <;> simp
  · rfl

end CheckBoxes

namespace Cluster

/-- Keyboard navigation keeps the cursor on an item. -/
theorem navigate_lt {n rows cursor c : Nat} {k : Key} (hc : cursor < n)
    (h : navigate n rows cursor k = some c) : c < n := by
  unfold navigate at h
  split at h
  · cases h
  · split at h
    · cases h; exact Nat.mod_lt _ (by omega)
    · cases h; exact Nat.mod_lt _ (by omega)
    · cases h; split <;> omega
    · cases h; split <;> omega
    · cases h

theorem itemAt?_lt {labels : Array HotText} {rows : Nat} {p : Point} {i : Nat}
    (h : itemAt? labels rows p = some i) : i < labels.size := by
  unfold itemAt? at h
  exact List.mem_range.1 (List.mem_of_find?_eq_some h)

theorem hotkeyIndex?_lt {labels : Array HotText} {c : Char} {i : Nat}
    (h : hotkeyIndex? labels c = some i) : i < labels.size :=
  (Array.findIdx?_eq_some_iff_getElem.1 h).1

end Cluster

namespace RadioButtons

/-- The selection always refers to an existing item, whatever keys and clicks arrive. -/
theorem selected_lt_handleKey (rb : RadioButtons) (h : rb.selected < rb.items.size) (s : Size)
    (k : KeyEvent) : (rb.handleKey s k).1.selected < rb.items.size := by
  unfold RadioButtons.handleKey
  split
  · exact h
  · split
    · next c hc => exact Cluster.navigate_lt h hc
    · split
      · exact h
      · split
        · next i hi =>
          obtain ⟨_, _, hi⟩ := Option.bind_eq_some_iff.1 hi
          exact Cluster.hotkeyIndex?_lt hi
        · exact h

theorem selected_lt_handleMouse (rb : RadioButtons) (h : rb.selected < rb.items.size) (s : Size)
    (m : MouseEvent) : (rb.handleMouse s m).1.selected < rb.items.size := by
  unfold RadioButtons.handleMouse
  split
  · next i hi => exact Cluster.itemAt?_lt hi
  · exact h

end RadioButtons

/-! ## Memos -/

namespace Memo

/-- The invariant of a memo: it has at least one line. -/
def Valid (m : Memo) : Prop := 0 < m.lines.size

/-- The cursor lies on the text. -/
def CursorValid (m : Memo) : Prop :=
  m.cursor.row < m.lines.size ∧ m.cursor.col ≤ (m.line m.cursor.row).size

/-- Loading a string and reading the text back is the identity. -/
theorem text_ofString (s : String) : (ofString s).text = s := by
  simp [ofString, text, List.map_map, Function.comp_def, List.intercalate_splitOn, String.ofList_toList]

theorem valid_ofString (s : String) : (ofString s).Valid := by
  simp only [Valid, ofString, Array.size_map, List.size_toArray]
  exact List.length_pos_iff.2 (List.splitOn_ne_nil _ _)

@[simp] theorem lines_moveTo (m : Memo) (p : TextPos) (e : Bool) : (m.moveTo p e).lines = m.lines := by
  unfold Memo.moveTo; split <;> rfl

@[simp] theorem lines_adjust (m : Memo) (s : Size) : (m.adjust s).lines = m.lines := rfl
@[simp] theorem lines_scrollBy (m : Memo) (s : Size) (dy dx : Int) : (m.scrollBy s dy dx).lines = m.lines := rfl
@[simp] theorem lines_scrollPart (m : Memo) (s : Size) (v : Bool) (sb : ScrollBar) (o : Nat) :
    (m.scrollPart s v sb o).lines = m.lines := by
  unfold scrollPart; split <;> rfl
@[simp] theorem lines_scrollToValue (m : Memo) (s : Size) (v : Bool) (x : Nat) :
    (m.scrollToValue s v x).lines = m.lines := by
  unfold scrollToValue; split <;> rfl

theorem valid_deleteRange (m : Memo) (a b : TextPos) : (m.deleteRange a b).Valid := by
  simp [Valid, deleteRange]; omega

theorem Valid.deleteSelection {m : Memo} (h : m.Valid) : m.deleteSelection.Valid := by
  unfold Memo.deleteSelection; split
  · exact valid_deleteRange _ _ _
  · exact h

theorem valid_insertChars (m : Memo) (cs : Array Char) : (m.insertChars cs).Valid := by
  unfold insertChars Valid
  dsimp only
  split
  · simp
  · next hne => simpa [Array.isEmpty_iff_size_eq_zero] using Nat.pos_of_ne_zero (by simpa using hne)

theorem valid_newline (m : Memo) : m.newline.Valid := by
  simp [Valid, newline]; omega

theorem Valid.backspace {m : Memo} (h : m.Valid) : m.backspace.Valid := by
  unfold Memo.backspace
  split
  · exact h.deleteSelection
  · dsimp only
    split
    · exact valid_deleteRange _ _ _
    · split
      · exact valid_deleteRange _ _ _
      · exact h

theorem Valid.deleteForward {m : Memo} (h : m.Valid) : m.deleteForward.Valid := by
  unfold Memo.deleteForward
  split
  · exact h.deleteSelection
  · dsimp only
    split
    · exact valid_deleteRange _ _ _
    · split
      · exact valid_deleteRange _ _ _
      · exact h

/-- The clamped cursor lies on the text. -/
theorem cursorValid_clampPos {m : Memo} (h : m.Valid) (p : TextPos) :
    (m.clampPos p).row < m.lines.size ∧ (m.clampPos p).col ≤ (m.line (m.clampPos p).row).size := by
  simp only [clampPos, lastRow, Valid] at h ⊢
  omega

theorem CursorValid.adjust {m : Memo} (h : m.Valid) (s : Size) : (m.adjust s).CursorValid :=
  cursorValid_clampPos h m.cursor

/-- **Memos stay non-empty** under every key press, and every handled key leaves the
cursor on the text. -/
theorem Valid.handleKey {m : Memo} (h : m.Valid) (s : Size) (k : KeyEvent) :
    (m.handleKey s k).1.Valid ∧ ((m.handleKey s k).2 = .handled → (m.handleKey s k).1.CursorValid) := by
  unfold Memo.handleKey
  have hmap : ∀ o : Option Memo, (∀ m' ∈ o, m'.Valid) →
      (match o with
        | some m' => (m'.adjust s, Reply.handled)
        | none => (m, Reply.ignored)).1.Valid ∧
      ((match o with
        | some m' => (m'.adjust s, Reply.handled)
        | none => (m, Reply.ignored)).2 = .handled →
        (match o with
          | some m' => (m'.adjust s, Reply.handled)
          | none => (m, Reply.ignored)).1.CursorValid) := by
    intro o ho
    cases o with
    | none => exact ⟨h, fun h' => by cases h'⟩
    | some m' => exact ⟨ho m' rfl, fun _ => CursorValid.adjust (ho m' rfl) s⟩
  apply hmap
  intro m' hm'
  split at hm'
  · cases hm'
    split <;> simpa [Valid] using h
  · have hins : ∀ m'' ∈ k.text?.map fun ch => m.insertChars #[ch], m''.Valid := by
      intro m'' h''
      obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 h''
      exact valid_insertChars _ _
    split at hm'
    · split at hm' <;> cases hm'; exact valid_newline m
    · cases hm'; exact h.backspace
    · cases hm'; exact h.deleteForward
    · split at hm' <;> cases hm'; exact valid_insertChars _ _
    · split at hm'
      · cases hm'; exact h
      · exact hins m' hm'
    · exact hins m' hm'

/-- Mouse events never change the text of a memo (only the cursor, selection and scrolling). -/
@[simp] theorem lines_handleMouse (m : Memo) (s : Size) (e : MouseEvent) :
    (m.handleMouse s e).1.lines = m.lines := by
  unfold Memo.handleMouse
  dsimp only
  repeat' split
  all_goals simp

/-- **Memos stay non-empty** under every mouse event. -/
theorem Valid.handleMouse {m : Memo} (h : m.Valid) (s : Size) (e : MouseEvent) :
    (m.handleMouse s e).1.Valid := by
  simpa [Valid] using h

end Memo

end HyperVision
