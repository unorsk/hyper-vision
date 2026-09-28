import HyperVision.Window

/-!
# File lists: correctness theorems

* **Order.** A listing is a permutation of the entries read, sorted in Turbo Vision's
  order: files, then directories, then `..`, each group by name.
* **Wildcards.** `*` matches every name, and a pattern without `*` or `?` matches exactly
  the name it spells.
* **Focus.** After every key press and mouse event the focused entry is an entry of the
  list (or the list is empty) and lies within the columns on screen.
* **The information pane** of a file dialog describes the list's focused entry after
  every change of the list.
-/

namespace HyperVision

namespace FileEntry

theorem le_iff (a b : FileEntry) :
    le a b = true ↔ a.rank < b.rank ∨ (a.rank = b.rank ∧ a.name ≤ b.name) := by
  simp [le, String.not_lt]

theorem le_trans (a b c : FileEntry) : le a b = true → le b c = true → le a c = true := by
  simp only [le_iff]
  rintro (h₁ | ⟨h₁, h₁'⟩) (h₂ | ⟨h₂, h₂'⟩)
  · exact .inl (by omega)
  · exact .inl (by omega)
  · exact .inl (by omega)
  · exact .inr ⟨by omega, String.le_trans h₁' h₂'⟩

theorem le_total (a b : FileEntry) : (le a b || le b a) = true := by
  simp only [Bool.or_eq_true, le_iff]
  rcases Nat.lt_trichotomy a.rank b.rank with h | h | h
  · exact .inl (.inl h)
  · rcases String.le_total a.name b.name with h' | h'
    · exact .inl (.inr ⟨h, h'⟩)
    · exact .inr (.inr ⟨h.symm, h'⟩)
  · exact .inr (.inl h)

/-- Sorting only reorders the entries. -/
theorem sort_perm (es : Array FileEntry) : (sort es).toList.Perm es.toList := by
  simpa [sort] using List.mergeSort_perm es.toList le

/-- A sorted listing is in `TFileCollection` order. -/
theorem sort_sorted (es : Array FileEntry) : (sort es).toList.Pairwise (le · ·) := by
  simpa [sort] using List.pairwise_mergeSort le_trans le_total es.toList

/-- Files come before directories, and directories before `..`. -/
theorem sort_rank (es : Array FileEntry) {i j : Nat} (hij : i < j) (hj : j < (sort es).size) :
    (sort es)[i].rank ≤ (sort es)[j].rank := by
  have := List.pairwise_iff_getElem.1 (sort_sorted es) i j (by simpa using Nat.lt_trans hij hj)
    (by simpa using hj) hij
  simp only [Array.getElem_toList, le_iff] at this
  omega

end FileEntry

/-! ## Wildcards -/

/-- `*` matches every name. -/
theorem globMatch_star (s : List Char) : globMatch ['*'] s = true := by
  induction s with
  | nil => simp [globMatch]
  | cons c s ih => rw [globMatch]; simp [ih]

/-- A pattern without wildcard characters matches exactly the name it spells. -/
theorem globMatch_literal (p s : List Char) (hp : ∀ c ∈ p, c ≠ '*' ∧ c ≠ '?') :
    globMatch p s = true ↔ p = s := by
  induction p generalizing s with
  | nil => cases s <;> simp [globMatch]
  | cons c p ih =>
    have ⟨h₁, h₂⟩ := hp c (by simp)
    have ih' := fun s => ih s (fun d hd => hp d (by simp [hd]))
    cases s with
    | nil => simp [globMatch]
    | cons d s =>
      rw [globMatch]
      · simp [ih' s, Bool.and_eq_true, beq_iff_eq]
      · exact h₁
      · simpa using h₂

/-! ## Focus -/

namespace FileList

/-- The focused entry exists (or the list is empty) and lies in the columns shown for
a list of size `s`. -/
structure Valid (l : FileList) (s : Size) : Prop where
  focused_lt : l.focused < max l.entries.size 1
  top_le : l.top ≤ l.focused
  lt_page : l.focused < l.top + page s

theorem rows_pos (s : Size) : 0 < rows s := by unfold rows; omega

/-- **Focusing any position yields a valid list**: the target is clamped into the list,
and the view scrolls (by whole columns) to show it. -/
theorem focusItem_valid (l : FileList) (s : Size) (i : Int) : (l.focusItem s i).Valid s := by
  have hr := rows_pos s
  have hp : page s = rows s * 2 := rfl
  unfold focusItem
  dsimp only
  generalize hf : (clampInt i 0 ((l.entries.size - 1 : Nat) : Int)).toNat = f
  have hfn : f < max l.entries.size 1 := by
    rw [← hf]; unfold clampInt; omega
  have hm := Nat.mod_lt f hr
  have hle := Nat.mod_le f (rows s)
  generalize f % rows s = m at hm hle
  generalize rows s = r at hr hm hle hp
  simp only [columns]
  refine ⟨hfn, ?_, ?_⟩ <;> dsimp only <;> split <;> (try split) <;> omega

theorem Valid.congr {l l' : FileList} {s : Size} (h : l.Valid s) (he : l'.entries = l.entries)
    (hf : l'.focused = l.focused) (ht : l'.top = l.top) : l'.Valid s :=
  ⟨he ▸ hf ▸ h.focused_lt, hf ▸ ht ▸ h.top_le, hf ▸ ht ▸ h.lt_page⟩

theorem Valid.typeAhead {l : FileList} {s : Size} (h : l.Valid s) (c : Char) :
    (l.typeAhead s c).1.Valid s := by
  unfold FileList.typeAhead
  dsimp only
  split
  · next _ i _ => exact (focusItem_valid l s i).congr rfl rfl rfl
  · exact h

theorem Valid.searchBack {l : FileList} {s : Size} (h : l.Valid s) : (l.searchBack s).1.Valid s := by
  unfold FileList.searchBack
  split
  · exact h
  · dsimp only
    split
    · next _ i _ => exact (focusItem_valid l s i).congr rfl rfl rfl
    · exact h.congr rfl rfl rfl

/-- Adjusting the view to a size makes the list valid for that size. -/
theorem adjust_valid (l : FileList) (s : Size) : (l.adjust s).Valid s :=
  (focusItem_valid l s l.focused).congr rfl rfl rfl

/-- **After every key press the focused entry is in the list and on screen**, whatever
state the list was in (it may have been resized since). -/
theorem valid_handleKey (l : FileList) (s : Size) (k : KeyEvent) : (l.handleKey s k).1.Valid s := by
  have h := adjust_valid l s
  unfold FileList.handleKey
  generalize l.adjust s = l at h
  dsimp only
  split
  · exact h
  · split <;> first
      | exact focusItem_valid ..
      | exact h.searchBack
      | (split <;> exact h)
      | (split
         · exact h.typeAhead _
         · exact h)

/-- **After every mouse event the focused entry is in the list and on screen.** -/
theorem valid_handleMouse (l : FileList) (s : Size) (m : MouseEvent) :
    (l.handleMouse s m).1.Valid s := by
  have h := adjust_valid l s
  unfold FileList.handleMouse
  generalize l.adjust s = l at h
  dsimp only
  split
  · exact focusItem_valid ..
  · exact focusItem_valid ..
  · split
    · split
      · exact h.congr rfl rfl rfl
      · exact Valid.congr (focusItem_valid l s _) rfl rfl rfl
    · split
      · split <;> exact focusItem_valid ..
      · exact h
  · split
    · exact focusItem_valid ..
    · exact h
    · split <;> (try split) <;> (try split) <;> (try split) <;> exact focusItem_valid ..
  · exact h.congr rfl rfl rfl
  · exact h

/-- A freshly loaded directory is valid. -/
theorem valid_load (l : FileList) (s : Size) (dir wildcard : String) (es : Array FileEntry) :
    (l.load dir wildcard es).Valid s := by
  have hr := rows_pos s
  refine ⟨?_, ?_, ?_⟩ <;> simp only [load, page, columns] <;> omega

end FileList

/-! ## The information pane -/

namespace Window

variable {α : Type}

/-- **The information pane describes the focused entry.** After file list `i` changes,
every information pane of the window shows that list's directory, wildcard and focused
entry. -/
theorem changed_info {w : Window α} {i : Nat} {c : Control α} {l : FileList}
    (hc : w.controls[i]? = some c) (hk : c.kind = .fileList l) :
    ∀ c' ∈ (w.changed i).controls, ∀ inf, c'.kind = .fileInfo inf → inf = l.info := by
  obtain ⟨name, b, g, k⟩ := c
  simp only at hk
  subst hk
  intro c' hc' inf hinf
  simp only [Window.changed, hc, Array.mem_mapIdx] at hc'
  obtain ⟨j, hj, rfl⟩ := hc'
  generalize w.controls[j] = c₀ at hinf
  obtain ⟨n₀, b₀, g₀, k₀⟩ := c₀
  cases k₀ <;> simp_all
  split at hinf <;> simp_all

end Window

end HyperVision
