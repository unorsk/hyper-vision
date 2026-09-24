import HyperVision.Desktop

/-!
# Window management: correctness theorems

* `Desktop.WF` — window ids are distinct and below `nextId` — is preserved by every
  desktop operation.
* Inserting or raising a window makes it the active (front) window; closing removes
  exactly the windows with that id.
* `next` and `prev` (F6 / Shift-F6) are inverse to each other.
* **No window can be lost**: every operation (inserting, moving, resizing, zooming,
  tiling, cascading, restacking, closing) keeps some cell of every title bar on the
  desktop, so every window can always be grabbed again; resizing the desktop
  re-establishes this for all windows.
* Resizing respects the minimum size and the desktop size; zooming twice restores
  the original bounds.
-/

namespace HyperVision

namespace Window

variable {α : Type}

@[simp] theorem id_setFocus (w : Window α) (i : Nat) : (w.setFocus i).id = w.id := by
  unfold setFocus; split <;> rfl

@[simp] theorem id_initFocus (w : Window α) : w.initFocus.id = w.id := by
  unfold initFocus; split
  · rfl
  · split <;> simp

@[simp] theorem bounds_setFocus (w : Window α) (i : Nat) : (w.setFocus i).bounds = w.bounds := by
  unfold setFocus; split <;> rfl

@[simp] theorem bounds_initFocus (w : Window α) : w.initFocus.bounds = w.bounds := by
  unfold initFocus; split
  · rfl
  · split <;> simp

@[simp] theorem id_setBounds (w : Window α) (r : Rect) : (w.setBounds r).id = w.id := rfl

@[simp] theorem bounds_setBounds (w : Window α) (r : Rect) : (w.setBounds r).bounds = r := rfl

end Window

namespace Desktop

variable {α : Type}

/-- The ids of the windows, back to front. -/
def ids (d : Desktop α) : List Nat := d.windows.toList.map (·.id)

/-- A well-formed desktop: window ids are distinct and all below `nextId`. -/
structure WF (d : Desktop α) : Prop where
  nodup : d.ids.Nodup
  lt : ∀ i ∈ d.ids, i < d.nextId

theorem mem_ids {d : Desktop α} {w : Window α} (h : w ∈ d.windows) : w.id ∈ d.ids := by
  unfold ids
  exact List.mem_map.2 ⟨w, Array.mem_toList_iff.2 h, rfl⟩

/-- An empty desktop is well formed. -/
theorem WF.empty (r : Rect) : WF ({ bounds := r } : Desktop α) := ⟨by simp [ids], by simp [ids]⟩

/-! ### Modifying one window -/

private theorem map_modify {β γ : Type} (l : List β) (j : Nat) (f : β → β) (g : β → γ)
    (hf : ∀ b, g (f b) = g b) : (l.modify j f).map g = l.map g := by
  apply List.ext_getElem?
  intro k
  simp only [List.getElem?_map, List.getElem?_modify]
  split <;> cases l[k]? <;> simp [hf]

theorem ids_modify (d : Desktop α) (i : Nat) (f : Window α → Window α)
    (hf : ∀ w, (f w).id = w.id) : (d.modify i f).ids = d.ids := by
  unfold modify
  split
  · simp only [ids, Array.toList_modify]
    exact map_modify _ _ _ _ hf
  · rfl

@[simp] theorem nextId_modify (d : Desktop α) (i : Nat) (f : Window α → Window α) :
    (d.modify i f).nextId = d.nextId := by
  unfold modify; split <;> rfl

@[simp] theorem bounds_modify (d : Desktop α) (i : Nat) (f : Window α → Window α) :
    (d.modify i f).bounds = d.bounds := by
  unfold modify; split <;> rfl

theorem WF.modify {d : Desktop α} (h : d.WF) (i : Nat) {f : Window α → Window α}
    (hf : ∀ w, (f w).id = w.id) : (d.modify i f).WF := by
  refine ⟨?_, ?_⟩
  · rw [ids_modify d i f hf]; exact h.nodup
  · rw [ids_modify d i f hf, nextId_modify]; exact h.lt

/--
In a well-formed desktop, a window with id `i` after `modify i f` is `f` applied to
the window that had id `i`.
-/
theorem mem_modify {d : Desktop α} (h : d.WF) {i : Nat} {f : Window α → Window α} {w : Window α} (hw : w ∈ (d.modify i f).windows)
    (hid : w.id = i) : ∃ w₀ ∈ d.windows, w₀.id = i ∧ w = f w₀ := by
  unfold modify at hw
  split at hw
  · next j hj =>
    obtain ⟨hjlt, hjid, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hj
    simp only [beq_iff_eq] at hjid
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hw
    rw [Array.getElem_modify] at hid ⊢
    by_cases hjk : j = k
    · subst hjk
      simp only [ite_true] at hid ⊢
      exact ⟨_, Array.getElem_mem _, hjid, rfl⟩
    · simp only [hjk, ite_false] at hid ⊢
      -- Two different windows with id `i` would contradict distinct ids.
      exfalso
      have hk' : k < d.windows.size := by simpa using hk
      have hnd := h.nodup
      simp only [ids] at hnd
      exact hjk (hnd.eq_of_getElem_eq (i := j) (j := k) (by simpa using hjlt) (by simpa using hk')
        (by simp [hjid, hid]))
  · next hn =>
    have := Array.findIdx?_eq_none_iff.1 hn w hw
    simp [hid] at this

/-! ### Well-formedness of every operation -/

theorem WF.insert {d : Desktop α} (h : d.WF) (w : Window α) : (d.insert w).WF := by
  refine ⟨?_, ?_⟩
  · simp only [Desktop.insert, Desktop.insert', ids, Array.toList_push, List.map_append, List.map_cons,
      List.map_nil, Window.id_initFocus]
    rw [List.nodup_append]
    refine ⟨h.nodup, (by simp), fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    have := h.lt a ha
    omega
  · simp only [Desktop.insert, Desktop.insert', ids, Array.toList_push, List.map_append,
      List.map_cons, List.map_nil, Window.id_initFocus, List.mem_append, List.mem_singleton]
    rintro i (hi | rfl)
    · have := h.lt i hi; omega
    · omega

theorem ids_close (d : Desktop α) (i : Nat) : (d.close i).ids = d.ids.filter (· != i) := by
  simp [Desktop.close, ids, List.filter_map, Function.comp_def]

theorem WF.close {d : Desktop α} (h : d.WF) (i : Nat) : (d.close i).WF := by
  refine ⟨?_, ?_⟩
  · rw [ids_close]; exact h.nodup.sublist (List.filter_sublist)
  · rw [ids_close]; exact fun j hj => h.lt j (List.mem_filter.1 hj).1

theorem WF.raise {d : Desktop α} (h : d.WF) (i : Nat) : (d.raise i).WF := by
  unfold Desktop.raise
  split
  · next w hw =>
    have hmem := Array.mem_of_find?_eq_some hw
    have hid : w.id = i := by simpa using Array.find?_some hw
    have hids : ({ d with windows := (d.windows.filter (·.id != i)).push w } : Desktop α).ids =
        d.ids.filter (· != i) ++ [i] := by
      simp [ids, List.filter_map, Function.comp_def, hid]
    refine ⟨?_, ?_⟩
    · rw [hids, List.nodup_append]
      refine ⟨h.nodup.sublist List.filter_sublist, (by simp), fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb
      simp only [List.mem_filter, bne_iff_ne, ne_eq] at ha
      exact hb ▸ ha.2
    · rw [hids]
      intro j hj
      simp only [List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact h.lt j (List.mem_filter.1 hj).1
      · exact h.lt _ (hid ▸ mem_ids hmem)
  · exact h

theorem WF.next {d : Desktop α} (h : d.WF) : d.next.WF := by
  unfold Desktop.next
  split
  · exact h
  · split
    · next w hw =>
      have hl : d.windows.toList = w :: d.windows.toList.tail := by
        cases hd : d.windows.toList with
        | nil => simp [← Array.getElem?_toList, hd] at hw
        | cons a l => simp [← Array.getElem?_toList, hd] at hw; simp [hw]
      have hids : ({ d with windows := (d.windows.extract 1 d.windows.size).push w } : Desktop α).ids =
          d.ids.tail ++ [w.id] := by
        simp only [ids, Array.toList_push, Array.toList_extract, List.map_append, List.map_cons,
          List.map_nil]
        rw [hl]
        simp only [List.extract_eq_take_drop, List.drop_one, List.tail_cons]
        rw [List.take_of_length_le (by simp)]
        simp
      have hperm : (d.ids.tail ++ [w.id]).Perm d.ids := by
        have : d.ids = w.id :: d.ids.tail := by simp only [ids]; rw [hl]; simp
        rw [this]
        simp
      exact ⟨hids ▸ h.nodup.perm hperm.symm, fun j hj => h.lt j (hperm.mem_iff.1 (hids ▸ hj))⟩
    · exact h

theorem WF.prev {d : Desktop α} (h : d.WF) : d.prev.WF := by
  unfold Desktop.prev
  split
  · exact h
  · split
    · next w hw =>
      obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.1 hw
      have hd : d.ids = ys.toList.map (·.id) ++ [w.id] := by simp [ids, hys]
      have hids : ({ d with windows := #[w] ++ d.windows.pop } : Desktop α).ids =
          [w.id] ++ ys.toList.map (·.id) := by
        simp [ids, hys]
      have hperm : ([w.id] ++ ys.toList.map (·.id)).Perm d.ids := hd ▸ List.perm_append_comm
      exact ⟨hids ▸ h.nodup.perm hperm.symm, fun j hj => h.lt j (hperm.mem_iff.1 (hids ▸ hj))⟩
    · exact h

theorem WF.moveTo {d : Desktop α} (h : d.WF) (i : Nat) (p : Point) : (d.moveTo i p).WF :=
  h.modify i fun _ => rfl

theorem WF.resizeTo {d : Desktop α} (h : d.WF) (i : Nat) (s : Size) : (d.resizeTo i s).WF :=
  h.modify i fun _ => rfl

theorem WF.toggleZoom {d : Desktop α} (h : d.WF) (i : Nat) : (d.toggleZoom i).WF := by
  refine h.modify i fun w => ?_
  split
  · rfl
  · split
    · cases w.zoomRect <;> rfl
    · rfl

theorem WF.selectNumber {d : Desktop α} (h : d.WF) (n : Nat) : (d.selectNumber n).WF := by
  unfold Desktop.selectNumber
  split
  · exact h
  · split
    · exact h.raise _
    · exact h

theorem WF.arrange {d : Desktop α} (h : d.WF) (layout : Array (Window α × Rect)) :
    (d.arrange layout).WF := by
  unfold Desktop.arrange
  split
  · exact h
  · have := Array.foldl_induction (as := layout) (init := d)
      (motive := fun _ d' => d'.ids = d.ids ∧ d'.nextId = d.nextId) ⟨rfl, rfl⟩
      (f := fun d (w, r) => d.locate w.id r) fun i d' ⟨h₁, h₂⟩ => by
        split
        rename_i w r _
        exact ⟨by rw [locate, ids_modify d' w.id (fun x => x.setBounds (d'.place x.minSize r)) fun _ => rfl, h₁],
          by rw [locate, nextId_modify, h₂]⟩
    exact ⟨this.1 ▸ h.nodup, this.1 ▸ this.2 ▸ h.lt⟩

theorem WF.tile {d : Desktop α} (h : d.WF) : d.tile.WF := by
  unfold Desktop.tile
  dsimp only
  split
  · exact h
  · exact h.arrange _

theorem WF.cascade {d : Desktop α} (h : d.WF) : d.cascade.WF := h.arrange _

theorem WF.setBounds {d : Desktop α} (h : d.WF) (r : Rect) : (d.setBounds r).WF := by
  have hids : (d.setBounds r).ids = d.ids := by
    simp only [Desktop.setBounds, ids, Array.toList_map, List.map_map]
    congr 1
    funext w
    simp only [Function.comp_apply]
    split <;> rfl
  exact ⟨hids ▸ h.nodup, hids ▸ h.lt⟩

theorem WF.insertCentered {d : Desktop α} (h : d.WF) (w : Window α) : (d.insertCentered w).WF :=
  h.insert _

/-! ### Stacking -/

/-- A newly inserted window is the front (active) window. -/
theorem insert_top (d : Desktop α) (w : Window α) :
    (d.insert w).top?.map (·.id) = some d.nextId := by
  simp [Desktop.insert, Desktop.insert', top?]

/-- Raising a window makes it the front (active) window. -/
theorem raise_top {d : Desktop α} {i : Nat} {w : Window α} (hw : d.find? i = some w) :
    (d.raise i).top? = some w := by
  simp [Desktop.raise, hw, top?]

/-- After closing `i`, no window with id `i` is left… -/
theorem close_removes (d : Desktop α) (i : Nat) : ∀ w ∈ (d.close i).windows, w.id ≠ i := by
  intro w hw
  have := (Array.mem_filter.1 hw).2
  simpa using this

/-- …and every other window is still there. -/
theorem close_keeps (d : Desktop α) (i : Nat) {w : Window α} (hw : w ∈ d.windows)
    (hne : w.id ≠ i) : w ∈ (d.close i).windows :=
  Array.mem_filter.2 ⟨hw, by simpa using hne⟩

/-- Without modal windows, `prev` (Shift-F6) undoes `next` (F6). -/
theorem prev_next (d : Desktop α) (hm : ∀ w ∈ d.windows, w.modal = false) : d.next.prev = d := by
  have hmod : ∀ d' : Desktop α, (∀ w ∈ d'.windows, w.modal = false) → d'.modalActive = false := by
    intro d' h'
    unfold modalActive top?
    cases hb : d'.windows.back? with
    | none => rfl
    | some w =>
      have := h' w (Array.mem_of_back? hb)
      simp [this]
  unfold Desktop.next
  rw [hmod d hm]
  simp only [Bool.false_eq_true, ite_false]
  cases hw : d.windows[0]? with
  | none =>
    unfold Desktop.prev
    rw [hmod d hm]
    have : d.windows = #[] := by
      rcases d with ⟨ws, n, b⟩
      cases ws using Array.rec with
      | mk l => cases l <;> simp_all
    simp [this]
  | some w =>
    simp only
    have hl : d.windows.toList = w :: d.windows.toList.tail := by
      cases hd : d.windows.toList with
      | nil => simp [← Array.getElem?_toList, hd] at hw
      | cons a l => simp [← Array.getElem?_toList, hd] at hw; simp [hw]
    let d' : Desktop α := { d with windows := (d.windows.extract 1 d.windows.size).push w }
    have hd'm : ∀ w' ∈ d'.windows, w'.modal = false := by
      intro w' hw'
      apply hm
      rcases Array.mem_push.1 hw' with h' | rfl
      · rw [← Array.mem_toList_iff, Array.toList_extract, List.extract_eq_take_drop] at h'
        exact Array.mem_toList_iff.1 (List.mem_of_mem_drop (List.mem_of_mem_take h'))
      · exact Array.mem_of_getElem? hw
    unfold Desktop.prev
    rw [hmod d' hd'm]
    simp only [Bool.false_eq_true, ite_false, Array.back?_push, Array.pop_push]
    rcases d with ⟨ws, n, b⟩
    simp only [Desktop.mk.injEq, and_true]
    apply Array.toList_inj.1
    simp only at hl ⊢
    rw [Array.toList_append, Array.toList_extract, hl]
    simp only [List.extract_eq_take_drop, List.drop_one, List.tail_cons]
    rw [List.take_of_length_le (by simp)]
    simp

/-! ### Moving, resizing, zooming -/

/-- Some cell of the window's title bar (its top row) lies on the desktop `desk`. -/
def TitleReachable (desk : Rect) (w : Window α) : Prop :=
  ∃ x, desk.contains ⟨x, w.bounds.y⟩ ∧ w.bounds.x ≤ x ∧ x < w.bounds.right

/--
**Windows cannot be lost.** However far a window is dragged, part of its title bar
remains on the (non-empty) desktop, so it can always be grabbed again.
-/
theorem moveTo_titleReachable {d : Desktop α} (h : d.WF) (i : Nat) (p : Point)
    (hdw : 0 < d.bounds.w) (hdh : 0 < d.bounds.h) :
    ∀ w ∈ (d.moveTo i p).windows, w.id = i → 0 < w.bounds.w → TitleReachable d.bounds w := by
  intro w hw hid hpos
  obtain ⟨w₀, -, -, rfl⟩ := mem_modify h hw hid
  unfold TitleReachable
  dsimp only at hpos ⊢
  have hq : d.bounds.x - w₀.size.w + 1 ≤ (d.constrain w₀.size p).x ∧
      (d.constrain w₀.size p).x ≤ d.bounds.right - 1 ∧ d.bounds.y ≤ (d.constrain w₀.size p).y ∧
      (d.constrain w₀.size p).y ≤ d.bounds.bottom - 1 := by
    simp only [constrain, clampInt, Rect.right, Rect.bottom, Window.size]
    omega
  generalize d.constrain w₀.size p = q at hq ⊢
  simp only [Window.size, Rect.contains_iff, Rect.right, Rect.bottom] at hq ⊢
  exact ⟨max d.bounds.x q.x, by omega, by omega, by omega⟩

/-- A resized window is at least its minimum size and at most the desktop size. -/
theorem resizeTo_size {d : Desktop α} (h : d.WF) (i : Nat) (s : Size) :
    ∀ w ∈ (d.resizeTo i s).windows, w.id = i →
      w.minSize.w ≤ w.bounds.w ∧ w.minSize.h ≤ w.bounds.h ∧
      (w.minSize.w ≤ d.bounds.w → w.bounds.w ≤ d.bounds.w) ∧
      (w.minSize.h ≤ d.bounds.h → w.bounds.h ≤ d.bounds.h) := by
  intro w hw hid
  obtain ⟨w₀, -, -, rfl⟩ := mem_modify h hw hid
  simp only [Window.setBounds, place]
  omega

/-- Bounds that already respect the size limits and keep part of the title bar on the
desktop are placed unchanged. -/
theorem place_eq_self {d : Desktop α} {m : Size} {r : Rect} (hw : m.w ≤ r.w) (hh : m.h ≤ r.h)
    (hdw : r.w ≤ d.bounds.w) (hdh : r.h ≤ d.bounds.h)
    (hx : d.bounds.x - r.w + 1 ≤ r.x ∧ r.x ≤ d.bounds.right - 1)
    (hy : d.bounds.y ≤ r.y ∧ r.y ≤ d.bounds.bottom - 1) : d.place m r = r := by
  simp only [place, constrain, clampInt, Rect.origin]
  rcases r with ⟨x, y, w, h⟩
  simp only at *
  have e₁ : max m.w (min w d.bounds.w) = w := by omega
  have e₂ : max m.h (min h d.bounds.h) = h := by omega
  rw [e₁, e₂]
  congr 1 <;> omega

/-- Zooming a window that is not maximized, then zooming again, restores its bounds
(when they are valid bounds for it, as those of every window placed by the desktop are). -/
theorem toggleZoom_twice {d : Desktop α} (h : d.WF) {i : Nat} {w₀ : Window α}
    (hw₀ : w₀ ∈ d.windows) (hid : w₀.id = i) (hz : w₀.flags.zoom = true)
    (hmax : w₀.isMaximized d.bounds = false) (hfit : d.place w₀.minSize w₀.bounds = w₀.bounds) :
    ∀ w ∈ ((d.toggleZoom i).toggleZoom i).windows, w.id = i → w.bounds = w₀.bounds := by
  intro w hw hwid
  have h₁ := h.toggleZoom i
  obtain ⟨w₁, hw₁, hid₁, rfl⟩ := mem_modify h₁ hw hwid
  obtain ⟨w₂, hw₂, hid₂, rfl⟩ := mem_modify h hw₁ hid₁
  -- `w₂` is `w₀`: both are the window with id `i`.
  have : w₂ = w₀ := by
    obtain ⟨a, ha, rfl⟩ := Array.mem_iff_getElem.1 hw₂
    obtain ⟨b, hb, rfl⟩ := Array.mem_iff_getElem.1 hw₀
    have hnd := h.nodup
    simp only [ids] at hnd
    have := hnd.eq_of_getElem_eq (i := a) (j := b) (by simpa using ha) (by simpa using hb)
      (by simp [hid₂, hid])
    subst this; rfl
  subst this
  have hb : (d.toggleZoom i).bounds = d.bounds := bounds_modify ..
  simp only [hb, hz, hmax, Bool.not_true, Bool.false_eq_true, ite_false]
  have hp : (d.toggleZoom i).place = d.place := by funext m r; simp only [place, constrain, hb]
  simp [Window.isMaximized, Window.setBounds, hz, hp, hfit]

/-! ### No window can be lost -/

/-- Every window (of positive width) has part of its title bar on the desktop, so it can
always be grabbed with the mouse. -/
def Reachable (d : Desktop α) : Prop :=
  ∀ w ∈ d.windows, 0 < w.bounds.w → TitleReachable d.bounds w

theorem titleReachable_congr {desk : Rect} {w w' : Window α} (hb : w'.bounds = w.bounds) :
    TitleReachable desk w' ↔ TitleReachable desk w := by
  simp only [TitleReachable, hb]

/-- A window whose origin is the `constrain`ed origin for its size is reachable. -/
theorem titleReachable_constrain {d : Desktop α} (hdw : 0 < d.bounds.w) (hdh : 0 < d.bounds.h)
    {w : Window α} {p : Point} (hx : w.bounds.x = (d.constrain ⟨w.bounds.w, w.bounds.h⟩ p).x)
    (hy : w.bounds.y = (d.constrain ⟨w.bounds.w, w.bounds.h⟩ p).y) (hpos : 0 < w.bounds.w) :
    TitleReachable d.bounds w := by
  have hq : d.bounds.x - w.bounds.w + 1 ≤ (d.constrain ⟨w.bounds.w, w.bounds.h⟩ p).x ∧
      (d.constrain ⟨w.bounds.w, w.bounds.h⟩ p).x ≤ d.bounds.right - 1 ∧
      d.bounds.y ≤ (d.constrain ⟨w.bounds.w, w.bounds.h⟩ p).y ∧
      (d.constrain ⟨w.bounds.w, w.bounds.h⟩ p).y ≤ d.bounds.bottom - 1 := by
    simp only [constrain, clampInt, Rect.right, Rect.bottom]
    omega
  rw [← hx, ← hy] at hq
  simp only [TitleReachable, Rect.contains_iff, Rect.right, Rect.bottom] at hq ⊢
  exact ⟨max d.bounds.x w.bounds.x, by omega, by omega, by omega⟩

/-- Bounds chosen by `place` keep part of the title bar on a non-empty desktop. -/
theorem titleReachable_place {d : Desktop α} (hdw : 0 < d.bounds.w) (hdh : 0 < d.bounds.h)
    {w : Window α} {m : Size} {r : Rect} (hb : w.bounds = d.place m r) (hpos : 0 < w.bounds.w) :
    TitleReachable d.bounds w :=
  titleReachable_constrain hdw hdh (p := r.origin) (by rw [hb]; rfl) (by rw [hb]; rfl) hpos

theorem mem_modify_cases {d : Desktop α} {i : Nat} {f : Window α → Window α} {w : Window α}
    (hw : w ∈ (d.modify i f).windows) : w ∈ d.windows ∨ ∃ w₀ ∈ d.windows, w = f w₀ := by
  unfold modify at hw
  split at hw
  · obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hw
    have hk' : k < d.windows.size := by simpa using hk
    rw [Array.getElem_modify]
    split
    · exact .inr ⟨_, Array.getElem_mem hk', rfl⟩
    · exact .inl (Array.getElem_mem hk')
  · exact .inl hw

theorem Reachable.modify {d : Desktop α} (h : d.Reachable) (i : Nat) {f : Window α → Window α}
    (hf : ∀ w ∈ d.windows, 0 < (f w).bounds.w → TitleReachable d.bounds (f w)) :
    (d.modify i f).Reachable := by
  intro w hw hpos
  rw [bounds_modify]
  rcases mem_modify_cases hw with hw | ⟨w₀, hw₀, rfl⟩
  · exact h w hw hpos
  · exact hf w₀ hw₀ hpos

/-- Changing a window without changing its bounds (its controls, focus, flags, …). -/
theorem Reachable.modify_of_bounds {d : Desktop α} (h : d.Reachable) (i : Nat)
    {f : Window α → Window α} (hf : ∀ w, (f w).bounds = w.bounds) : (d.modify i f).Reachable :=
  h.modify i fun w hw hpos => (titleReachable_congr (hf w)).2 (h w hw (hf w ▸ hpos))

theorem Reachable.of_subset {d d' : Desktop α} (h : d.Reachable)
    (hsub : ∀ w ∈ d'.windows, w ∈ d.windows) (hb : d'.bounds = d.bounds) : d'.Reachable :=
  fun w hw hpos => hb ▸ h w (hsub w hw) hpos

theorem Reachable.empty (r : Rect) : Reachable ({ bounds := r } : Desktop α) := by
  intro w hw; simp at hw

theorem Reachable.insert {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) (w : Window α) : (d.insert w).Reachable := by
  intro w' hw' hpos
  simp only [Desktop.insert, Desktop.insert', Array.mem_push] at hw' ⊢
  rcases hw' with hw' | rfl
  · exact h w' hw' hpos
  · exact titleReachable_place hdw hdh (m := w.minSize) (r := w.bounds) (by simp) hpos

theorem Reachable.insertCentered {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) (w : Window α) : (d.insertCentered w).Reachable :=
  h.insert hdw hdh _

theorem Reachable.close {d : Desktop α} (h : d.Reachable) (i : Nat) : (d.close i).Reachable :=
  h.of_subset (fun w hw => by simp only [Desktop.close, Array.mem_filter] at hw; exact hw.1) rfl

theorem Reachable.raise {d : Desktop α} (h : d.Reachable) (i : Nat) : (d.raise i).Reachable := by
  unfold Desktop.raise
  split
  · next w' hw' =>
    refine h.of_subset (fun w hw => ?_) rfl
    rcases Array.mem_push.1 hw with hw | rfl
    · exact (Array.mem_filter.1 hw).1
    · exact Array.mem_of_find?_eq_some hw'
  · exact h

theorem Reachable.next {d : Desktop α} (h : d.Reachable) : d.next.Reachable := by
  unfold Desktop.next
  split
  · exact h
  · split
    · next w' hw' =>
      refine h.of_subset (fun w hw => ?_) rfl
      rcases Array.mem_push.1 hw with hw | rfl
      · rw [← Array.mem_toList_iff, Array.toList_extract, List.extract_eq_take_drop] at hw
        exact Array.mem_toList_iff.1 (List.mem_of_mem_drop (List.mem_of_mem_take hw))
      · exact Array.mem_of_getElem? hw'
    · exact h

theorem Reachable.prev {d : Desktop α} (h : d.Reachable) : d.prev.Reachable := by
  unfold Desktop.prev
  split
  · exact h
  · split
    · next w' hw' =>
      obtain ⟨ys, hys⟩ := Array.back?_eq_some_iff.1 hw'
      refine h.of_subset (fun w hw => ?_) rfl
      simp only [hys, Array.pop_push, Array.mem_append, Array.mem_singleton] at hw
      rw [hys, Array.mem_push]
      exact hw.symm
    · exact h

theorem Reachable.selectNumber {d : Desktop α} (h : d.Reachable) (n : Nat) :
    (d.selectNumber n).Reachable := by
  unfold Desktop.selectNumber
  split
  · exact h
  · split
    · exact h.raise _
    · exact h

theorem Reachable.moveTo {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) (i : Nat) (p : Point) : (d.moveTo i p).Reachable :=
  h.modify i fun _ _ hpos => titleReachable_constrain hdw hdh (p := p) rfl rfl hpos

theorem Reachable.locate {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) (i : Nat) (r : Rect) : (d.locate i r).Reachable :=
  h.modify i fun _ _ hpos => titleReachable_place hdw hdh rfl hpos

theorem Reachable.resizeTo {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) (i : Nat) (s : Size) : (d.resizeTo i s).Reachable :=
  h.modify i fun _ _ hpos => titleReachable_place hdw hdh rfl hpos

theorem Reachable.toggleZoom {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) (i : Nat) : (d.toggleZoom i).Reachable := by
  refine h.modify i fun w hw hpos => ?_
  by_cases hz : w.flags.zoom = true
  · by_cases hm : w.isMaximized d.bounds = true
    · simp only [hz, hm, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at hpos ⊢
      cases hr : w.zoomRect with
      | none =>
        simp only [hr, Option.map_none, Option.getD_none] at hpos ⊢
        exact h w hw hpos
      | some r =>
        simp only [hr, Option.map_some, Option.getD_some] at hpos ⊢
        exact titleReachable_place hdw hdh rfl hpos
    · simp only [hz, hm, Bool.not_true, Bool.false_eq_true, ite_false] at hpos ⊢
      refine ⟨d.bounds.x, ?_, ?_, ?_⟩ <;>
        simp only [Window.setBounds, Rect.contains_iff, Rect.right] <;> omega
  · simp only [hz, Bool.not_false, ite_true] at hpos ⊢
    exact h w hw hpos

theorem Reachable.arrange {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) (layout : Array (Window α × Rect)) : (d.arrange layout).Reachable := by
  unfold Desktop.arrange
  split
  · exact h
  · have := Array.foldl_induction (as := layout) (init := d)
      (motive := fun _ d' => d'.Reachable ∧ d'.bounds = d.bounds) ⟨h, rfl⟩
      (f := fun d (w, r) => d.locate w.id r) fun i d' ⟨h₁, h₂⟩ => by
        split
        rename_i w r _
        exact ⟨h₁.locate (h₂ ▸ hdw) (h₂ ▸ hdh) w.id r, by rw [Desktop.locate, bounds_modify, h₂]⟩
    exact this.1

theorem Reachable.tile {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) : d.tile.Reachable := by
  unfold Desktop.tile
  dsimp only
  split
  · exact h
  · exact h.arrange hdw hdh _

theorem Reachable.cascade {d : Desktop α} (h : d.Reachable) (hdw : 0 < d.bounds.w)
    (hdh : 0 < d.bounds.h) : d.cascade.Reachable :=
  h.arrange hdw hdh _

/-- Resizing the desktop to a non-empty area makes every window reachable, wherever the
windows were before. -/
theorem reachable_setBounds (d : Desktop α) {r : Rect} (hrw : 0 < r.w) (hrh : 0 < r.h) :
    (d.setBounds r).Reachable := by
  intro w hw hpos
  simp only [Desktop.setBounds, Array.mem_map] at hw
  obtain ⟨w₀, -, rfl⟩ := hw
  show TitleReachable r _
  by_cases hm : w₀.isMaximized d.bounds = true
  · simp only [hm, ite_true] at hpos ⊢
    refine ⟨r.x, ?_, ?_, ?_⟩ <;> simp only [Window.setBounds, Rect.contains_iff, Rect.right] <;> omega
  · simp only [hm, Bool.false_eq_true, ite_false] at hpos ⊢
    exact titleReachable_constrain (d := { d with bounds := r }) hrw hrh (p := w₀.bounds.origin)
      rfl rfl hpos

end Desktop

end HyperVision
