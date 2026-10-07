import HyperVision.Control

/-!
# Text views: correctness theorems

* **The cache is faithful.** A view caches its wrapped lines; whatever the handlers do,
  the cache only ever holds the wrapping of the view's own paragraphs, so the cached
  and the freshly wrapped text agree.
* **Scrolling stays in the text.** After every key press and mouse event the first
  visible line is at most `maxTop`, so the view never scrolls past the end — even when
  a resize had left it there before the event (`draw` clamps the same way).
* **Links are real.** The target reported for an activated link is one of the
  document's link targets.
-/

namespace HyperVision

namespace TextView

/-- The cache holds the wrapping of the paragraphs, at the width it records. -/
def CacheOk (v : TextView) : Prop := ∀ w ls, v.wrapped = some (w, ls) → ls = wrapParas v.paras w

/-- The invariant at size `s`: a faithful cache and a scroll position inside the text. -/
def Valid (v : TextView) (s : Size) : Prop := v.CacheOk ∧ v.top ≤ v.maxTop s

theorem lines_eq {v : TextView} (h : v.CacheOk) (s : Size) :
    v.lines s = wrapParas v.paras (v.textWidth s) := by
  unfold lines
  split
  · next w ls hw =>
    split
    · next he => rw [h w ls hw, (beq_iff_eq.1 he)]
    · rfl
  · rfl

@[simp] theorem paras_layout (v : TextView) (s : Size) : (v.layout s).paras = v.paras := by
  unfold layout; split <;> (try split) <;> rfl

@[simp] theorem top_layout (v : TextView) (s : Size) : (v.layout s).top = v.top := by
  unfold layout; split <;> (try split) <;> rfl

@[simp] theorem scrollBar_layout (v : TextView) (s : Size) : (v.layout s).scrollBar = v.scrollBar := by
  unfold layout; split <;> (try split) <;> rfl

theorem textWidth_layout (v : TextView) (s s' : Size) : (v.layout s).textWidth s' = v.textWidth s' := by
  simp [textWidth]

theorem CacheOk.layout {v : TextView} (h : v.CacheOk) (s : Size) : (v.layout s).CacheOk := by
  intro w ls hw
  unfold TextView.layout at hw
  split at hw
  · split at hw
    · exact paras_layout v s ▸ h w ls (by simpa using hw)
    · simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simp [lines_eq h]
  · simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    simp [lines_eq h]

theorem lines_layout {v : TextView} (h : v.CacheOk) (s s' : Size) : (v.layout s).lines s' = v.lines s' := by
  rw [lines_eq (h.layout s), lines_eq h, paras_layout, textWidth_layout]

theorem maxTop_layout {v : TextView} (h : v.CacheOk) (s s' : Size) :
    (v.layout s).maxTop s' = v.maxTop s' := by
  simp only [maxTop, lines_layout h]

theorem Valid.layout {v : TextView} {s : Size} (h : v.Valid s) (s' : Size) : (v.layout s').Valid s :=
  ⟨h.1.layout s', by rw [top_layout, maxTop_layout h.1]; exact h.2⟩

theorem valid_adjust {v : TextView} (h : v.CacheOk) (s : Size) : (v.adjust s).Valid s := by
  have hl := h.layout s
  unfold TextView.adjust
  dsimp only
  split
  · refine ⟨fun w ls hw => hl w ls hw, ?_⟩
    simp only [maxTop]
    exact Nat.le_refl _
  · next hle =>
    refine ⟨hl, ?_⟩
    simp only [maxTop] at hle ⊢
    omega

/-! ### Scrolling -/

theorem top_scrollTo_le (v : TextView) (s : Size) (t : Int) : (v.scrollTo s t).top ≤ v.maxTop s := by
  unfold scrollTo clampInt
  dsimp only
  omega

theorem CacheOk.scrollTo {v : TextView} (h : v.CacheOk) (s : Size) (t : Int) : (v.scrollTo s t).CacheOk :=
  fun w ls hw => h w ls hw

theorem maxTop_scrollTo (v : TextView) (s s' : Size) (t : Int) : (v.scrollTo s t).maxTop s' = v.maxTop s' := rfl

theorem valid_scrollTo {v : TextView} (h : v.CacheOk) (s : Size) (t : Int) : (v.scrollTo s t).Valid s :=
  ⟨h.scrollTo s t, by rw [maxTop_scrollTo]; exact top_scrollTo_le v s t⟩

theorem valid_scrollToPara {v : TextView} (h : v.CacheOk) (s : Size) (i : Nat) :
    (v.scrollToPara s i).Valid s := by
  have hl := h.layout s
  unfold scrollToPara
  exact valid_scrollTo hl s _

/-- Changing only the highlighted link or the mouse state keeps the invariant. -/
theorem Valid.withLink {v : TextView} {s : Size} (h : v.Valid s) (l : Option Nat) :
    ({ v with link := l } : TextView).Valid s := ⟨fun w ls hw => h.1 w ls hw, h.2⟩

theorem Valid.withGrab {v : TextView} {s : Size} (h : v.Valid s) (g : Option Bool) :
    ({ v with scrollGrab := g } : TextView).Valid s := ⟨fun w ls hw => h.1 w ls hw, h.2⟩

theorem Valid.focusLink {v : TextView} {s : Size} (h : v.Valid s) (i : Nat) : (v.focusLink s i).Valid s := by
  unfold TextView.focusLink
  split
  · dsimp only
    split
    · exact valid_scrollTo (h.withLink _).1 s _
    · split
      · exact valid_scrollTo (h.withLink _).1 s _
      · exact h.withLink _
  · exact h

theorem Valid.stepLink {v : TextView} {s : Size} (h : v.Valid s) (forward : Bool) :
    (v.stepLink s forward).Valid s := by
  have hm : ∀ o : Option Nat, (match o with | some i => v.focusLink s i | none => v).Valid s := by
    intro o; cases o
    · exact h
    · exact h.focusLink _
  unfold TextView.stepLink
  dsimp only
  split
  · exact h
  · exact hm _

/-- **Scrolling stays in the text** under every key press. -/
theorem Valid.handleKey {v : TextView} (h : v.CacheOk) (s : Size) (k : KeyEvent) :
    (v.handleKey s k).1.Valid s := by
  have h' := valid_adjust h s
  unfold TextView.handleKey
  dsimp only
  split
  · exact h'
  · split <;> first
      | exact valid_scrollTo h'.1 s _
      | exact h'.stepLink _
      | (split <;> exact h')
      | exact h'

/-- **Scrolling stays in the text** under every mouse event. -/
theorem Valid.handleMouse {v : TextView} (h : v.CacheOk) (s : Size) (m : MouseEvent) :
    (v.handleMouse s m).1.Valid s := by
  have h' := valid_adjust h s
  unfold TextView.handleMouse
  dsimp only
  split
  · exact valid_scrollTo h'.1 s _
  · exact valid_scrollTo h'.1 s _
  · split
    · split
      · exact h'.withGrab _
      · exact (valid_scrollTo h'.1 s _).withGrab _
    · split
      · exact h'.withLink _
      · exact h'
  · split
    · exact valid_scrollTo h'.1 s _
    · exact h'
  · exact h'.withGrab _
  · exact h'

/-- A new text starts out valid. -/
theorem valid_setParas (v : TextView) (s : Size) (ps : Array TextPara) : (v.setParas ps).Valid s :=
  ⟨fun _ _ hw => by simp [setParas] at hw, by simp [setParas]⟩

/-- Appending text leaves a faithful cache, which is all the handlers need: the next
event (or `draw`) starts from the adjusted view (`Valid.handleKey`). -/
theorem cacheOk_appendParas (v : TextView) (ps : Array TextPara) : (v.appendParas ps).CacheOk :=
  fun _ _ hw => by simp [appendParas] at hw

theorem cacheOk_setParas (v : TextView) (ps : Array TextPara) : (v.setParas ps).CacheOk :=
  fun _ _ hw => by simp [setParas] at hw

/-! ### Links -/

/-- **Links are real**: a reported target is one of the document's link targets. -/
theorem linkTarget?_mem {v : TextView} {t : String} (h : v.linkTarget? = some t) :
    t ∈ TextPara.linkTargets v.paras := by
  unfold linkTarget? at h
  obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.1 h
  exact Array.mem_of_getElem? hi

end TextView

end HyperVision
