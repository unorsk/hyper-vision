import HyperVision.Input

/-!
# Input decoding: correctness theorems

* Decoding is **prefix-stable**: once a prefix of the input decodes to an event,
  more input arriving later cannot change that event.
* Decoding is **independent of how the input is split into reads**: feeding the
  bytes in arbitrary chunks, keeping undecoded bytes for the next read (as the
  application loop does), yields exactly the events of decoding everything at once.
* Printable ASCII bytes decode to the characters they encode.
-/

namespace HyperVision.Input

theorem splitFinal_append {x y ps r : List UInt8} {f : UInt8} (h : splitFinal x = some (ps, f, r)) :
    splitFinal (x ++ y) = some (ps, f, r ++ y) := by
  induction x generalizing ps with
  | nil => simp [splitFinal] at h
  | cons b rest ih =>
    simp only [splitFinal, List.cons_append] at h ⊢
    split at h
    · next hb =>
      simp only [hb, ite_true]
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    · next hb =>
      simp only [hb, ite_false, Bool.false_eq_true]
      obtain ⟨⟨ps', f', r'⟩, h', heq⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [ih h']
      rfl

theorem utf8Char_append {b : UInt8} {rest y r : List UInt8} {ev : Option Event}
    (h : utf8Char false b rest = some (ev, r)) : utf8Char false b (rest ++ y) = some (ev, r ++ y) := by
  simp only [utf8Char] at h ⊢
  split at h
  · next hn =>
    simp only [hn, ite_true]
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · next hn =>
    simp only [hn, ite_false, Bool.false_eq_true]
    split at h
    · simp at h
    · next hlen =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hle : utf8Length b - 1 ≤ rest.length := by omega
      simp only [List.length_append, show ¬ (rest.length + y.length < utf8Length b - 1) by omega,
        decide_false, ite_false, List.take_append_of_le_length hle, List.drop_append_of_le_length hle]

theorem decodeText_append {x y r : List UInt8} {ev : Option Event}
    (h : decodeText false x = some (ev, r)) : decodeText false (x ++ y) = some (ev, r ++ y) := by
  cases x with
  | nil => simp [decodeText] at h
  | cons b rest =>
    simp only [decodeText, List.cons_append] at h ⊢
    split at h
    · next e he =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    · next he =>
      exact utf8Char_append h

/-- **Prefix stability.** An event decoded from `x` is decoded the same way from `x ++ y`. -/
theorem step_append {x y r : List UInt8} {ev : Option Event} (h : step false x = some (ev, r)) :
    step false (x ++ y) = some (ev, r ++ y) := by
  cases x with
  | nil => simp [step] at h
  | cons b rest =>
    simp only [step, List.cons_append] at h ⊢
    split at h
    · next hb =>
      simp only [hb, ite_true]
      cases rest with
      | nil => simp [escape] at h
      | cons c r₁ =>
        simp only [escape, List.cons_append] at h ⊢
        split at h
        · next hc =>
          simp only [hc, ite_true]
          cases r₁ with
          | nil => simp [csiOrLinux] at h
          | cons d r₂ =>
            simp only [csiOrLinux, List.cons_append] at h ⊢
            split at h
            · next hd =>
              simp only [hd, ite_true]
              cases r₂ with
              | nil => simp [linuxSeq] at h
              | cons e r₃ =>
                simp only [linuxSeq, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                rfl
            · next hd =>
              simp only [hd, ite_false, Bool.false_eq_true]
              simp only [csi] at h ⊢
              split at h
              · next ps f r' hs =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                rw [← List.cons_append, splitFinal_append hs]
              · simp at h
        · next hc =>
          simp only [hc, ite_false, Bool.false_eq_true]
          split at h
          · next ho =>
            simp only [ho, ite_true]
            cases r₁ with
            | nil => simp [ss3] at h
            | cons d r₂ =>
              simp only [ss3, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rfl
          · next ho =>
            simp only [ho, ite_false, Bool.false_eq_true]
            split at h
            · next he =>
              simp only [he, ite_true]
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rfl
            · next he =>
              simp only [he, ite_false, Bool.false_eq_true]
              obtain ⟨⟨ev', r'⟩, h', heq⟩ := Option.map_eq_some_iff.1 h
              simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              rw [← List.cons_append, decodeText_append h']
              rfl
    · next hb =>
      simp only [hb, ite_false, Bool.false_eq_true]
      rw [← List.cons_append, decodeText_append h]

theorem decodeList_of_none {flush : Bool} {bs : List UInt8} (h : step flush bs = none) :
    decodeList flush bs = ([], bs) := by
  rw [decodeList]
  split
  · rfl
  · next heq => rw [h] at heq; cases heq

theorem decodeList_of_some {flush : Bool} {bs r : List UInt8} {ev : Option Event}
    (h : step flush bs = some (ev, r)) :
    decodeList flush bs = (ev.toList ++ (decodeList flush r).1, (decodeList flush r).2) := by
  rw [decodeList]
  split
  · next heq => rw [h] at heq; cases heq
  · next ev' r' heq =>
    rw [h] at heq
    simp only [Option.some.injEq, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rfl

/-- **Decoding is independent of read boundaries**: decoding `x ++ y` is decoding `x`,
then decoding its undecoded rest followed by `y`. -/
theorem decodeList_append (x y : List UInt8) :
    decodeList false (x ++ y) =
      ((decodeList false x).1 ++ (decodeList false ((decodeList false x).2 ++ y)).1,
       (decodeList false ((decodeList false x).2 ++ y)).2) := by
  induction h : x.length using Nat.strongRecOn generalizing x with
  | _ n ih =>
    cases hs : step false x with
    | none =>
      rw [decodeList_of_none hs]
      simp
    | some p =>
      obtain ⟨ev, r⟩ := p
      have hlen := step_length hs
      rw [decodeList_of_some hs, decodeList_of_some (step_append hs), ih r.length (h ▸ hlen) r rfl]
      simp

/-- One iteration of the application's read loop: decode what is pending plus the new
bytes, and keep the undecoded rest for the next read. -/
def feed (st : List Event × List UInt8) (chunk : List UInt8) : List Event × List UInt8 :=
  ((st.1 ++ (decodeList false (st.2 ++ chunk)).1), (decodeList false (st.2 ++ chunk)).2)

/-- Decoding stops exactly where no further event can be decoded. -/
theorem step_decodeList_snd (flush : Bool) (bs : List UInt8) :
    step flush (decodeList flush bs).2 = none := by
  induction h : bs.length using Nat.strongRecOn generalizing bs with
  | _ n ih =>
    cases hs : step flush bs with
    | none => rw [decodeList_of_none hs]; exact hs
    | some p =>
      obtain ⟨ev, r⟩ := p
      rw [decodeList_of_some hs]
      exact ih r.length (h ▸ step_length hs) r rfl

/-- **Feeding input in chunks yields exactly the events of decoding it all at once**
(and leaves the same undecoded rest), however the bytes are split. -/
theorem feed_chunks (chunks : List (List UInt8)) :
    chunks.foldl feed ([], []) = decodeList false chunks.flatten := by
  suffices ∀ (evs : List Event) (pending : List UInt8), step false pending = none →
      chunks.foldl feed (evs, pending) =
        (evs ++ (decodeList false (pending ++ chunks.flatten)).1,
         (decodeList false (pending ++ chunks.flatten)).2) by
    simpa using this [] [] rfl
  induction chunks with
  | nil =>
    intro evs pending hp
    simp [decodeList_of_none hp]
  | cons c cs ih =>
    intro evs pending _
    rw [List.foldl_cons, feed, ih _ _ (step_decodeList_snd false _), List.flatten_cons,
      ← List.append_assoc, decodeList_append (pending ++ c)]
    simp

/-- Every printable ASCII byte (checked exhaustively by the kernel). -/
theorem asciiEvent?_printable : ∀ n : Fin 256, 32 ≤ n.val → n.val < 127 →
    asciiEvent? (UInt8.ofNat n.val) = some (key (.char (Char.ofNat n.val))) := by
  decide +kernel

/-- Printable ASCII decodes to the character it encodes. -/
theorem decodeList_printable (b : UInt8) (h₁ : 32 ≤ b.toNat) (h₂ : b.toNat < 127) :
    decodeList false [b] = ([.key ⟨.char (Char.ofNat b.toNat), {}⟩], []) := by
  have ha : asciiEvent? b = some (key (.char (Char.ofNat b.toNat))) := by
    have := asciiEvent?_printable ⟨b.toNat, b.toNat_lt⟩ h₁ h₂
    simpa using this
  have hne : (b == 0x1b) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; subst h; simp at h₁
  have hstep : step false [b] = some (key (.char (Char.ofNat b.toNat)), []) := by
    simp [step, hne, decodeText, ha]
  rw [decodeList_of_some hstep, decodeList_of_none (by rfl)]
  rfl

end HyperVision.Input
