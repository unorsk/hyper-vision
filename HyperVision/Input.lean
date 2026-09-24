import HyperVision.Event

/-!
# Terminal input decoding

Turns raw bytes from the terminal into `Event`s: UTF-8 text, control keys,
CSI/SS3 escape sequences (xterm style) and SGR mouse reports.

The decoder works on the byte list: `step` decodes one event from the front of the
input and returns the rest, which is strictly shorter (`step_length`). Bytes that do
not yet form a complete sequence are left for the next read, and decoding does not
depend on how the input is split into reads (`Proofs/Input.lean`).
-/

namespace HyperVision.Input

def key (k : Key) (mods : Modifiers := {}) : Option Event := some (.key ⟨k, mods⟩)

/-- xterm modifier parameter: `1 + (shift | alt << 1 | ctrl << 2 | meta << 3)`. -/
def modsOfParam (p : Nat) : Modifiers :=
  let m := p - 1
  { shift := m &&& 1 != 0, alt := m &&& 2 != 0 || m &&& 8 != 0, ctrl := m &&& 4 != 0 }

/-- The length of a UTF-8 sequence starting with lead byte `b` (1 for invalid leads). -/
def utf8Length (b : UInt8) : Nat :=
  if b &&& 0xE0 == 0xC0 then 2 else if b &&& 0xF0 == 0xE0 then 3
  else if b &&& 0xF8 == 0xF0 then 4 else 1

/-- The event of a single ASCII byte (`none` inside: no event), or `none` for bytes ≥ 128. -/
def asciiEvent? (b : UInt8) : Option (Option Event) :=
  if b == 13 || b == 10 then some (key .enter)
  else if b == 9 then some (key .tab)
  else if b == 127 || b == 8 then some (key .backspace)
  else if b == 0 then some (key (.char ' ') { ctrl := true })
  else if b < 27 then some (key (.char (Char.ofNat (b.toNat + 96))) { ctrl := true })
  else if b < 32 then some none
  else if b < 128 then some (key (.char (Char.ofNat b.toNat)))
  else none

/-- A UTF-8 sequence with lead byte `b` followed by `rest`. -/
def utf8Char (flush : Bool) (b : UInt8) (rest : List UInt8) : Option (Option Event × List UInt8) :=
  let n := utf8Length b
  if n == 1 then some (none, rest)
  else if rest.length < n - 1 then (if flush then some (none, []) else none)
  else
    let lead := (b &&& (0xFF >>> (n + 1).toUInt8)).toNat
    let cp := (rest.take (n - 1)).foldl (fun acc c => acc * 64 + (c &&& 0x3F).toNat) lead
    some (key (.char (Char.ofNat cp)), rest.drop (n - 1))

/--
Decodes a single (non-escape) byte or UTF-8 sequence at the front of the input:
`none` if more bytes are needed, otherwise the event (if any) and the rest.
-/
def decodeText (flush : Bool) : List UInt8 → Option (Option Event × List UInt8)
  | [] => none
  | b :: rest =>
    match asciiEvent? b with
    | some ev => some (ev, rest)
    | none => utf8Char flush b rest

def parseParams (s : String) : Array Nat :=
  (s.splitOn ";").toArray.map fun p => p.toNat?.getD 1

def csiKey (params : Array Nat) (final : Char) : Option Event :=
  let mods := modsOfParam (params[1]?.getD 1)
  match final with
  | 'A' => key .up mods | 'B' => key .down mods
  | 'C' => key .right mods | 'D' => key .left mods
  | 'H' => key .home mods | 'F' => key .end mods
  | 'Z' => key .tab { shift := true }
  | 'P' => key (.f 1) mods | 'Q' => key (.f 2) mods
  | 'R' => key (.f 3) mods | 'S' => key (.f 4) mods
  | '~' =>
    match params[0]?.getD 0 with
    | 1 | 7 => key .home mods | 2 => key .insert mods | 3 => key .delete mods
    | 4 | 8 => key .end mods | 5 => key .pageUp mods | 6 => key .pageDown mods
    | 11 => key (.f 1) mods | 12 => key (.f 2) mods | 13 => key (.f 3) mods
    | 14 => key (.f 4) mods | 15 => key (.f 5) mods | 17 => key (.f 6) mods
    | 18 => key (.f 7) mods | 19 => key (.f 8) mods | 20 => key (.f 9) mods
    | 21 => key (.f 10) mods | 23 => key (.f 11) mods | 24 => key (.f 12) mods
    | _ => none
  | _ => none

/-- Decodes an SGR (`CSI < b ; x ; y M/m`) mouse report. -/
def sgrMouse (params : Array Nat) (final : Char) : Option Event :=
  match params with
  | #[b, x, y] =>
    -- Buttons 8‥11 (back/forward, bit 128) are not supported.
    if b &&& 128 != 0 then none else
    let mods : Modifiers := { shift := b &&& 4 != 0, alt := b &&& 8 != 0, ctrl := b &&& 16 != 0 }
    let pos : Point := ⟨(x : Int) - 1, (y : Int) - 1⟩
    let button := match b &&& 3 with
      | 0 => MouseButton.left | 1 => .middle | 2 => .right | _ => .none
    let action :=
      if b &&& 64 != 0 then (if b &&& 1 == 0 then MouseAction.wheelUp else .wheelDown)
      else if final == 'm' then .release
      else if b &&& 32 != 0 then (if button == .none then .move else .drag)
      else .press
    some (.mouse { pos, button, action, mods })
  | _ => none

/-- Splits a CSI sequence at its final byte (`0x40‥0x7E`): parameters, final byte, rest. -/
def splitFinal : List UInt8 → Option (List UInt8 × UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
    if 0x40 ≤ b && b ≤ 0x7E then some ([], b, rest)
    else (splitFinal rest).map fun (ps, f, r) => (b :: ps, f, r)

def bytesToString (bs : List UInt8) : String :=
  String.ofList (bs.map fun b => Char.ofNat b.toNat)

/-- The event of a CSI sequence with parameter bytes `params` and final byte `final`. -/
def csiEvent (params : List UInt8) (final : UInt8) : Option Event :=
  let raw := bytesToString params
  let f := Char.ofNat final.toNat
  if raw.startsWith "<" then sgrMouse (parseParams (String.ofList raw.toList.tail)) f
  else csiKey (parseParams raw) f

/-- The Linux console's `ESC [ [ A`‥`E` function keys. -/
def linuxFKey (b : UInt8) : Option Event :=
  if 0x41 ≤ b && b ≤ 0x45 then key (.f (b - 0x40).toNat) else none

def ss3Key (b : UInt8) : Option Event :=
  match Char.ofNat b.toNat with
  | 'P' => key (.f 1) | 'Q' => key (.f 2) | 'R' => key (.f 3) | 'S' => key (.f 4)
  | 'A' => key .up | 'B' => key .down | 'C' => key .right | 'D' => key .left
  | 'H' => key .home | 'F' => key .end
  | _ => none

def withAlt : Option Event → Option Event
  | some (.key k) => some (.key { k with mods := { k.mods with alt := true } })
  | ev => ev

/-- The rest of a CSI sequence after `ESC [`. -/
def csi (flush : Bool) (bs : List UInt8) : Option (Option Event × List UInt8) :=
  match splitFinal bs with
  | some (ps, f, r) => some (csiEvent ps f, r)
  | none => if flush then some (none, []) else none

/-- After `ESC [ [`: a Linux console function key. -/
def linuxSeq (flush : Bool) : List UInt8 → Option (Option Event × List UInt8)
  | e :: r => some (linuxFKey e, r)
  | [] => if flush then some (none, []) else none

/-- After `ESC [`. -/
def csiOrLinux (flush : Bool) : List UInt8 → Option (Option Event × List UInt8)
  | d :: r => if d == 0x5b then linuxSeq flush r else csi flush (d :: r)
  | [] => if flush then some (none, []) else none

/-- After `ESC O`. -/
def ss3 (flush : Bool) : List UInt8 → Option (Option Event × List UInt8)
  | d :: r => some (ss3Key d, r)
  | [] => if flush then some (key (.char 'O') { alt := true }, []) else none

/-- After `ESC`. -/
def escape (flush : Bool) : List UInt8 → Option (Option Event × List UInt8)
  | c :: r =>
    if c == 0x5b then csiOrLinux flush r
    else if c == 0x4f then ss3 flush r
    else if c == 0x1b then some (key .escape, c :: r)
    else (decodeText flush (c :: r)).map fun (ev, r') => (withAlt ev, r')
  | [] => if flush then some (key .escape, []) else none

/--
Decodes one event from the front of the input: `none` if the input ends inside a
sequence (with `flush`, such input is consumed instead), otherwise the event (if
any) and the remaining bytes.
-/
def step (flush : Bool) : List UInt8 → Option (Option Event × List UInt8)
  | b :: r => if b == 0x1b then escape flush r else decodeText flush (b :: r)
  | [] => none

/-! ### Termination -/

theorem splitFinal_length {bs ps r : List UInt8} {f : UInt8} (h : splitFinal bs = some (ps, f, r)) :
    r.length < bs.length := by
  induction bs generalizing ps with
  | nil => simp [splitFinal] at h
  | cons b rest ih =>
    simp only [splitFinal] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      simp
    · obtain ⟨⟨ps', f', r'⟩, h', heq⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl, rfl⟩ := heq
      have := ih h'
      simp only [List.length_cons]
      omega

theorem utf8Char_length {flush : Bool} {b : UInt8} {rest r : List UInt8} {ev : Option Event}
    (h : utf8Char flush b rest = some (ev, r)) : r.length ≤ rest.length := by
  simp only [utf8Char] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact Nat.le_refl _
  · split at h
    · split at h <;> simp at h; obtain ⟨-, rfl⟩ := h; simp
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp

theorem decodeText_length {flush : Bool} {bs r : List UInt8} {ev : Option Event}
    (h : decodeText flush bs = some (ev, r)) : r.length < bs.length := by
  cases bs with
  | nil => simp [decodeText] at h
  | cons b rest =>
    simp only [decodeText] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
    · have := utf8Char_length h; simp; omega

/-- Every decoding step consumes at least one byte. -/
theorem step_length {flush : Bool} {bs r : List UInt8} {ev : Option Event}
    (h : step flush bs = some (ev, r)) : r.length < bs.length := by
  have hflush : ∀ {e : Option Event} {bs' : List UInt8},
      (if flush then some (e, ([] : List UInt8)) else none) = some (ev, r) → r.length < bs'.length + 1 := by
    intro e bs' h; split at h <;> simp at h; obtain ⟨-, rfl⟩ := h; simp
  cases bs with
  | nil => simp [step] at h
  | cons b rest =>
    simp only [step] at h
    split at h
    · cases rest with
      | nil => exact hflush (bs' := []) (by simpa [escape] using h)
      | cons c r₁ =>
        simp only [escape] at h
        split at h
        · cases r₁ with
          | nil => have := hflush (bs' := [c]) (by simpa [csiOrLinux] using h); simp at this ⊢; omega
          | cons d r₂ =>
            simp only [csiOrLinux] at h
            split at h
            · cases r₂ with
              | nil => have := hflush (bs' := [c, d]) (by simpa [linuxSeq] using h); simp at this ⊢; omega
              | cons e r₃ =>
                simp only [linuxSeq, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨-, rfl⟩ := h; simp; omega
            · simp only [csi] at h
              split at h
              · next ps f r' hs =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
                have := splitFinal_length hs; simp at this ⊢; omega
              · have := hflush (bs' := c :: d :: r₂) h; simp at this ⊢; omega
        · split at h
          · cases r₁ with
            | nil => have := hflush (bs' := [c]) (by simpa [ss3] using h); simp at this ⊢; omega
            | cons d r₂ =>
              simp only [ss3, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, rfl⟩ := h; simp; omega
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp
            · obtain ⟨⟨ev', r'⟩, h', heq⟩ := Option.map_eq_some_iff.1 h
              simp only [Prod.mk.injEq] at heq
              obtain ⟨-, rfl⟩ := heq
              have := decodeText_length h'
              simp at this ⊢; omega
    · exact decodeText_length h

/-- Decodes as many events as possible; returns them with the undecoded rest. -/
def decodeList (flush : Bool) (bs : List UInt8) : List Event × List UInt8 :=
  match h : step flush bs with
  | none => ([], bs)
  | some (ev, rest) =>
    have := step_length h
    let (evs, left) := decodeList flush rest
    (ev.toList ++ evs, left)
termination_by bs.length

/--
Decodes a byte buffer. Returns the events and the unconsumed tail, which should be
prepended to the next read. With `flush`, incomplete sequences are resolved eagerly.
-/
def decode (bytes : ByteArray) (flush : Bool := false) : Array Event × ByteArray :=
  let (evs, rest) := decodeList flush bytes.toList
  (evs.toArray, ⟨rest.toArray⟩)

end HyperVision.Input
