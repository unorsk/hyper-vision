import HyperVision.Event

/-!
# Terminal input decoding

Turns raw bytes from the terminal into `Event`s: UTF-8 text, control keys,
CSI/SS3 escape sequences (xterm style) and SGR mouse reports.

Decoding is total: every step consumes at least one byte, which is what the
termination proof of `decodeFrom` relies on.
-/

namespace HyperVision.Input

/-- The outcome of decoding one event at position `i`. -/
inductive Step (i : Nat) where
  /-- The buffer ends inside an escape or UTF-8 sequence; wait for more bytes. -/
  | incomplete
  /-- Input was consumed up to (exclusive) `j`, optionally producing an event. -/
  | done (ev : Option Event) (j : Nat) (h : i < j)

/-- Consumes through `j` (at least one byte). -/
def Step.advance {i : Nat} (ev : Option Event) (j : Nat) : Step i :=
  .done ev (max (i + 1) j) (Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_max_left _ _))

private def key (k : Key) (mods : Modifiers := {}) : Option Event := some (.key ⟨k, mods⟩)

/-- xterm modifier parameter: `1 + (shift | alt << 1 | ctrl << 2 | meta << 3)`. -/
private def modsOfParam (p : Nat) : Modifiers :=
  let m := p - 1
  { shift := m &&& 1 != 0, alt := m &&& 2 != 0 || m &&& 8 != 0, ctrl := m &&& 4 != 0 }

/-- Decodes a single (non-escape) byte or UTF-8 sequence at `i`. -/
private def decodeText (bs : ByteArray) (i : Nat) (flush : Bool) :
    Option (Option Event × Nat) :=
  match bs[i]? with
  | none => none
  | some b =>
    if b == 13 || b == 10 then some (key .enter, 1)
    else if b == 9 then some (key .tab, 1)
    else if b == 127 || b == 8 then some (key .backspace, 1)
    else if b == 0 then some (key (.char ' ') { ctrl := true }, 1)
    else if b < 27 then
      some (key (.char (Char.ofNat (b.toNat + 96))) { ctrl := true }, 1)
    else if b < 32 then some (none, 1)
    else if b < 128 then some (key (.char (Char.ofNat b.toNat)), 1)
    else
      let n := if b &&& 0xE0 == 0xC0 then 2 else if b &&& 0xF0 == 0xE0 then 3
        else if b &&& 0xF8 == 0xF0 then 4 else 1
      if n == 1 then some (none, 1)
      else if i + n > bs.size then (if flush then some (none, bs.size - i) else none)
      else
        let lead := (b &&& (0xFF >>> (n + 1).toUInt8)).toNat
        let cp := (List.range (n - 1)).foldl
          (fun acc k => acc * 64 + ((bs[i + 1 + k]?.getD 0) &&& 0x3F).toNat) lead
        some (key (.char (Char.ofNat cp)), n)

private def parseParams (s : String) : Array Nat :=
  (s.splitOn ";").toArray.map fun p => p.toNat?.getD 1

private def csiKey (params : Array Nat) (final : Char) : Option Event :=
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
private def sgrMouse (params : Array Nat) (final : Char) : Option Event :=
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

/-- Scans a CSI sequence whose parameters start at `start`; returns the final byte index. -/
private def findFinal (bs : ByteArray) (start : Nat) : Option Nat :=
  (List.range (bs.size - start)).findSome? fun k =>
    let b := bs[start + k]?.getD 0
    if 0x40 ≤ b && b ≤ 0x7E then some (start + k) else none

private def bytesToString (bs : ByteArray) (lo hi : Nat) : String :=
  String.ofList ((bs.extract lo hi).toList.map fun b => Char.ofNat b.toNat)

private def ss3Key (b : UInt8) : Option Event :=
  match Char.ofNat b.toNat with
  | 'P' => key (.f 1) | 'Q' => key (.f 2) | 'R' => key (.f 3) | 'S' => key (.f 4)
  | 'A' => key .up | 'B' => key .down | 'C' => key .right | 'D' => key .left
  | 'H' => key .home | 'F' => key .end
  | _ => none

private def withAlt : Option Event → Option Event
  | some (.key k) => some (.key { k with mods := { k.mods with alt := true } })
  | ev => ev

/-- Decodes one event starting at `i`. With `flush`, a pending lone ESC is a key press. -/
def step (bs : ByteArray) (flush : Bool) (i : Nat) (h : i < bs.size) : Step i :=
  if bs[i] != 0x1b then
    match decodeText bs i flush with
    | some (ev, n) => .advance ev (i + n)
    | none => .incomplete
  else match bs[i + 1]? with
    | none => if flush then .advance (key .escape) (i + 1) else .incomplete
    | some 0x5b => -- '['
      -- The Linux console sends F1‥F5 as `ESC [ [ A`‥`E`.
      if bs[i + 2]? == some 0x5b then
        match bs[i + 3]? with
        | some b =>
          let ev := if 0x41 ≤ b && b ≤ 0x45 then key (.f (b - 0x40).toNat) else none
          .advance ev (i + 4)
        | none => if flush then .advance none bs.size else .incomplete
      else
      match findFinal bs (i + 2) with
      | none => if flush then .advance none bs.size else .incomplete
      | some j =>
        let final := Char.ofNat (bs[j]?.getD 0).toNat
        let raw := bytesToString bs (i + 2) j
        let ev :=
          if raw.startsWith "<" then sgrMouse (parseParams (String.ofList raw.toList.tail)) final
          else csiKey (parseParams raw) final
        .advance ev (j + 1)
    | some 0x4f => -- 'O'
      match bs[i + 2]? with
      | some b => .advance (ss3Key b) (i + 3)
      | none => if flush then .advance (key (.char 'O') { alt := true }) (i + 2) else .incomplete
    | some 0x1b => .advance (key .escape) (i + 1)
    | some _ =>
      match decodeText bs (i + 1) flush with
      | some (ev, n) => .advance (withAlt ev) (i + 1 + n)
      | none => .incomplete

/-- Decodes events from position `i`; returns them with the index of the first unconsumed byte. -/
def decodeFrom (bs : ByteArray) (flush : Bool) (i : Nat) (acc : Array Event) :
    Array Event × Nat :=
  if h : i < bs.size then
    match step bs flush i h with
    | .incomplete => (acc, i)
    | .done ev j _ => decodeFrom bs flush j (acc ++ ev.toArray)
  else (acc, i)
termination_by bs.size - i

/--
Decodes a byte buffer. Returns the events and the unconsumed tail, which should be
prepended to the next read. With `flush`, incomplete sequences are resolved eagerly.
-/
def decode (bytes : ByteArray) (flush : Bool := false) : Array Event × ByteArray :=
  let (evs, j) := decodeFrom bytes flush 0 #[]
  (evs, bytes.extract j bytes.size)

end HyperVision.Input
