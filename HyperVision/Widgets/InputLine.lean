import HyperVision.Widget

/-!
# Single-line input

A `TInputLine`: white on blue, horizontal scrolling with `◄`/`►` indicators,
shift-selection and mouse selection. The whole text is selected on focus.
-/

namespace HyperVision

structure InputLine where
  text : Array Char := #[]
  /-- Insertion point, `≤ text.size`. -/
  cursor : Nat := 0
  /-- First visible character. -/
  first : Nat := 0
  /-- Selection anchor; the selection spans the anchor and the cursor. -/
  anchor : Option Nat := none
  maxLength : Nat := 256
deriving Inhabited, Repr

namespace InputLine

def ofString (s : String) (maxLength : Nat := 256) : InputLine :=
  { text := s.toList.toArray, cursor := s.length, maxLength }

def value (i : InputLine) : String := String.ofList i.text.toList

/-- The selected range `[lo, hi)`, if non-empty. -/
def selection? (i : InputLine) : Option (Nat × Nat) :=
  i.anchor.bind fun a =>
    let lo := min a i.cursor
    let hi := max a i.cursor
    if lo < hi then some (lo, hi) else none

def selectAll (i : InputLine) : InputLine := { i with anchor := some 0, cursor := i.text.size }

/-- Scrolls so the cursor is visible in a field `width` cells wide. -/
def adjust (i : InputLine) (width : Nat) : InputLine :=
  let vis := max 1 (width - 2)
  let cursor := min i.cursor i.text.size
  let first :=
    if cursor < i.first then cursor
    else if cursor ≥ i.first + vis then cursor + 1 - vis
    else i.first
  { i with cursor, first := min first i.text.size }

def deleteRange (i : InputLine) (lo hi : Nat) : InputLine :=
  { i with text := i.text.extract 0 lo ++ i.text.extract hi i.text.size, cursor := lo,
           anchor := none }

def deleteSelection (i : InputLine) : InputLine :=
  match i.selection? with
  | some (lo, hi) => i.deleteRange lo hi
  | none => { i with anchor := none }

def insert (i : InputLine) (c : Char) : InputLine :=
  let i := i.deleteSelection
  if i.text.size ≥ i.maxLength then i
  else
    let pos := min i.cursor i.text.size
    { i with text := i.text.extract 0 pos |>.push c |>.append (i.text.extract pos i.text.size),
             cursor := pos + 1 }

/-- Moves the cursor, extending the selection when `extend` is set. -/
def moveTo (i : InputLine) (pos : Nat) (extend : Bool) : InputLine :=
  let pos := min pos i.text.size
  if extend then { i with anchor := some (i.anchor.getD i.cursor), cursor := pos }
  else { i with anchor := none, cursor := pos }

def handleKey (i : InputLine) (s : Size) (k : KeyEvent) : InputLine × Reply :=
  let shift := k.mods.shift
  let r : Option InputLine := match k.key with
    | .left => some (i.moveTo (i.cursor - 1) shift)
    | .right => some (i.moveTo (i.cursor + 1) shift)
    | .home => some (i.moveTo 0 shift)
    | .end => some (i.moveTo i.text.size shift)
    | .backspace =>
      some (if i.selection?.isSome then i.deleteSelection
        else if i.cursor == 0 then i else i.deleteRange (i.cursor - 1) i.cursor)
    | .delete =>
      some (if i.selection?.isSome then i.deleteSelection
        else if i.cursor ≥ i.text.size then i else i.deleteRange i.cursor (i.cursor + 1))
    | .char 'a' => if k.mods.ctrl then some i.selectAll else k.text?.map i.insert
    | .char 'y' =>
      if k.mods.ctrl then some { i with text := #[], cursor := 0, anchor := none }
      else k.text?.map i.insert
    | _ => k.text?.map i.insert
  match r with
  | some i' => (i'.adjust s.w, .handled)
  | none => (i, .ignored)

def handleMouse (i : InputLine) (s : Size) (m : MouseEvent) : InputLine × Reply :=
  let pos := (m.pos.x - 1 + i.first).toNat
  match m.action with
  | .press =>
    if m.double then (i.selectAll.adjust s.w, .handled)
    else ((i.moveTo pos false).adjust s.w, .handled)
  | .drag => ((i.moveTo pos true).adjust s.w, .handled)
  | _ => (i, .handled)

def draw (i : InputLine) (ctx : DrawCtx) : DrawM Unit := do
  let c := ctx.theme.dialog
  let w := ctx.size.w
  let i := i.adjust w
  Draw.hline 0 0 w ' ' c.input
  Draw.putChars 1 0 (i.text.extract i.first (i.first + (w - 2))) c.input
  if i.text.size - i.first + 2 > w then Draw.putChar (w - 1) 0 '►' c.inputArrows
  if ctx.focused then
    if i.first > 0 then Draw.putChar 0 0 '◄' c.inputArrows
    if let some (lo, hi) := i.selection? then
      let l := min (lo - i.first) (w - 2)
      let r := min (hi - i.first) (w - 2)
      for x in [l:r] do
        Draw.modifyCell (x + 1) 0 fun cell => { cell with attr := c.inputSelection }

end InputLine

instance : Widget InputLine where
  draw := InputLine.draw
  handleKey := InputLine.handleKey
  handleMouse := InputLine.handleMouse
  cursor? i s := let i := i.adjust s.w; some ⟨i.cursor - i.first + 1, 0⟩
  wantsText _ := true
  onFocus i := i.selectAll

end HyperVision
