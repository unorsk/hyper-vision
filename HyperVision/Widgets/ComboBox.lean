import HyperVision.Widgets.InputLine

/-!
# Combo box

An input line with Turbo Vision's history button (`▐↓▌`). `Down` or a click on
the button asks the application to open a drop-down list of choices.

A combo box that is not `editable` is a plain drop-down list: its value is always one
of the items, shown from its start. `Space` opens the list too, and typing a letter
chooses the next item starting with it.
-/

namespace HyperVision

structure ComboBox where
  input : InputLine
  items : Array String
  /-- The value can be typed in, not only chosen from the list. -/
  editable : Bool := true
deriving Inhabited

namespace ComboBox

def ofItems (items : Array String) (value : String := items[0]?.getD "") (editable := true) : ComboBox :=
  let input := InputLine.ofString value
  { input := if editable then input else { input with cursor := 0 }, items, editable }

def value (c : ComboBox) : String := c.input.value

/-- Sets the text to the `i`-th item. -/
def choose (c : ComboBox) (i : Nat) : ComboBox :=
  match c.items[i]? with
  | some s =>
    let input := InputLine.ofString s c.input.maxLength
    { c with input := if c.editable then input.selectAll else { input with cursor := 0 } }
  | none => c

def inputSize (s : Size) : Size := ⟨s.w - 3, 1⟩

def dropDown (c : ComboBox) (s : Size) : Reply :=
  .dropDown ⟨0, 0, s.w - 3, 1⟩ c.items ((c.items.findIdx? (· == c.value)).getD 0)

/-- The next item after the current one that starts with `ch` (ignoring case). -/
def nextStartingWith (c : ComboBox) (ch : Char) : Option Nat :=
  let n := c.items.size
  let cur := (c.items.findIdx? (· == c.value)).getD (n - 1)
  (cyclicOrder n cur true).find? fun i =>
    ((c.items[i]?.bind (·.toList.head?)).map (·.toLower == ch.toLower)).getD false

def handleKey (c : ComboBox) (s : Size) (k : KeyEvent) : ComboBox × Reply :=
  if k.key == .down && !k.mods.ctrl then (c, c.dropDown s)
  else if c.editable then
    let (i, r) := InputLine.handleKey c.input (inputSize s) k
    ({ c with input := i }, r)
  else if k.key == .char ' ' && k.mods.isNone then (c, c.dropDown s)
  else match k.text? with
    | some ch =>
      match c.nextStartingWith ch with
      | some i =>
        let c' := c.choose i
        (c', if c'.value == c.value then .handled else .changed)
      | none => (c, .handled)
    | none => (c, .ignored)

end ComboBox

instance : Widget ComboBox where
  draw c ctx := do
    let t := ctx.theme.dialog
    let iw := ctx.size.w - 3
    -- A drop-down list shows its value from the start and never a selection.
    let input := if c.editable then c.input else { c.input with cursor := 0, first := 0, anchor := none }
    Draw.within ⟨0, 0, iw, 1⟩ (InputLine.draw input { ctx with size := ⟨iw, 1⟩ })
    Draw.putChar iw 0 '▐' t.historySides
    Draw.putChar (iw + 1) 0 '↓' t.historyArrow
    Draw.putChar (iw + 2) 0 '▌' t.historySides
  handleKey := ComboBox.handleKey
  handleMouse c s m :=
    if m.action == .press && (m.pos.x ≥ s.w - 3 || !c.editable) then (c, c.dropDown s)
    else if !c.editable then (c, .handled)
    else
      let (i, r) := InputLine.handleMouse c.input (ComboBox.inputSize s) m
      ({ c with input := i }, r)
  cursor? c s := if c.editable then Widget.cursor? c.input (ComboBox.inputSize s) else none
  wantsText c := c.editable
  onFocus c := if c.editable then { c with input := c.input.selectAll } else c

end HyperVision
