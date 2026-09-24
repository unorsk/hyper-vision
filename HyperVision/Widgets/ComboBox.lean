import HyperVision.Widgets.InputLine

/-!
# Combo box

An input line with Turbo Vision's history button (`▐↓▌`). `Down` or a click on
the button asks the application to open a drop-down list of choices.
-/

namespace HyperVision

structure ComboBox where
  input : InputLine
  items : Array String
deriving Inhabited

namespace ComboBox

def ofItems (items : Array String) (value : String := items[0]?.getD "") : ComboBox :=
  { input := InputLine.ofString value, items }

def value (c : ComboBox) : String := c.input.value

/-- Sets the text to the `i`-th item. -/
def choose (c : ComboBox) (i : Nat) : ComboBox :=
  match c.items[i]? with
  | some s => { c with input := (InputLine.ofString s c.input.maxLength).selectAll }
  | none => c

def inputSize (s : Size) : Size := ⟨s.w - 3, 1⟩

def dropDown (c : ComboBox) (s : Size) : Reply :=
  .dropDown ⟨0, 0, s.w - 3, 1⟩ c.items ((c.items.findIdx? (· == c.value)).getD 0)

end ComboBox

instance : Widget ComboBox where
  draw c ctx := do
    let t := ctx.theme.dialog
    let iw := ctx.size.w - 3
    Draw.within ⟨0, 0, iw, 1⟩ (InputLine.draw c.input { ctx with size := ⟨iw, 1⟩ })
    Draw.putChar iw 0 '▐' t.historySides
    Draw.putChar (iw + 1) 0 '↓' t.historyArrow
    Draw.putChar (iw + 2) 0 '▌' t.historySides
  handleKey c s k :=
    if k.key == .down then (c, c.dropDown s)
    else
      let (i, r) := InputLine.handleKey c.input (ComboBox.inputSize s) k
      ({ c with input := i }, r)
  handleMouse c s m :=
    if m.action == .press && m.pos.x ≥ s.w - 3 then (c, c.dropDown s)
    else
      let (i, r) := InputLine.handleMouse c.input (ComboBox.inputSize s) m
      ({ c with input := i }, r)
  cursor? c s := Widget.cursor? c.input (ComboBox.inputSize s)
  wantsText _ := true
  onFocus c := { c with input := c.input.selectAll }

end HyperVision
