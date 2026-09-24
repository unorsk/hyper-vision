import HyperVision.Widgets.Label
import HyperVision.Widgets.Button
import HyperVision.Widgets.Cluster
import HyperVision.Widgets.InputLine
import HyperVision.Widgets.ComboBox
import HyperVision.Widgets.Memo

/-!
# Controls

A `Control` places a widget inside a window. The set of widget kinds is closed
(`ControlKind`), so application code can read results back with exhaustive,
typed accessors; behaviour is dispatched through the `Widget` class.
-/

namespace HyperVision

inductive ControlKind (α : Type) where
  | label (w : Label)
  | staticText (w : StaticText)
  | button (w : Button α)
  | checkBoxes (w : CheckBoxes)
  | radioButtons (w : RadioButtons)
  | inputLine (w : InputLine)
  | comboBox (w : ComboBox)
  | memo (w : Memo)
deriving Inhabited

namespace ControlKind

variable {α β : Type}

/-- Runs `f` on the widget, also passing a function that re-wraps an updated widget. -/
@[inline] def withWidget (k : ControlKind α)
    (f : {W : Type} → [Widget W] → W → (W → ControlKind α) → β) : β :=
  match k with
  | label w => f w label
  | staticText w => f w staticText
  | button w => f w button
  | checkBoxes w => f w checkBoxes
  | radioButtons w => f w radioButtons
  | inputLine w => f w inputLine
  | comboBox w => f w comboBox
  | memo w => f w memo

def draw (k : ControlKind α) (ctx : DrawCtx) : DrawM Unit :=
  k.withWidget fun w _ => Widget.draw w ctx

def handleKey (k : ControlKind α) (s : Size) (e : KeyEvent) : ControlKind α × Reply :=
  k.withWidget fun w wrap => let (w, r) := Widget.handleKey w s e; (wrap w, r)

def handleMouse (k : ControlKind α) (s : Size) (e : MouseEvent) : ControlKind α × Reply :=
  k.withWidget fun w wrap => let (w, r) := Widget.handleMouse w s e; (wrap w, r)

def focusable (k : ControlKind α) : Bool := k.withWidget fun w _ => Widget.focusable w

def hotkey (k : ControlKind α) (c : Char) : Option (ControlKind α × Reply) :=
  k.withWidget fun w wrap => (Widget.hotkey w c).map fun (w, r) => (wrap w, r)

def cursor? (k : ControlKind α) (s : Size) : Option Point :=
  k.withWidget fun w _ => Widget.cursor? w s

def wantsText (k : ControlKind α) : Bool := k.withWidget fun w _ => Widget.wantsText w

def onFocus (k : ControlKind α) : ControlKind α := k.withWidget fun w wrap => wrap (Widget.onFocus w)

def cancelMouse (k : ControlKind α) : ControlKind α :=
  k.withWidget fun w wrap => wrap (Widget.cancelMouse w)

end ControlKind

/--
How a control follows its window when the window is resized (Turbo Vision's
`growMode`): each flag makes that edge keep its distance to the window's
right (`X`) or bottom (`Y`) edge.
-/
structure GrowMode where
  loX : Bool := false
  loY : Bool := false
  hiX : Bool := false
  hiY : Bool := false
deriving BEq, Repr, Inhabited

namespace GrowMode

def fixed : GrowMode := {}
/-- Stretch with the window in both directions. -/
def stretch : GrowMode := { hiX := true, hiY := true }
/-- Stretch horizontally. -/
def stretchX : GrowMode := { hiX := true }
/-- Stick to the bottom-right corner. -/
def anchorBottomRight : GrowMode := { loX := true, loY := true, hiX := true, hiY := true }
/-- Stick to the bottom edge. -/
def anchorBottom : GrowMode := { loY := true, hiY := true }

/-- The bounds of a control after its window grew by `(dx, dy)`. -/
def apply (g : GrowMode) (r : Rect) (dx dy : Int) : Rect :=
  let x0 := if g.loX then r.x + dx else r.x
  let y0 := if g.loY then r.y + dy else r.y
  let x1 := if g.hiX then r.right + dx else r.right
  let y1 := if g.hiY then r.bottom + dy else r.bottom
  ⟨x0, y0, (x1 - x0).toNat, (y1 - y0).toNat⟩

end GrowMode

structure Control (α : Type) where
  /-- Used to link labels and to read values back; may be empty. -/
  name : String := ""
  /-- Position relative to the window interior, for the window's `layoutSize`. -/
  bounds : Rect
  grow : GrowMode := {}
  kind : ControlKind α
deriving Inhabited

namespace Control

variable {α : Type}

def size (c : Control α) : Size := ⟨c.bounds.w, c.bounds.h⟩

/-! ### Constructors -/

def label (x y : Int) (text : String) (link : Option String := none) : Control α :=
  { bounds := ⟨x, y, (HotText.parse text).width + 2, 1⟩, kind := .label { text, link } }

def staticText (bounds : Rect) (text : String) (grow : GrowMode := {}) : Control α :=
  { bounds, grow, kind := .staticText { text } }

def button (x y : Int) (w : Nat) (title : String) (cmd : Command α) (isDefault : Bool := false)
    (grow : GrowMode := {}) : Control α :=
  { bounds := ⟨x, y, w, 2⟩, grow, kind := .button { title, command := cmd, isDefault } }

def checkBoxes (name : String) (bounds : Rect) (items : Array String)
    (checked : Array Bool := #[]) : Control α :=
  { name, bounds,
    kind := .checkBoxes { items := items.mapIdx fun i s => (HotText.parse s, checked[i]?.getD false) } }

def radioButtons (name : String) (bounds : Rect) (items : Array String) (selected : Nat := 0) :
    Control α :=
  { name, bounds, kind := .radioButtons { items := items.map HotText.parse, selected } }

def inputLine (name : String) (x y : Int) (w : Nat) (value : String := "")
    (grow : GrowMode := {}) : Control α :=
  { name, bounds := ⟨x, y, w, 1⟩, grow, kind := .inputLine (InputLine.ofString value) }

def comboBox (name : String) (x y : Int) (w : Nat) (items : Array String)
    (value : String := items[0]?.getD "") : Control α :=
  { name, bounds := ⟨x, y, w, 1⟩, kind := .comboBox (ComboBox.ofItems items value) }

def memo (name : String) (bounds : Rect) (text : String := "") (grow : GrowMode := {})
    (scrollBar := true) : Control α :=
  { name, bounds, grow, kind := .memo { Memo.ofString text with scrollBar } }

/-! ### Reading values -/

/-- The text of an input line, combo box or memo. -/
def text? (c : Control α) : Option String :=
  match c.kind with
  | .inputLine i => some i.value
  | .comboBox cb => some cb.value
  | .memo m => some m.text
  | _ => none

/-- The states of a group of check boxes. -/
def checked? (c : Control α) : Option (Array Bool) :=
  match c.kind with
  | .checkBoxes cb => some cb.values
  | _ => none

/-- The selected index of a group of radio buttons. -/
def selected? (c : Control α) : Option Nat :=
  match c.kind with
  | .radioButtons rb => some rb.selected
  | _ => none

end Control

end HyperVision
