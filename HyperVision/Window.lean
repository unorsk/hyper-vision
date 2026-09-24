import HyperVision.Control

/-!
# Windows

A framed, movable, resizable container of controls: `TWindow`/`TDialog` with
`TFrame` drawing, focus traversal, hot keys, default buttons, and — for editor
windows — scroll bars and a line:column indicator embedded in the frame.
-/

namespace HyperVision

inductive WindowStyle where
  | blue | cyan | gray | dialog
deriving DecidableEq, Repr, Inhabited

def WindowStyle.colors (t : Theme) : WindowStyle → WindowColors
  | .blue => t.blueWindow
  | .cyan => t.cyanWindow
  | .gray => t.grayWindow
  | .dialog =>
    { frame := t.dialog.frame, scrollPage := t.dialog.scrollPage
      scrollControls := t.dialog.scrollControls, text := t.dialog.staticText
      selection := t.dialog.labelSelected }

/-- Which frame gadgets a window has (Turbo Vision's `wfMove`, `wfGrow`, …). -/
structure WindowFlags where
  move : Bool := true
  grow : Bool := true
  close : Bool := true
  zoom : Bool := true
deriving BEq, Repr, Inhabited

namespace WindowFlags
/-- Dialogs can be moved and closed, but not resized or zoomed. -/
def dialog : WindowFlags := { grow := false, zoom := false }
end WindowFlags

structure Window (α : Type) where
  /-- Assigned by the desktop. -/
  id : Nat := 0
  title : String
  /-- Shown in the frame (1‥9) and selectable with `Alt+n`. -/
  number : Option Nat := none
  /-- Bounds in screen coordinates, frame included. -/
  bounds : Rect
  /-- The window size the controls were laid out for. Their actual bounds follow from
  their grow modes and the difference to this size, so shrinking never loses layout. -/
  layoutSize : Size := ⟨bounds.w, bounds.h⟩
  style : WindowStyle := .blue
  flags : WindowFlags := {}
  controls : Array (Control α) := #[]
  focus : Option Nat := none
  minSize : Size := ⟨16, 6⟩
  /-- Bounds to restore when un-zooming (Turbo Vision's `zoomRect`). -/
  zoomRect : Option Rect := none
  /-- A modal window blocks the rest of the desktop until it is closed. -/
  modal : Bool := false
  /-- A memo whose scroll bars and cursor indicator live on the frame (editor windows). -/
  editor : Option Nat := none
  /-- Set while the window is being moved or resized. -/
  dragging : Bool := false
deriving Inhabited

/-- What a window asks of its owner after handling an event. -/
inductive WindowReply (α : Type) where
  | ignored
  | handled
  | command (c : Command α)
  /-- Open a drop-down list for control `control` under `anchor` (window coordinates). -/
  | dropDown (control : Nat) (anchor : Rect) (items : Array String) (current : Nat)
deriving Inhabited

/-- The frame part under the mouse. -/
inductive FrameHit where
  | close | zoom | move | resize
  | vScroll (offset : Nat) | hScroll (offset : Nat)
  | interior | border
deriving BEq, Repr, Inhabited

namespace Window

variable {α : Type}

def size (w : Window α) : Size := ⟨w.bounds.w, w.bounds.h⟩

/-- The client area in window coordinates. -/
def interior (w : Window α) : Rect := ⟨1, 1, w.bounds.w - 2, w.bounds.h - 2⟩

def isDialog (w : Window α) : Bool := w.style == .dialog

/-- Whether the window has the maximum size, i.e. that of the desktop `desk`. -/
def isMaximized (w : Window α) (desk : Rect) : Bool := w.bounds.w == desk.w && w.bounds.h == desk.h

def controlIndex? (w : Window α) (name : String) : Option Nat :=
  w.controls.findIdx? (·.name == name)

def control? (w : Window α) (name : String) : Option (Control α) :=
  w.controls.find? (·.name == name)

/-- Updates the control named `name`. -/
def modifyControl (w : Window α) (name : String) (f : Control α → Control α) : Window α :=
  match w.controlIndex? name with
  | some i => { w with controls := w.controls.modify i f }
  | none => w

def focused? (w : Window α) : Option (Control α) := w.focus.bind (w.controls[·]?)

def focusable (w : Window α) (i : Nat) : Bool :=
  (w.controls[i]?.map (·.kind.focusable)).getD false

/-- Gives the focus to control `i` (if it can take it). -/
def setFocus (w : Window α) (i : Nat) : Window α :=
  if w.focus == some i || !w.focusable i then w
  else { w with focus := some i, controls := w.controls.modify i fun c => { c with kind := c.kind.onFocus } }

/-- Moves the focus to the next (or previous) focusable control, wrapping around. -/
def focusNext (w : Window α) (forward : Bool := true) : Window α :=
  let n := w.controls.size
  if n == 0 then w else
  let start := w.focus.getD (if forward then n - 1 else 0)
  match (cyclicOrder n start forward).find? w.focusable with
  | some i => w.setFocus i
  | none => w

/-- Focuses the first focusable control, if nothing has the focus yet. -/
def initFocus (w : Window α) : Window α :=
  if w.focus.isSome then w else
  match (List.range w.controls.size).find? w.focusable with
  | some i => w.setFocus i
  | none => w

/-- Whether control `i` is drawn emphasized (labels of the focused control, the default button). -/
def emphasized (w : Window α) (i : Nat) : Bool :=
  match w.controls[i]? with
  | some { kind := .label l, .. } =>
    match l.link, w.focused? with
    | some name, some f => f.name == name
    | _, _ => false
  | some { kind := .button b, .. } =>
    b.isDefault && !(w.focused?.any fun c => match c.kind with | .button _ => true | _ => false)
  | _ => false

/-- Moves or resizes the window; controls follow through their grow modes. -/
def setBounds (w : Window α) (r : Rect) : Window α := { w with bounds := r }

/-- A control's current bounds (interior coordinates), after applying its grow mode. -/
def boundsOf (w : Window α) (c : Control α) : Rect :=
  c.grow.apply c.bounds ((w.bounds.w : Int) - w.layoutSize.w) ((w.bounds.h : Int) - w.layoutSize.h)

def sizeOf (w : Window α) (c : Control α) : Size :=
  let r := w.boundsOf c
  ⟨r.w, r.h⟩

/-! ### Drawing -/

private def editorMemo? (w : Window α) : Option Memo :=
  w.editor.bind (w.controls[·]?) |>.bind fun c => match c.kind with
    | .memo m => some m
    | _ => none

/-- Editor-window scroll bars: vertical along the right edge, horizontal after the indicator. -/
def vScrollBar? (w : Window α) : Option ScrollBar :=
  (editorMemo? w).map fun m => m.vBar (w.bounds.h - 2) (w.bounds.h - 2)

def hScrollBar? (w : Window α) : Option ScrollBar :=
  if w.bounds.w < 24 then none else
  (editorMemo? w).map fun m => m.hBar (w.bounds.w - 2) (w.bounds.w - 20)

def drawFrame (w : Window α) (t : Theme) (active maximized : Bool) : DrawM Unit := do
  let fc := (w.style.colors t).frame
  let (cFrame, bc) :=
    if w.dragging then (fc.icon, BoxChars.single)
    else if active then (fc.active, BoxChars.double)
    else (fc.passive, BoxChars.single)
  let wd := w.bounds.w
  let ht := w.bounds.h
  Draw.fill ⟨0, 0, wd, ht⟩ ' ' cFrame
  Draw.box ⟨0, 0, wd, ht⟩ bc cFrame
  -- Title, centered with one blank on each side.
  let l := min w.title.length (wd - 10)
  let i := (wd - l) / 2
  if l > 0 then
    Draw.putChar (i - 1 : Int) 0 ' ' cFrame
    Draw.putStr i 0 (String.ofList (w.title.toList.take l)) cFrame
    Draw.putChar (i + l) 0 ' ' cFrame
  if let some n := w.number then
    if n < 10 then
      Draw.putChar (wd - (if w.flags.zoom then 7 else 3) : Nat) 0 (Char.ofNat (48 + n)) cFrame
  if active then
    if w.flags.close then
      Draw.putStr 2 0 "[ ]" cFrame
      Draw.putChar 3 0 '■' fc.icon
    if w.flags.zoom then
      Draw.putStr (wd - 5 : Nat) 0 "[ ]" cFrame
      Draw.putChar (wd - 4 : Nat) 0 (if maximized then '↕' else '↑') fc.icon
    if w.flags.grow then
      Draw.putStr (wd - 2 : Nat) (ht - 1 : Nat) "─┘" fc.icon
    -- Editor windows: scroll bars and the line:column indicator.
    let wc := w.style.colors t
    if let some sb := w.vScrollBar? then
      sb.draw (wd - 1 : Nat) 1 wc.scrollPage wc.scrollControls
    if let some sb := w.hScrollBar? then
      sb.draw 18 (ht - 1 : Nat) wc.scrollPage wc.scrollControls
    if let some m := editorMemo? w then
      let attr := if w.dragging then fc.icon else fc.active
      Draw.hline 2 (ht - 1 : Nat) 14 (if w.dragging then '─' else '═') attr
      if m.modified then Draw.putChar 2 (ht - 1 : Nat) '☼' attr
      let s := s!" {m.cursor.row + 1}:{m.cursor.col + 1} "
      let colon := (s.toList.findIdx? (· == ':')).getD 0
      Draw.putStr (2 + 8 - colon : Int) (ht - 1 : Nat) s attr

def draw (w : Window α) (t : Theme) (active : Bool) (maximized : Bool := false) : DrawM Unit := do
  drawFrame w t active maximized
  let colors := w.style.colors t
  Draw.within w.interior do
    for h : i in [0:w.controls.size] do
      let c := w.controls[i]
      let ctx : DrawCtx :=
        { theme := t, size := w.sizeOf c, focused := active && w.focus == some i
          emphasized := active && w.emphasized i, inDialog := w.isDialog, window := colors }
      Draw.within (w.boundsOf c) (c.kind.draw ctx)

/-- Where the hardware cursor goes (window coordinates), if the focused control has one. -/
def cursorPos? (w : Window α) : Option Point := do
  let c ← w.focused?
  let r := w.boundsOf c
  let p ← c.kind.cursor? (w.sizeOf c)
  let abs := p + r.origin + ⟨1, 1⟩
  if w.interior.contains abs && r.contains (p + r.origin) then some abs else none

/-! ### Events -/

/-- Translates a control's reply into a window reply. -/
def applyReply (w : Window α) (i : Nat) (r : Reply) : Window α × WindowReply α :=
  match r with
  | .ignored => (w, .ignored)
  | .handled => (w, .handled)
  | .activated =>
    match w.controls[i]? with
    | some { kind := .button b, .. } => (w, .command b.command)
    | _ => (w, .handled)
  | .focus name =>
    match w.controlIndex? name with
    | some j => (w.setFocus j, .handled)
    | none => (w, .handled)
  | .dropDown anchor items current =>
    let origin := (w.controls[i]?.map (w.boundsOf · |>.origin)).getD Point.origin
    (w, .dropDown i (anchor.translate (origin + ⟨1, 1⟩)) items current)

/-- Replaces the kind (widget state) of control `i`. -/
def updateKind (w : Window α) (i : Nat) (k : ControlKind α) : Window α :=
  { w with controls := w.controls.modify i fun c => { c with kind := k } }

/-- Offers a hot key to every control, in order. -/
def dispatchHotkey (w : Window α) (ch : Char) : Option (Window α × WindowReply α) :=
  (List.range w.controls.size).findSome? fun i => do
    let c ← w.controls[i]?
    let (k, r) ← c.kind.hotkey ch
    pure ((updateKind w i k).setFocus i |>.applyReply i r)

/-- The default button's command, if there is an enabled default button. -/
def defaultCommand? (w : Window α) : Option (Command α) :=
  w.controls.findSome? fun c => match c.kind with
    | .button b => if b.isDefault && b.enabled then some b.command else none
    | _ => none

/-- Offers a key to the focused control. -/
def keyToFocus (w : Window α) (k : KeyEvent) : Window α × WindowReply α :=
  match w.focus, w.focused? with
  | some i, some c =>
    let (kind, r) := c.kind.handleKey (w.sizeOf c) k
    (updateKind w i kind).applyReply i r
  | _, _ => (w, .ignored)

/-- What the window itself does with a key the focused control ignored: hot keys,
`Tab`/`Shift-Tab`, the default button on `Enter`, and `Esc` in dialogs. -/
def keyFallback (w : Window α) (k : KeyEvent) : Window α × WindowReply α :=
  let focusTakesText := w.focused?.any (·.kind.wantsText)
  let hot : Option Char := match k.key with
    | .char c =>
      if k.mods.alt && !k.mods.ctrl then some c.toLower
      else if k.mods.isNone && !focusTakesText then some c.toLower
      else none
    | _ => none
  match k.key, hot >>= w.dispatchHotkey with
  | _, some res => res
  | .tab, none => (w.focusNext !k.mods.shift, .handled)
  | .enter, none =>
    match w.defaultCommand? with
    | some cmd => (w, .command cmd)
    | none => (w, .ignored)
  | .escape, none => if w.isDialog then (w, .command .cancel) else (w, .ignored)
  | _, none => (w, .ignored)

def handleKey (w : Window α) (k : KeyEvent) : Window α × WindowReply α :=
  match w.keyToFocus k with
  | (w, .ignored) => w.keyFallback k
  | res => res

/-- Classifies a left-button press at window coordinates `p`. -/
def frameHit (w : Window α) (p : Point) : FrameHit :=
  let wd : Int := w.bounds.w
  let ht : Int := w.bounds.h
  if p.y == 0 then
    if w.flags.close && 2 ≤ p.x && p.x ≤ 4 then .close
    else if w.flags.zoom && wd - 5 ≤ p.x && p.x ≤ wd - 3 then .zoom
    else if w.flags.move then .move else .border
  else if p.y == ht - 1 && p.x ≥ wd - 2 && w.flags.grow then .resize
  else if w.vScrollBar?.isSome && p.x == wd - 1 && 1 ≤ p.y && p.y ≤ ht - 2 then
    .vScroll (p.y - 1).toNat
  else if (w.hScrollBar?.map (·.length)).any (fun len => p.y == ht - 1 && 18 ≤ p.x && p.x < 18 + len) then
    .hScroll (p.x - 18).toNat
  else if w.interior.contains p then .interior
  else .border

/-- The top-most control under `p` (window coordinates). -/
def controlAt? (w : Window α) (p : Point) : Option Nat :=
  let q := p - ⟨1, 1⟩
  (List.range w.controls.size).reverse.find? fun i =>
    (w.controls[i]?.map fun c => (w.boundsOf c).contains q).getD false

/-- Delivers a mouse event (window coordinates) to control `i`, focusing it on a press. -/
def mouseControl (w : Window α) (i : Nat) (e : MouseEvent) : Window α × WindowReply α :=
  let w := if e.action == .press then w.setFocus i else w
  match w.controls[i]? with
  | some c =>
    let (kind, r) := c.kind.handleMouse (w.sizeOf c) (e.relativeTo ((w.boundsOf c).origin + ⟨1, 1⟩))
    (updateKind w i kind).applyReply i r
  | none => (w, .ignored)

/-- Scrolls the editor memo from a click on a frame scroll bar, or (with `thumb`) from
dragging its thumb to `offset`. -/
def scrollEditor (w : Window α) (vertical : Bool) (offset : Nat) (thumb : Bool := false) :
    Window α :=
  match w.editor, w.editor.bind (w.controls[·]?) with
  | some i, some c@{ kind := .memo m, .. } =>
    let s := w.sizeOf c
    let sb? := if vertical then w.vScrollBar? else w.hScrollBar?
    match sb? with
    | some sb =>
      let m := if thumb then m.scrollToValue s vertical (sb.valueAt offset)
        else m.scrollPart s vertical sb offset
      updateKind w i (.memo m)
    | none => w
  | _, _ => w

/-- Abandons the mouse interaction of control `i` (its release was lost). -/
def cancelMouse (w : Window α) (i : Nat) : Window α :=
  { w with controls := w.controls.modify i fun c => { c with kind := c.kind.cancelMouse } }

/-- Mouse wheel over an editor window scrolls its text. -/
def wheel (w : Window α) (down : Bool) : Window α :=
  match w.editor, w.editor.bind (w.controls[·]?) with
  | some i, some c@{ kind := .memo m, .. } =>
    updateKind w i (.memo (m.scrollBy (w.sizeOf c) (if down then 3 else -3) 0))
  | _, _ => w

/-! ### Constructors -/

/-- An empty window with a frame of the given class. -/
def new (title : String) (bounds : Rect) (style : WindowStyle := .blue) : Window α :=
  { title, bounds, style }

/-- A dialog box: gray, movable, closable, not resizable. -/
def dialog (title : String) (bounds : Rect) (controls : Array (Control α)) : Window α :=
  initFocus { title, bounds, style := .dialog, flags := .dialog, controls, minSize := ⟨bounds.w, bounds.h⟩ }

/-- A text editor window: a memo filling the interior, scroll bars in the frame. -/
def editorWindow (title : String) (bounds : Rect) (text : String) : Window α :=
  let memo : Control α :=
    { name := "text", bounds := ⟨0, 0, bounds.w - 2, bounds.h - 2⟩, grow := .stretch
      kind := .memo { Memo.ofString text with acceptsTab := true } }
  { title, bounds, style := .blue, controls := #[memo], focus := some 0, editor := some 0 }

end Window

end HyperVision
