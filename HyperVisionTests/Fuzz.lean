import HyperVision

/-!
# Application fuzzing

Drives a complete application (menus, status line, editor windows, a dialog with
every kind of control, modal message boxes) with long random sessions of key
presses, mouse gestures aimed at window parts, and terminal resizes, and checks
after every single event that the whole state is consistent:

* the desktop is well-formed and every window's focus is on a focusable control;
* no window is lost: part of every title bar is on the desktop;
* windows keep their minimum size (unless maximized to a smaller desktop);
* widget states are valid (cursors on the text, selections in range, lengths within
  limits, list selections in range);
* menus, drop-down lists, mouse captures and keyboard drags refer to things that
  exist, and a capture ends with the button release;
* a modal window stays in front until it is closed, and no menu opens over it;
* the frame has the screen's size, the cursor is inside the active window, and the
  active window is drawn exactly as it draws itself (nothing leaks on top of it).

A failing session is shrunk to a short event sequence and reported.
-/

namespace HyperVisionTests.Fuzz

open HyperVision

/-! ## The application under test (the demo's windows and commands) -/

inductive Cmd where
  | newEditor | openControls | about | showValues
  | insert (text : String)
deriving BEq, Inhabited

def controlsDialog : Window Cmd :=
  Window.dialog "Controls" ⟨28, 2, 50, 20⟩ #[
    Control.label 1 1 "~N~ame" (some "name"),
    { name := "name", bounds := ⟨13, 1, 32, 1⟩, kind := .inputLine (InputLine.ofString "Anders" 12) },
    Control.label 1 3 "~L~anguage" (some "lang"),
    Control.comboBox "lang" 13 3 24 #["Lean 4", "Turbo Pascal", "C++", "Haskell", "OCaml", "Rust",
      "Modula-2", "Oberon", "Ada", "Forth", "Lisp"] "Turbo Pascal",
    Control.label 1 5 "~S~tyle" (some "style"),
    Control.checkBoxes "style" ⟨2, 6, 20, 3⟩ #["~B~old", "~I~talic", "~U~nderline"] #[true, false, true],
    Control.label 24 5 "Si~z~e" (some "size"),
    Control.radioButtons "size" ⟨25, 6, 21, 3⟩ #["Sm~a~ll", "~M~edium", "La~r~ge"] 1,
    Control.label 1 10 "No~t~es" (some "notes"),
    Control.memo "notes" ⟨2, 11, 44, 4⟩ "A memo.\n  Indented\n\nwide 中文 and é\nfive\nsix\nseven",
    Control.button 10 16 12 "~O~K" (.user .showValues) (isDefault := true),
    Control.button 25 16 12 "Cancel" .cancel ]

def menuBar : Array (Menu Cmd) := #[
  Menu.new "~≡~" #[
    MenuItem.item "~A~bout..." (.user .about),
    .separator,
    MenuItem.item "~C~ontrols..." (.user .openControls)],
  Menu.new "~F~ile" #[
    MenuItem.item "~N~ew" (.user .newEditor) (some (KeyEvent.plain (.f 4))),
    MenuItem.item "~O~pen controls..." (.user .openControls) (some (KeyEvent.plain (.f 3))),
    .separator,
    MenuItem.item "E~x~it" .quit (some (KeyEvent.alt 'x'))],
  Menu.new "~E~dit" #[
    MenuItem.item "~U~ndo" .quit none (enabled := false),
    .separator,
    MenuItem.sub "~I~nsert" #[
      MenuItem.item "~G~reeting" (.user (.insert "Hello!")),
      .separator,
      MenuItem.item "~L~ines" (.user (.insert "one\ntwo\n  three"))]],
  Menu.new "~W~indow" #[
    MenuItem.item "~T~ile" .tile,
    MenuItem.item "C~a~scade" .cascade,
    .separator,
    MenuItem.item "~S~ize/move" .resize (some ⟨.f 5, { ctrl := true }⟩),
    MenuItem.item "~Z~oom" .zoom (some (KeyEvent.plain (.f 5))),
    MenuItem.item "~N~ext" .nextWindow (some (KeyEvent.plain (.f 6))),
    MenuItem.item "~P~revious" .prevWindow (some ⟨.f 6, { shift := true }⟩),
    MenuItem.item "~C~lose" .close (some ⟨.f 3, { alt := true }⟩)]]

def statusLine : Array (StatusItem Cmd) := #[
  StatusItem.new "~Alt-X~ Exit" (KeyEvent.alt 'x') .quit,
  StatusItem.new "~F3~ Controls" (KeyEvent.plain (.f 3)) (.user .openControls),
  StatusItem.new "~F4~ New" (KeyEvent.plain (.f 4)) (.user .newEditor),
  StatusItem.new "~F5~ Zoom" (KeyEvent.plain (.f 5)) .zoom,
  StatusItem.new "~F6~ Next" (KeyEvent.plain (.f 6)) .nextWindow,
  StatusItem.new "~Alt-F3~ Close" ⟨.f 3, { alt := true }⟩ .close,
  StatusItem.new "~F10~ Menu" (KeyEvent.plain (.f 10)) .menu]

def onCommand (cmd : Cmd) (source : Option (Window Cmd)) (d : Desktop Cmd) : IO (Handled Cmd) := do
  -- No jobs here; the `Desktop → Handled` coercion supplies the empty job list.
  let d' : Desktop Cmd := match cmd with
  | .about => d.insertCentered (Window.messageBox "About" "^CHyper Vision\n\nA modal box.")
  | .openControls =>
    match d.windows.find? (·.title == "Controls") with
    | some w => d.raise w.id
    | none => d.insertCentered controlsDialog
  | .newEditor =>
    let k : Int := d.windows.size
    d.insert (Window.editorWindow "Untitled" ⟨2 + 2 * k, 2 + k, 40, 12⟩ "")
  | .showValues =>
    match source with
    | some w => (d.close w.id).insertCentered (Window.messageBox "Values" "Some values.")
    | none => d
  | .insert text =>
    match d.top? with
    | some w => d.modify w.id fun w => w.modifyControl "text" fun c => match c.kind with
        | .memo m => { c with kind := .memo (m.insertText text) }
        | _ => c
    | none => d
  return d'

def app : App Cmd := { menuBar, statusLine, onCommand }

def initial (w h : Nat) : AppState Cmd :=
  let screen : Size := ⟨w, h⟩
  let windows := #[Window.editorWindow "Hello" ⟨1, 2, 46, 16⟩ "def main : IO Unit :=\n  pure ()\n",
    controlsDialog]
  { desktop := windows.foldl Desktop.insert ({ bounds := App.desktopRect screen } : Desktop Cmd), screen }

/-! ## Invariants -/

def inputLineIssues (i : InputLine) : List String :=
  (if i.cursor ≤ i.text.size then [] else ["input line: cursor past the end"]) ++
  (if i.text.size ≤ i.maxLength then [] else ["input line: text longer than its maximum"]) ++
  (if i.anchor.all (· ≤ i.text.size) then [] else ["input line: selection anchor past the end"]) ++
  (if i.first ≤ i.text.size then [] else ["input line: scrolled past the end"])

def memoIssues (m : Memo) : List String :=
  let onText (p : TextPos) := p.row < m.lines.size && p.col ≤ (m.line p.row).size
  (if 0 < m.lines.size then [] else ["memo: no lines"]) ++
  (if onText m.cursor then [] else ["memo: cursor off the text"]) ++
  (if m.anchor.all onText then [] else ["memo: selection anchor off the text"])

def controlIssues (c : Control Cmd) : List String :=
  match c.kind with
  | .inputLine i => inputLineIssues i
  | .comboBox cb => inputLineIssues cb.input
  | .memo m => memoIssues m
  | .radioButtons r => if r.selected < r.items.size then [] else ["radio buttons: selection out of range"]
  | .checkBoxes cb => if cb.cursor < cb.items.size then [] else ["check boxes: cursor out of range"]
  | _ => []

def captureWindow? : Capture → Option Nat
  | .move id _ | .resize id _ | .control id _ | .closeIcon id | .scroll id .. => some id
  | _ => none

/-- Everything that must hold between events. `before` is the state the event was applied to. -/
def issues (before : AppState Cmd) (ev : Event) (st : AppState Cmd) : IO (List String) := do
  let d := st.desktop
  let desk := App.desktopRect st.screen
  let exists_ (id : Nat) := (d.find? id).isSome
  let mut out : List String := []
  -- Desktop and windows.
  unless decide d.ids.Nodup && d.ids.all (· < d.nextId) do out := "desktop not well-formed" :: out
  for w in d.windows do
    let tag := s!"window {w.id} '{w.title}'"
    unless w.focus.all w.focusable do out := s!"{tag}: focus on a control that cannot take it" :: out
    if 0 < desk.w && 0 < desk.h then
      unless max desk.x w.bounds.x < min desk.right w.bounds.right && desk.y ≤ w.bounds.y &&
          w.bounds.y < desk.bottom do
        out := s!"{tag}: title bar off the desktop at {repr w.bounds}" :: out
    unless (w.minSize.w ≤ w.bounds.w && w.minSize.h ≤ w.bounds.h) || w.isMaximized desk do
      out := s!"{tag}: smaller than its minimum size: {repr w.bounds}" :: out
    for c in w.controls do
      out := (controlIssues c).map (s!"{tag}: " ++ ·) ++ out
    let dragged := (captureWindow? st.capture == some w.id &&
        match st.capture with | .move .. | .resize .. => true | _ => false) ||
      st.keyDrag.any (·.1 == w.id)
    unless w.dragging == dragged do
      out := s!"{tag}: dragging flag is {w.dragging} but a drag is {if dragged then "" else "not "}in progress" :: out
  -- Menus.
  if let some t := st.menu then
    if d.modalActive then out := "a menu is open over a modal window" :: out
    if t.bar ≥ app.menuBar.size then out := "menu: bar entry out of range" :: out
    let boxes := MenuBar.boxes app.menuBar t st.screen
    unless boxes.size == t.path.size do out := "menu: open boxes and highlight path disagree" :: out
    for h : k in [0:boxes.size] do
      let items := boxes[k].2
      match t.path[k]? >>= (items[·]?) with
      | some it => if it.isSeparator then out := "menu: a separator is highlighted" :: out
      | none => out := "menu: highlighted item out of range" :: out
  -- Drop-down list.
  if let some p := st.popup then
    unless d.top?.map (·.id) == some p.window do out := "drop-down list of an inactive window" :: out
    match (d.find? p.window).bind (·.controls[p.control]?) with
    | some { kind := .comboBox _, .. } => pure ()
    | _ => out := "drop-down list without its combo box" :: out
    unless p.current < p.items.size do out := "drop-down list: selection out of range" :: out
    unless p.top ≤ p.current && p.current < p.top + max p.listHeight 1 do
      out := "drop-down list: selection scrolled out of view" :: out
  -- Mouse capture and keyboard drag.
  if let some id := captureWindow? st.capture then
    unless exists_ id do out := s!"mouse capture of closed window {id}" :: out
  if let .status i := st.capture then
    unless i < app.statusLine.size do out := "status capture out of range" :: out
  if let .mouse { action := .release, .. } := ev then
    unless st.capture == .none do out := "mouse capture outlived the button release" :: out
  if let some (id, _) := st.keyDrag then
    unless exists_ id do out := s!"keyboard drag of closed window {id}" :: out
  -- Modality.
  if let some m := before.desktop.top? then
    if m.modal && exists_ m.id && !d.modalActive then
      out := s!"modal window {m.id} lost the front" :: out
  -- Rendering.
  let ((frame, cursor), _) ← (App.render.run app).run st
  unless frame.width == st.screen.w && frame.height == st.screen.h do
    out := "frame size differs from the screen size" :: out
  if let some c := cursor then
    let inside := d.top?.any fun w => (w.interior.translate w.bounds.origin).contains c
    unless desk.contains c && inside do out := s!"cursor at {repr c} outside the active window" :: out
  if st.menu.isNone && st.popup.isNone then
    if let some w := d.top? then
      let alone := Draw.run (Screen.new st.screen.w st.screen.h) do
        Draw.clip desk (Draw.within w.bounds (w.draw app.theme true (w.isMaximized desk)))
      let r := w.bounds.intersect desk
      let mut diff := false
      for y in [0:r.h] do
        for x in [0:r.w] do
          if frame.get? (r.x + x) (r.y + y) != alone.get? (r.x + x) (r.y + y) then diff := true
      if diff then out := "the active window is not drawn as it draws itself" :: out
  return out.reverse

/-! ## Random sessions -/

abbrev Rnd := StateM StdGen

def rnd (lo hi : Nat) : Rnd Nat := modifyGet fun g => randNat g lo (max lo hi)
def chance (pct : Nat) : Rnd Bool := return (← rnd 0 99) < pct
def oneOf {β : Type} [Inhabited β] (xs : Array β) : Rnd β := return xs[← rnd 0 (xs.size - 1)]!
def rndInt (lo hi : Int) : Rnd Int := return lo + (← rnd 0 (hi - lo).toNat)

def chars : Array Char := "abcxyzABCXYZ019 ~-_é中─".toList.toArray

def genKey : Rnd KeyEvent := do
  let mods : Modifiers ← oneOf #[{}, {}, {}, {}, { shift := true }, { ctrl := true }, { alt := true },
    { shift := true, ctrl := true }]
  let key : Key ← match ← rnd 0 22 with
    | 0 | 1 => pure .tab | 2 => pure .enter | 3 => pure .escape | 4 => pure .backspace
    | 5 => pure .delete | 6 => pure .left | 7 => pure .right | 8 => pure .up | 9 => pure .down
    | 10 => pure .home | 11 => pure .end | 12 => pure .pageUp | 13 => pure .pageDown | 14 => pure .insert
    | 15 | 16 => pure (.f (← rnd 1 10))
    | _ => pure (.char (← oneOf chars))
  return ⟨key, mods⟩

/-- A point on a screen of size `s`, often on an interesting part of some window. -/
def genPoint (st : AppState Cmd) : Rnd Point := do
  let p ← genPoint' st
  return ⟨max p.x 0, max p.y 0⟩  -- terminals report no negative positions
where genPoint' (st : AppState Cmd) : Rnd Point := do
  let ws := st.desktop.windows
  if ws.isEmpty || (← chance 30) then
    return ⟨← rndInt 0 (st.screen.w + 1), ← rndInt 0 (st.screen.h + 1)⟩
  -- Prefer the active window.
  let i ← if ← chance 60 then pure (ws.size - 1) else rnd 0 (ws.size - 1)
  let w := ws[i]!
  let b := w.bounds
  let inX : Rnd Int := rndInt b.x (b.right - 1)
  let inY : Rnd Int := rndInt b.y (b.bottom - 1)
  match ← rnd 0 7 with
  | 0 | 1 => return ⟨← inX, b.y⟩                              -- title bar
  | 2 => return ⟨b.x + (← rndInt 2 4), b.y⟩                   -- close icon
  | 3 => return ⟨b.right - (← rndInt 3 5), b.y⟩               -- zoom icon
  | 4 => return ⟨b.right - 1, b.bottom - 1⟩                    -- resize corner
  | 5 => return ⟨b.right - 1, ← inY⟩                           -- right edge (scroll bar)
  | 6 => return ⟨← inX, b.bottom - 1⟩                          -- bottom edge (scroll bar)
  | _ => return ⟨← inX, ← inY⟩                                 -- interior

def mouse (pos : Point) (button : MouseButton) (action : MouseAction) : Event :=
  .mouse { pos, button, action }

/-- A gesture: a click, a drag, a wheel turn, a key press, a resize, … -/
def genGesture (st : AppState Cmd) : Rnd (List Event) := do
  let n ← rnd 0 99
  if n < 45 then return [.key (← genKey)]
  if n < 57 then
    let p ← genPoint st
    let b ← oneOf #[MouseButton.left, .left, .left, .right]
    return [mouse p b .press, mouse p b .release]
  if n < 60 then
    -- A double click.
    let p ← genPoint st
    return [mouse p .left .press, mouse p .left .release, mouse p .left .press, mouse p .left .release]
  if n < 82 then
    -- Press, drag around (possibly far off), release (sometimes lost).
    let p ← genPoint st
    let mut evs := [mouse p .left .press]
    let mut q := p
    for _ in [0:← rnd 1 6] do
      q ← if ← chance 50 then pure (q + ⟨← rndInt (-6) 6, ← rndInt (-3) 3⟩) else genPoint st
      q := ⟨max q.x 0, max q.y 0⟩
      evs := evs ++ [mouse q .left .drag]
    if ← chance 90 then evs := evs ++ [mouse q .left .release]
    return evs
  if n < 88 then return [mouse (← genPoint st) .none (← oneOf #[MouseAction.wheelUp, .wheelDown])]
  if n < 92 then return [mouse (← genPoint st) .none .move]
  if n < 97 then
    -- Keyboard move/resize: Ctrl-F5, some arrows, then Enter or Escape.
    let mut evs : List Event := [.key ⟨.f 5, { ctrl := true }⟩]
    for _ in [0:← rnd 1 12] do
      let k ← oneOf #[Key.left, .right, .up, .down]
      let mods ← oneOf #[({} : Modifiers), { shift := true }, { ctrl := true }, { shift := true, ctrl := true }]
      evs := evs ++ [.key ⟨k, mods⟩]
    return evs ++ [.key (.plain (← oneOf #[Key.enter, .escape]))]
  let w ← if ← chance 20 then rnd 0 12 else rnd 20 140
  let h ← if ← chance 20 then rnd 0 6 else rnd 8 50
  return [.resize w h]

/-! ## Running and shrinking -/

def showEvent : Event → String
  | .key k =>
    let m := k.mods
    s!"key {if m.ctrl then "Ctrl+" else ""}{if m.alt then "Alt+" else ""}{if m.shift then "Shift+" else ""}{repr k.key}"
  | .mouse m => s!"mouse {repr m.action} {repr m.button} at ({m.pos.x}, {m.pos.y})"
  | .resize w h => s!"resize {w}x{h}"

/-- Plays `evs` from the initial state; the first violation, if any, with its position. -/
def replay (evs : Array Event) : IO (Option (Nat × List String)) := do
  let mut st := initial 80 25
  for h : i in [0:evs.size] do
    let before := st
    st := (← ((App.handleEvent evs[i]).run app).run st).2
    st := { st with quit := false }
    let errs ← issues before evs[i] st
    unless errs.isEmpty do return some (i, errs)
  return none

/-- Removes chunks of events while the failure (same first message) persists. -/
def shrink (evs : Array Event) (msg : String) : IO (Array Event) := do
  let fails (xs : Array Event) : IO Bool := do
    return match ← replay xs with
      | some (_, e :: _) => e == msg
      | _ => false
  let mut evs := evs
  let mut chunk := evs.size / 2
  while chunk > 0 do
    let mut i := 0
    while i < evs.size do
      let cand := evs.extract 0 i ++ evs.extract (i + chunk) evs.size
      if ← fails cand then evs := cand else i := i + chunk
    chunk := chunk / 2
  return evs

/-- Runs `sessions` random sessions of `length` gestures each, from `seed`. -/
def fuzz (seed sessions length : Nat) : IO Unit := do
  for s in [0:sessions] do
    let mut g := mkStdGen (seed + s)
    let mut st := initial 80 25
    let mut trace : Array Event := #[]
    for _ in [0:length] do
      let (evs, g') := (genGesture st).run g
      g := g'
      for ev in evs do
        let before := st
        st := (← ((App.handleEvent ev).run app).run st).2
        st := { st with quit := false }
        trace := trace.push ev
        let errs ← issues before ev st
        if let e :: _ := errs then
          let small ← shrink trace e
          throw <| IO.userError <| s!"session {seed + s}: {e}\nafter {small.size} events:\n  " ++
            "\n  ".intercalate (small.toList.map showEvent)

end HyperVisionTests.Fuzz
