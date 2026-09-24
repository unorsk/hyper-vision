import HyperVision

/-!
# hyper-vision demo

A Turbo Vision style desktop: menu bar with drop-downs and a sub-menu, status
line, a text editor window and a dialog with every kind of control.
-/

open HyperVision

/-- The demo's own commands; everything else uses the built-in `Command`s. -/
inductive DemoCmd where
  | newEditor
  | openControls
  | about
  | showValues
  | insert (text : String)
deriving BEq, Repr, Inhabited

abbrev Cmd := Command DemoCmd

def sampleCode : String :=
"-- Welcome to hyper-vision: Turbo Vision for Lean 4.

import HyperVision
open HyperVision

def main : IO Unit :=
  demoApp.run #[helloWindow, controlsDialog]

-- Things to try:
--   * drag a window by its title bar
--   * resize it from the bottom-right corner
--   * double-click a title bar to zoom
--   * F10 or a click opens the menus
--   * Tab / Shift-Tab walk through a dialog
--   * Alt+letter jumps to a control"

def languages : Array String :=
  #["Lean 4", "Turbo Pascal", "C++", "Haskell", "OCaml", "Rust", "Modula-2", "Oberon"]

def controlsDialog : Window DemoCmd :=
  Window.dialog "Controls" ⟨28, 2, 50, 20⟩ #[
    Control.label 1 1 "~N~ame" (some "name"),
    Control.inputLine "name" 13 1 32 "Anders Hejlsberg",
    Control.label 1 3 "~L~anguage" (some "lang"),
    Control.comboBox "lang" 13 3 24 languages "Turbo Pascal",
    Control.label 1 5 "~S~tyle" (some "style"),
    Control.checkBoxes "style" ⟨2, 6, 20, 3⟩ #["~B~old", "~I~talic", "~U~nderline"] #[true, false, true],
    Control.label 24 5 "Si~z~e" (some "size"),
    Control.radioButtons "size" ⟨25, 6, 21, 3⟩ #["Sm~a~ll", "~M~edium", "La~r~ge"] 1,
    Control.label 1 10 "No~t~es" (some "notes"),
    Control.memo "notes" ⟨2, 11, 44, 4⟩
      "A multi-line memo.\nArrows, Shift+arrows, mouse drag\nto select, Enter for new lines.\nIt scrolls, too.\nLine five.\nLine six.",
    Control.button 10 16 12 "~O~K" (.user .showValues) (isDefault := true),
    Control.button 25 16 12 "Cancel" .cancel ]

def helloWindow : Window DemoCmd :=
  Window.editorWindow "Hello.lean" ⟨1, 2, 46, 16⟩ sampleCode

def aboutBox : Window DemoCmd :=
  Window.messageBox "About"
    "^CHyper Vision\n^CTurbo Vision for Lean 4\n\n^CWindows, menus, dialogs,\n^Cand DOS-era colors."

def menuBar : Array (Menu DemoCmd) := #[
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
    MenuItem.item "Cu~t~" .quit (some ⟨.delete, { shift := true }⟩) (enabled := false),
    MenuItem.item "~C~opy" .quit (some ⟨.insert, { ctrl := true }⟩) (enabled := false),
    MenuItem.item "~P~aste" .quit (some ⟨.insert, { shift := true }⟩) (enabled := false),
    .separator,
    MenuItem.sub "~I~nsert" #[
      MenuItem.item "~G~reeting" (.user (.insert "Hello from hyper-vision!")),
      MenuItem.item "~L~orem ipsum" (.user (.insert "Lorem ipsum dolor sit amet,\nconsectetur adipiscing elit.")),
      MenuItem.item "~B~ox" (.user (.insert "┌──────┐\n│ Lean │\n└──────┘"))]],
  Menu.new "~W~indow" #[
    MenuItem.item "~T~ile" .tile,
    MenuItem.item "C~a~scade" .cascade,
    .separator,
    MenuItem.item "~S~ize/move" .resize (some ⟨.f 5, { ctrl := true }⟩),
    MenuItem.item "~Z~oom" .zoom (some (KeyEvent.plain (.f 5))),
    MenuItem.item "~N~ext" .nextWindow (some (KeyEvent.plain (.f 6))),
    MenuItem.item "~P~revious" .prevWindow (some ⟨.f 6, { shift := true }⟩),
    MenuItem.item "~C~lose" .close (some ⟨.f 3, { alt := true }⟩)],
  Menu.new "~H~elp" #[
    MenuItem.item "~A~bout..." (.user .about)]]

def statusLine : Array (StatusItem DemoCmd) := #[
  StatusItem.new "~Alt-X~ Exit" (KeyEvent.alt 'x') .quit,
  StatusItem.new "~F3~ Controls" (KeyEvent.plain (.f 3)) (.user .openControls),
  StatusItem.new "~F4~ New" (KeyEvent.plain (.f 4)) (.user .newEditor),
  StatusItem.new "~F5~ Zoom" (KeyEvent.plain (.f 5)) .zoom,
  StatusItem.new "~F6~ Next" (KeyEvent.plain (.f 6)) .nextWindow,
  StatusItem.new "~Alt-F3~ Close" ⟨.f 3, { alt := true }⟩ .close,
  StatusItem.new "~F10~ Menu" (KeyEvent.plain (.f 10)) .menu]

/-- A summary of the controls dialog, for the message box shown by `OK`. -/
def summarize (w : Window DemoCmd) : String :=
  let text (n : String) := ((w.control? n).bind (·.text?)).getD ""
  let styles := ((w.control? "style").bind (·.checked?)).getD #[]
  let styleNames := (#["Bold", "Italic", "Underline"].zip styles).filterMap fun (s, on) =>
    if on then some s else none
  let size := ((w.control? "size").bind (·.selected?)).getD 0
  let lines := (text "notes").splitOn "\n" |>.length
  s!"Name:     {text "name"}\nLanguage: {text "lang"}\nStyle:    {", ".intercalate styleNames.toList}\n" ++
  s!"Size:     {#["Small", "Medium", "Large"][size]?.getD "?"}\nNotes:    {lines} lines"

def onCommand (cmd : DemoCmd) (source : Option (Window DemoCmd)) (d : Desktop DemoCmd) :
    IO (Desktop DemoCmd) := do
  match cmd with
  | .about => return d.insertCentered aboutBox
  | .openControls =>
    match d.windows.find? (·.title == "Controls") with
    | some w => return d.raise w.id
    | none => return d.insertCentered controlsDialog
  | .newEditor =>
    let k : Int := d.windows.size
    return d.insert (Window.editorWindow "Untitled.lean" ⟨2 + 2 * k, 2 + k, 40, 12⟩ "")
  | .showValues =>
    match source with
    | some w => return (d.close w.id).insertCentered (Window.messageBox "Values" (summarize w))
    | none => return d
  | .insert text =>
    match d.top? with
    | some w =>
      return d.modify w.id fun w => w.modifyControl "text" fun c => match c.kind with
        | .memo m => { c with kind := .memo (m.insertText text) }
        | _ => c
    | none => return d

def demoApp (mouseCursor : Bool) : App DemoCmd :=
  { menuBar, statusLine, onCommand, mouseCursor }

def main : IO Unit := do
  let mouseCursor := (← IO.getEnv "HV_MOUSE_CURSOR").isSome
  (demoApp mouseCursor).run #[helloWindow, controlsDialog]
