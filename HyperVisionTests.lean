import HyperVision

/-!
# Tests

Checked at compile time with `#guard`; run with `lake test`.
-/

open HyperVision

namespace HyperVisionTests

def decodeStr (s : String) (flush := false) : Array Event × Nat :=
  let (evs, rest) := Input.decode s.toUTF8 flush
  (evs, rest.size)

def keyEv (k : Key) (mods : Modifiers := {}) : Event := .key ⟨k, mods⟩

/-! ## Input decoding -/

#guard decodeStr "a" == (#[keyEv (.char 'a')], 0)
#guard decodeStr "é" == (#[keyEv (.char 'é')], 0)
#guard decodeStr "\x1b[A" == (#[keyEv .up], 0)
#guard decodeStr "\x1b[1;5C" == (#[keyEv .right { ctrl := true }], 0)
#guard decodeStr "\x1b[21~" == (#[keyEv (.f 10)], 0)
#guard decodeStr "\x1b[15;2~" == (#[keyEv (.f 5) { shift := true }], 0)
#guard decodeStr "\x1bOR" == (#[keyEv (.f 3)], 0)
#guard decodeStr "\x1bx" == (#[keyEv (.char 'x') { alt := true }], 0)
#guard decodeStr "\x1b[Z" == (#[keyEv .tab { shift := true }], 0)
#guard decodeStr "\x01" == (#[keyEv (.char 'a') { ctrl := true }], 0)
-- A lone ESC waits for more input unless flushed.
#guard decodeStr "\x1b" == (#[], 1)
#guard decodeStr "\x1b" (flush := true) == (#[keyEv .escape], 0)
-- An incomplete CSI sequence is kept for the next read.
#guard decodeStr "x\x1b[1;5" == (#[keyEv (.char 'x')], 5)
-- SGR mouse reports (1-based on the wire, 0-based in events).
#guard decodeStr "\x1b[<0;10;5M" ==
  (#[.mouse { pos := ⟨9, 4⟩, button := .left, action := .press }], 0)
#guard decodeStr "\x1b[<32;11;5M" ==
  (#[.mouse { pos := ⟨10, 4⟩, button := .left, action := .drag }], 0)
#guard decodeStr "\x1b[<0;11;5m" ==
  (#[.mouse { pos := ⟨10, 4⟩, button := .left, action := .release }], 0)
#guard decodeStr "\x1b[<65;1;1M" ==
  (#[.mouse { pos := ⟨0, 0⟩, button := .middle, action := .wheelDown }], 0)
-- Extra mouse buttons (back/forward) are ignored.
#guard decodeStr "\x1b[<128;1;1M" == (#[], 0)
-- Linux console function keys.
#guard decodeStr "\x1b[[C" == (#[keyEv (.f 3)], 0)
-- C1 control characters are not text.
#guard (KeyEvent.plain (.char (Char.ofNat 0x85))).text? == none
-- Shortcuts ignore case and Shift for Alt/Ctrl letters.
#guard (KeyEvent.alt 'X').triggers (KeyEvent.alt 'x')

/-! ## Text and screen -/

#guard (HotText.parse "~F~ile").plain == "File"
#guard (HotText.parse "E~x~it").hotkey? == some 'x'
#guard (HotText.parse "Plain").hotkey? == none
#guard fitString "abcdef" 3 == "abc" && fitString "ab" 4 == "ab  "

#guard ((Screen.new 4 3).set 3 2 { ch := 'z' }).get? 3 2 == some { ch := 'z' }
#guard ((Screen.new 4 3).set 4 0 { ch := 'z' }).get? 4 0 == none
#guard (Draw.run (Screen.new 10 5) (Draw.within ⟨2, 1, 3, 3⟩ (Draw.putStr 0 0 "hello" {
    fg := .white, bg := .blue }))).get? 5 1 == some { ch := ' ' }

#guard Attr.ofByte 0x1F == ⟨.white, .blue⟩ && (Attr.ofByte 0x1F).toByte == 0x1F

/-! ## Editing -/

#guard ((InputLine.ofString "abc").insert 'd').value == "abcd"
#guard ((InputLine.ofString "abc").selectAll.insert 'x').value == "x"
#guard ((InputLine.ofString "abc").handleKey ⟨20, 1⟩ (.plain .backspace)).1.value == "ab"
-- Letters that double as Ctrl shortcuts are still text without Ctrl.
#guard ((InputLine.ofString "").handleKey ⟨20, 1⟩ (.plain (.char 'a'))).1.value == "a"
#guard ((InputLine.ofString "").handleKey ⟨20, 1⟩ (.plain (.char 'y'))).1.value == "y"
#guard StaticText.wrap 20 "Name:     Wirth" == ["Name:     Wirth"]
#guard StaticText.wrap 10 "one two three" == ["one two", "three"]

#guard (({ Memo.ofString "hello" with cursor := ⟨0, 2⟩ }).newline).text == "he\nllo"
#guard ((({ Memo.ofString "hello" with cursor := ⟨0, 2⟩ }).newline).backspace).text == "hello"
#guard ((Memo.ofString "ab").insertText "x\ny").text == "x\nyab"
#guard (({ Memo.ofString "one two" with cursor := ⟨0, 7⟩ }).wordLeft ⟨0, 7⟩) == ⟨0, 4⟩
-- Page Down stops when the last line reaches the bottom.
#guard ((List.range 3).foldl (fun m _ => (m.handleKey ⟨10, 4⟩ (.plain .pageDown)).1)
  (Memo.ofString "0\n1\n2\n3\n4\n5\n6\n7\n8\n9")).top == 6
-- Tab replaces the selection, then pads to the next tab stop.
def tabMemo : Memo :=
  { Memo.ofString "abcdefgh" with acceptsTab := true, anchor := some ⟨0, 2⟩, cursor := ⟨0, 5⟩ }
#guard (tabMemo.handleKey ⟨20, 4⟩ (.plain .tab)).1.text == "ab  fgh"

/-! ## Layout -/

#guard GrowMode.stretch.apply ⟨1, 1, 10, 5⟩ 4 2 == ⟨1, 1, 14, 7⟩
#guard GrowMode.anchorBottomRight.apply ⟨1, 1, 10, 5⟩ 4 2 == ⟨5, 3, 10, 5⟩
#guard Desktop.mostEqualDivisors 4 == (2, 2)
#guard Desktop.mostEqualDivisors 3 == (3, 1)

def twoWindows : Desktop Unit :=
  ({ bounds := ⟨0, 1, 80, 23⟩ } : Desktop Unit)
    |>.insert (Window.new "A" ⟨0, 1, 20, 10⟩) |>.insert (Window.new "B" ⟨5, 5, 20, 10⟩)

#guard twoWindows.tile.windows.map (·.bounds) == #[⟨0, 1, 40, 23⟩, ⟨40, 1, 40, 23⟩]
#guard twoWindows.cascade.windows.map (·.bounds) == #[⟨0, 1, 80, 23⟩, ⟨1, 2, 79, 22⟩]
#guard twoWindows.windows.map (·.number) == #[some 1, some 2]
#guard (twoWindows.next.top?.map (·.title)) == some "A"
-- Zoom fills the desktop; zooming again restores the previous bounds.
#guard ((twoWindows.toggleZoom 1).find? 1).map (·.bounds) == some ⟨0, 1, 80, 23⟩
#guard (((twoWindows.toggleZoom 1).toggleZoom 1).find? 1).map (·.bounds) == some ⟨0, 1, 20, 10⟩
-- Tiling that would go below a window's minimum size is refused.
#guard (((List.range 25).foldl (fun d _ => d.insert (Window.new "W" ⟨0, 1, 20, 8⟩))
  ({ bounds := ⟨0, 1, 80, 23⟩ } : Desktop Unit)).cascade.windows.map (·.bounds)).all
  (· == ⟨0, 1, 20, 8⟩)
-- Windows cannot be dragged above the desktop or entirely off its right edge.
#guard ((twoWindows.moveTo 2 ⟨200, -5⟩).find? 2).map (·.bounds.origin) == some ⟨79, 1⟩

/-! ## Focus and hot keys -/

def form : Window Unit :=
  Window.dialog "Form" ⟨0, 0, 40, 10⟩ #[
    Control.label 1 1 "~N~ame" (some "name"),
    Control.inputLine "name" 8 1 20 "x",
    Control.checkBoxes "opts" ⟨1, 3, 20, 2⟩ #["~B~old", "~I~talic"],
    Control.button 1 6 10 "~O~K" .ok (isDefault := true)]

#guard form.focus == some 1
#guard (form.focusNext).focus == some 2
#guard (form.focusNext.focusNext.focusNext).focus == some 1
#guard ((form.handleKey (KeyEvent.alt 'i')).1.control? "opts" >>= (·.checked?)) == some #[false, true]
#guard match (form.handleKey (.plain .enter)).2 with
  | .command .ok => true
  | _ => false

-- Shrinking and regrowing a window restores its controls' layout.
#guard
  let w : Window Unit := Window.dialog "D" ⟨0, 0, 50, 10⟩ #[Control.inputLine "i" 13 1 32 "" .stretchX]
  let w' := (w.setBounds ⟨0, 0, 16, 10⟩).setBounds ⟨0, 0, 50, 10⟩
  (w'.control? "i").map w'.boundsOf == some ⟨13, 1, 32, 1⟩

/-! ## Application behaviour (run headlessly) -/

def check (ok : Bool) (msg : String) : IO Unit := unless ok do throw (IO.userError msg)

def runEvents (d : Desktop Unit) (evs : List Event) : IO (AppState Unit) := do
  let app : App Unit := { menuBar := #[], statusLine :=
    #[StatusItem.new "~F4~ New" (KeyEvent.plain (.f 4)) .tile] }
  evs.foldlM (init := { desktop := d, screen := ⟨80, 25⟩ }) fun st ev => do
    return (← ((App.handleEvent ev).run app).run st).2

-- A modal window cannot be escaped through the status line, but can be dismissed.
#eval show IO Unit from do
  let d := twoWindows.insertCentered (Window.messageBox "Note" "Hi")
  let st ← runEvents d [.key (KeyEvent.plain (.f 4))]
  check (st.desktop.top?.map (·.title) == some "Note") "status command escaped a modal window"
  check ((st.desktop.find? 1).map (·.bounds) == some ⟨0, 1, 20, 10⟩) "status command reached the desktop"
  let st ← runEvents st.desktop [.key (KeyEvent.plain .enter)]
  check (st.desktop.top?.map (·.title) == some "B") "Enter did not close the message box"

-- A lost mouse release does not leave a window stuck in the dragging state.
#eval show IO Unit from do
  let press : Event := .mouse { pos := ⟨10, 5⟩, button := .left, action := .press }
  let move : Event := .mouse { pos := ⟨12, 6⟩, button := .none, action := .move }
  let st ← runEvents twoWindows [press, move]
  check (st.capture == .none) "capture survived a lost release"
  check (st.desktop.windows.all (!·.dragging)) "window left in dragging state"

end HyperVisionTests
