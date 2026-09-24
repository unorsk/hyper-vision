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

end HyperVisionTests
