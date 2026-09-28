import HyperVision

/-!
# File dialog tests

Wildcards, sort order, path resolution, list navigation and type-ahead, keeping the
name field and the information pane in step with the list, and complete sessions
through the application loop against a real directory tree.
-/

namespace HyperVisionTests.FileDialogTests

open HyperVision

def check (ok : Bool) (msg : String) : IO Unit := unless ok do throw (IO.userError msg)

/-! ## Wildcards -/

#guard globMatch "*.lean".toList "Main.lean".toList
#guard !globMatch "*.lean".toList "Main.leanx".toList
#guard globMatch "?ain.*".toList "Main.lean".toList
#guard globMatch "*".toList [] && !globMatch "?".toList []
#guard globMatch "a*b*c".toList "aXbYbZc".toList && !globMatch "a*b*c".toList "aXbYbZ".toList
#guard matchesWildcard "*.lean; *.md" "README.md" && !matchesWildcard "*.lean; *.md" "lakefile.toml"
#guard !matchesWildcard "" "anything" && !matchesWildcard " ; " "anything"
#guard isWild "src/*.lean" && isWild "a?" && !isWild "Main.lean"

/-! ## Order: files, then directories, then `..`, each by name -/

#guard (FileEntry.sort #[.parent, { name := "b", isDir := true }, { name := "z" },
    { name := "a", isDir := true }, { name := "c" }]).map (·.display) ==
  #["c", "z", "a/", "b/", "../"]

/-! ## Paths -/

#guard FileDialog.normalize "/a/./b//c/../d/" == "/a/b/d"
#guard FileDialog.normalize "/../.." == "/" && FileDialog.normalize "" == "/"
#guard FileDialog.resolve "/home/me" "../you/x.txt" == "/home/you/x.txt"
#guard FileDialog.resolve "/home/me" "/etc/hosts" == "/etc/hosts"
#guard FileDialog.resolve "/" "etc" == "/etc"
#guard FileDialog.splitLast "/home/me/*.lean" == ("/home/me", "*.lean")
#guard FileDialog.splitLast "/x" == ("/", "x") && FileDialog.splitLast "/" == ("/", "")

/-! ## Navigation (8 rows of 2 columns) -/

def numbered (n : Nat) : FileList :=
  { dir := "/d", entries := (List.range n).toArray.map fun i => { name := s!"f{i}" } }

def sz : Size := ⟨31, 9⟩

def press (l : FileList) (k : KeyEvent) : FileList := (l.handleKey sz k).1

#guard (press (numbered 40) (.plain .down)).focused == 1
-- Right moves a column; the view scrolls by whole columns.
#guard (press (numbered 40) (.plain .right)).focused == 8
#guard ((numbered 40).focusItem sz 17).top == 8
#guard (((numbered 40).focusItem sz 17).focusItem sz 3).top == 0
-- Focusing is clamped to the list.
#guard ((numbered 40).focusItem sz 100).focused == 39 && ((numbered 40).focusItem sz (-5)).focused == 0
#guard ((numbered 0).focusItem sz 5).focused == 0
-- Ctrl-PgDn/Ctrl-PgUp go to the ends; Home/End to the first/last entry shown.
#guard (press (numbered 40) ⟨.pageDown, { ctrl := true }⟩).focused == 39
-- (Page Down from the top focuses entry 16 in the second column shown, so the view starts at 8.)
#guard (press (press (numbered 40) (.plain .pageDown)) (.plain .home)).focused == 8
#guard (press (numbered 40) (.plain .end)).focused == 15
-- Space (like a double click) activates the focused entry.
#guard match ((numbered 3).handleKey sz (.plain (.char ' '))).2 with | .activated => true | _ => false

/-! ## Type-ahead -/

def named : FileList :=
  { dir := "/d", entries := FileEntry.sort #[{ name := "alpha" }, { name := "beta" }, { name := "Bravo" },
      { name := "charlie" }, { name := "src", isDir := true }] }

def focusedName (l : FileList) : Option String := l.focusedEntry?.map (·.name)

-- Matching ignores case; each letter narrows the prefix; a letter that matches nothing is dropped.
#guard focusedName (press named (.plain (.char 'b'))) == some "Bravo"
#guard focusedName (press (press named (.plain (.char 'b'))) (.plain (.char 'e'))) == some "beta"
#guard focusedName (press (press (press named (.plain (.char 'b'))) (.plain (.char 'e')))
  (.plain (.char 'x'))) == some "beta"
#guard focusedName (press (press (press named (.plain (.char 'b'))) (.plain (.char 'e')))
  (.plain .backspace)) == some "Bravo"
#guard focusedName (press named (.plain (.char 's'))) == some "src"
-- Moving the focus ends the search.
#guard (press (press named (.plain (.char 'b'))) (.plain .down)).search == ""

/-! ## The name field and the information pane follow the list -/

def dialog : Window Unit :=
  FileDialog.make "Open" () "/d" "*.txt"
    (FileEntry.sort #[{ name := "a.txt", size := 3 }, { name := "sub", isDir := true }, .parent])

def field (w : Window Unit) : Option String := (w.control? FileDialog.nameField).bind (·.text?)

def info (w : Window Unit) : Option FileInfo :=
  w.controls.findSome? fun c => match c.kind with | .fileInfo i => some i | _ => none

def keys (w : Window Unit) (ks : List KeyEvent) : Window Unit := ks.foldl (fun w k => (w.handleKey k).1) w

def typed' (text : String) : List KeyEvent := text.toList.map fun c => .plain (.char c)

-- The field starts with the wildcard (selected, so typing replaces it); the pane shows the first entry.
#guard field dialog == some "*.txt"
#guard (info dialog).map (·.path) == some "/d/*.txt"
#guard ((info dialog).bind (·.entry)).map (·.name) == some "a.txt"
#guard (keys dialog [.plain (.char 'x')] |> field) == some "x"
-- Tab to the list, Down: a directory shows as `name/wildcard`, so Open lists it.
#guard field (keys dialog [.plain .tab, .plain .down]) == some "sub/*.txt"
#guard ((info (keys dialog [.plain .tab, .plain .down])).bind (·.entry)).map (·.name) == some "sub"
#guard field (keys dialog [.plain .tab, .plain .down, .plain .down]) == some "../*.txt"
-- Enter on the list presses Open.
#guard match (keys dialog [.plain .tab]).handleKey (.plain .enter) |>.2 with
  | .command (.fileOpen ()) => true
  | _ => false

-- While the name field is being edited, the list (turned with the wheel) leaves it alone;
-- the information pane still follows the list.
#guard
  let w := (keys dialog (typed' "a.t")).mouseControl 3 { pos := ⟨3, 6⟩, button := .none, action := .wheelDown }
  field w.1 == some "a.t" && ((info w.1).bind (·.entry)).map (·.name) == some ".."

-- Regression (fuzzer): double-clicking an entry that was not focused shows it before Open
-- acts on the name field, so Open acts on the entry clicked, not the one focused before.
#guard
  let (w, r) := dialog.mouseControl 3 { pos := ⟨3, 7⟩, button := .left, action := .press, double := true }
  field w == some "sub/*.txt" && match r with | .command (.fileOpen ()) => true | _ => false

/-! ## Complete sessions through the application loop -/

/-- An app whose file dialog command opens a window titled with the chosen path. -/
def app : App Unit :=
  { menuBar := #[], statusLine := #[]
    onCommand := fun _ src d =>
      pure (d.insert (Window.new s!"chosen {((src.bind FileDialog.path?).getD "none")}" ⟨0, 1, 30, 5⟩)) }

def run (st : AppState Unit) (evs : List Event) : IO (AppState Unit) :=
  evs.foldlM (init := st) fun st ev => return (← ((App.handleEvent ev).run app).run st).2

def key (k : Key) (mods : Modifiers := {}) : Event := .key ⟨k, mods⟩

def typed (s : String) : List Event := s.toList.map fun c => key (.char c)

def topTitle (st : AppState Unit) : String := (st.desktop.top?.map (·.title)).getD ""

def listing (st : AppState Unit) : Array String :=
  ((st.desktop.top? >>= FileDialog.list?).map (·.2.entries.map (·.display))).getD #[]

#eval show IO Unit from do
  let root := (← IO.FS.realPath (← IO.FS.createTempDir)).toString
  try
    IO.FS.createDirAll (root ++ "/sub")
    IO.FS.writeFile (root ++ "/a.txt") "a"
    IO.FS.writeFile (root ++ "/b.md") "b"
    IO.FS.writeFile (root ++ "/.hidden.txt") "h"
    IO.FS.writeFile (root ++ "/sub/c.txt") "c"
    let dlg : Window Unit ← Window.fileDialog "Open" () root "*.txt"
    let st₀ : AppState Unit :=
      { desktop := ({ bounds := ⟨0, 1, 80, 23⟩ } : Desktop Unit).insertCentered dlg, screen := ⟨80, 25⟩ }
    -- Matching files, then directories, then `..`; hidden entries are left out.
    check (listing st₀ == #["a.txt", "sub/", "../"]) s!"listing {listing st₀}"
    -- Into `sub` from the list, then choose its file: the dialog closes and the app gets the path.
    let st ← run st₀ [key .tab, key .down, key .enter]
    check (listing st == #["c.txt", "../"]) s!"listing of sub {listing st}"
    let st ← run st [key .enter]
    check (topTitle st == s!"chosen {root}/sub/c.txt") s!"chosen {topTitle st}"
    check (!st.desktop.windows.any (·.title == "Open")) "the dialog stayed open"
    -- A wildcard typed into the name field lists the matching files.
    let st ← run st₀ (typed "*.md" ++ [key .enter])
    check (listing st == #["b.md", "sub/", "../"]) s!"listing of *.md {listing st}"
    -- `..` and a path typed with a directory part.
    let st ← run st₀ (typed "sub/../sub/*" ++ [key .enter])
    check (listing st == #["c.txt", "../"]) s!"listing of sub/* {listing st}"
    -- A double click on a directory opens it.
    let some w := st₀.desktop.top? | throw (IO.userError "no dialog")
    let (x, y) := (w.bounds.x + 3, w.bounds.y + 7)   -- second row of the list: `sub/`
    let click (a : MouseAction) : Event := .mouse { pos := ⟨x, y⟩, button := .left, action := a }
    let st ← run st₀ [click .press, click .release, click .press, click .release]
    check (listing st == #["c.txt", "../"]) s!"double click {listing st}"
    -- Regression (fuzzer): a double click that chooses a file closes the dialog during the
    -- second press; the mouse capture ends with it.
    let file (a : MouseAction) : Event := .mouse { pos := ⟨x, y - 1⟩, button := .left, action := a }
    let st ← run st₀ [file .press, file .release, file .press]
    check (topTitle st == s!"chosen {root}/a.txt") s!"double click on a file: {topTitle st}"
    check (st.capture == .none) "the capture outlived the dialog"
    -- A directory that does not exist is refused with a message.
    let st ← run st₀ (typed "/no/such/dir/x" ++ [key .enter])
    check (topTitle st == "Error") s!"no error box: {topTitle st}"
    -- Escape cancels.
    let st ← run st₀ [key .escape]
    check st.desktop.windows.isEmpty "Escape did not close the dialog"
  finally
    IO.FS.removeDirAll root

end HyperVisionTests.FileDialogTests
