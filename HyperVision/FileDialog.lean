import HyperVision.Dialogs
import Std.Time

/-!
# File dialog

Turbo Vision's `TFileDialog`: a file name field, the sorted list of the files that match
a wildcard together with the subdirectories, a pane with the name, size and date of the
focused entry, and `Open`/`Cancel` buttons.

Moving through the list shows the focused entry in the name field; for a directory it
shows the directory followed by the wildcard (`src/*.lean`). `Open` (or `Enter`, or a
double click on an entry) then acts on the name field:

* a wildcard (`*.md`, `docs/*.txt`) lists the files matching it;
* a directory (`..`, `src/`, `/usr/lib`) is listed;
* anything else is the chosen file: the dialog closes and the application receives the
  command given to `Window.fileDialog`, whose handler reads the file with
  `FileDialog.path?`.

Paths are POSIX paths. Hidden entries (names starting with `.`) are not listed, but can
be typed.
-/

namespace HyperVision

namespace FileDialog

/-! ## Paths -/

/-- Normalizes a path to an absolute one: empty and `.` components are dropped and `..`
removes the component before it (never going above `/`). -/
def normalize (path : String) : String :=
  let comps := (path.splitOn "/").foldl (init := (#[] : Array String)) fun acc c =>
    if c.isEmpty || c == "." then acc else if c == ".." then acc.pop else acc.push c
  "/" ++ "/".intercalate comps.toList

/-- `name` taken relative to the directory `dir` (unless it is absolute), normalized. -/
def resolve (dir name : String) : String :=
  normalize (if name.startsWith "/" then name else joinPath dir name)

/-- The directory and the last component of a normalized path. -/
def splitLast (path : String) : String × String :=
  match (path.splitOn "/").reverse with
  | last :: rest => (normalize ("/".intercalate rest.reverse), last)
  | [] => ("/", "")

/-- `s` without leading and trailing blanks. -/
def trimBlanks (s : String) : String :=
  String.ofList ((s.toList.dropWhile (· == ' ')).reverse.dropWhile (· == ' ')).reverse

/-! ## Reading directories -/

/-- The local time zone, or UTC if it cannot be determined. -/
def localZone : IO Std.Time.TimeZone.ZoneRules :=
  try Std.Time.Database.defaultGetLocalZoneRules
  catch _ => pure (Std.Time.TimeZone.ZoneRules.ofTimeZone Std.Time.TimeZone.UTC)

/-- The local wall-clock time of a file-system timestamp. -/
def localTime (zone : Std.Time.TimeZone.ZoneRules) (t : IO.FS.SystemTime) : FileTime :=
  let stamp := Std.Time.Timestamp.ofSecondsSinceUnixEpoch (.ofInt t.sec)
  let dt := (Std.Time.DateTime.ofTimestamp stamp zone).toPlainDateTime
  { year := dt.year.toInt.toNat, month := dt.month.toNat, day := dt.day.toNat
    hour := dt.hour.toNat, minute := dt.minute.toNat }

/-- The entries of directory `dir`: the files matching `wildcard`, every subdirectory,
and `..` (except at the root), sorted. Hidden entries are left out; an unreadable
directory lists only `..`. -/
def readDirectory (dir wildcard : String) : IO (Array FileEntry) := do
  let zone ← localZone
  let raw ← try System.FilePath.readDir dir catch _ => pure #[]
  -- The wildcard is split once, not once per entry.
  let pats := (wildcardPatterns wildcard).map String.toList
  let mut out : Array FileEntry := #[]
  for e in raw do
    let name := e.fileName
    if name.startsWith "." then continue
    -- `metadata` follows symbolic links, so a link to a directory is listed as one.
    match ← (try some <$> e.path.metadata catch _ => pure none) with
    | some md =>
      if md.type == .dir || matchesPatterns pats name then
        out := out.push { name, isDir := md.type == .dir, size := md.byteSize.toNat
                          modified := some (localTime zone md.modified) }
    | none =>
      -- A dangling link: listed as a file, without size or date.
      if matchesPatterns pats name then out := out.push { name }
  if dir != "/" then out := out.push FileEntry.parent
  return FileEntry.sort out

/-! ## The dialog -/

/-- The name of the file name field. -/
def nameField : String := "fileName"

/-- The name of the file list. -/
def listName : String := "files"

/-- Stick to the right edge. -/
private def right : GrowMode := { loX := true, hiX := true }

/-- The index and state of a window's file list. -/
def list? {α : Type} (w : Window α) : Option (Nat × FileList) :=
  (List.range w.controls.size).findSome? fun i => w.controls[i]?.bind fun c => match c.kind with
    | .fileList l => some (i, l)
    | _ => none

/-- The dialog for directory `dir` with its (sorted) `entries`; `Window.fileDialog`
reads them. It is modal and can be resized; the name field starts out focused, showing
the wildcard. -/
def make {α : Type} (title : String) (onOpen : α) (dir wildcard : String)
    (entries : Array FileEntry) : Window α :=
  let list : FileList := { dir, wildcard, entries, field := nameField }
  let w := Window.dialog title ⟨0, 0, 49, 19⟩ #[
    Control.label 1 1 "~N~ame" (some nameField),
    { name := nameField, bounds := ⟨2, 2, 31, 1⟩, grow := .stretchX
      kind := .inputLine (InputLine.ofString wildcard 1024) },
    Control.label 1 4 "~F~iles" (some listName),
    Control.fileList listName ⟨2, 5, 31, 9⟩ list .stretch,
    Control.button 34 2 11 "~O~pen" (.fileOpen onOpen) (isDefault := true) (grow := right),
    Control.button 34 5 11 "Cancel" .cancel (grow := right),
    Control.fileInfo ⟨0, 15, 47, 2⟩ { loY := true, hiX := true, hiY := true } ]
  -- Show the first entry in the information pane, but keep the wildcard in the field,
  -- selected so that typing replaces it.
  let w := ((list? w).map (w.changed ·.1)).getD w |>.modifyControl nameField fun c => match c.kind with
    | .inputLine i => { c with kind := .inputLine (i.setValue wildcard).selectAll }
    | _ => c
  { w with flags := { WindowFlags.dialog with grow := true }, modal := true }

/-- The file a file dialog accepted: set once its `Open` button chose a file, so the
handler of the dialog's command can read it. -/
def path? {α : Type} (w : Window α) : Option String := (list? w).bind (·.2.chosen)

/-- Lists `dir` in file list `i`, focuses the list and shows its first entry. -/
def openDir {α : Type} (w : Window α) (i : Nat) (l : FileList) (dir wildcard : String) :
    IO (Window α) := do
  let entries ← readDirectory dir wildcard
  let w := w.updateKind i (.fileList (l.load dir wildcard entries))
  return (w.setFocus i).changed i

/-- What `Open` did. -/
inductive Outcome (α : Type) where
  /-- The dialog stays open, possibly listing another directory or wildcard. -/
  | stay (w : Window α)
  /-- A file was chosen; `path?` of the window gives it. -/
  | chosen (w : Window α)
  /-- The name cannot be opened, for the reason given. -/
  | invalid (msg : String)

/-- Acts on the file name field when `Open` is pressed (Turbo Vision's
`TFileDialog::valid`). -/
def accept {α : Type} (w : Window α) : IO (Outcome α) := do
  let some (i, l) := list? w | return .stay w
  let name := trimBlanks (((w.control? l.field).bind (·.text?)).getD "")
  if name.isEmpty then return .stay w
  let path := resolve l.dir name
  let (parent, last) := splitLast path
  if isWild last then
    if ← System.FilePath.isDir parent then return .stay (← openDir w i l parent last)
    return .invalid "Invalid drive or directory"
  if ← System.FilePath.isDir path then return .stay (← openDir w i l path l.wildcard)
  if ← System.FilePath.isDir parent then
    return .chosen (w.updateKind i (.fileList { l with chosen := some path }))
  return .invalid "Invalid drive or directory"

end FileDialog

/--
Turbo Vision's file dialog, listing the directory `dir` (the current directory by
default) with the files that match `wildcard` (patterns such as `*.lean;*.md`).
Choosing a file closes the dialog and issues `.user onOpen` with the dialog as its
source; the handler reads the chosen file with `FileDialog.path?`.
-/
def Window.fileDialog {α : Type} (title : String) (onOpen : α) (dir : String := ".")
    (wildcard : String := "*") : IO (Window α) := do
  let dir := FileDialog.resolve (← IO.currentDir).toString dir
  let dir ← try pure (← IO.FS.realPath dir).toString catch _ => pure dir
  return FileDialog.make title onOpen dir wildcard (← FileDialog.readDirectory dir wildcard)

end HyperVision
