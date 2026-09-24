import HyperVision.Widget

/-!
# Labels and static text
-/

namespace HyperVision

/-- A caption with a hot key that moves the focus to its linked control. -/
structure Label where
  text : HotText
  /-- Name of the control that receives the focus. -/
  link : Option String := none
deriving Inhabited

instance : Widget Label where
  draw l ctx := do
    let c := ctx.theme.dialog
    let attr := if ctx.emphasized then c.labelSelected else c.label
    Draw.hline 0 0 ctx.size.w ' ' attr
    Draw.putHot 1 0 l.text attr c.labelShortcut
  handleMouse l _ m :=
    match l.link with
    | some name => if m.isPress then (l, .focus name) else (l, .handled)
    | none => (l, .ignored)
  focusable _ := false
  hotkey l c :=
    if l.text.hotkey? == some c then l.link.map fun name => (l, .focus name) else none

/-- Read-only text. Lines starting with `^C` are centered. -/
structure StaticText where
  text : String
deriving Inhabited

namespace StaticText

/-- Greedy word wrap of one paragraph to `width` columns; lines that fit are kept as is. -/
def wrap (width : Nat) (para : String) : List String :=
  if width == 0 then [] else
  if para.length ≤ width then [para] else
  let words := (para.splitOn " ").filter (· ≠ "")
  let (lines, cur) := words.foldl (init := ([], "")) fun (acc, cur) w =>
    if cur.isEmpty then (acc, w)
    else if cur.length + 1 + w.length ≤ width then (acc, cur ++ " " ++ w)
    else (cur :: acc, w)
  (cur :: lines).reverse

end StaticText

instance : Widget StaticText where
  draw t ctx := do
    let attr := ctx.theme.dialog.staticText
    Draw.fill ⟨0, 0, ctx.size.w, ctx.size.h⟩ ' ' attr
    let mut y : Nat := 0
    for para in t.text.splitOn "\n" do
      let centered := para.startsWith "^C"
      let body := if centered then String.ofList (para.toList.drop 2) else para
      for line in StaticText.wrap ctx.size.w body do
        let x := if centered then (ctx.size.w - line.length) / 2 else 0
        Draw.putStr x y line attr
        y := y + 1
  focusable _ := false

end HyperVision
