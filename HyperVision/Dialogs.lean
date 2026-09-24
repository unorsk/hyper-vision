import HyperVision.Window

/-!
# Standard dialogs
-/

namespace HyperVision

namespace Window

variable {α : Type}

/--
A modal message box: `text` (lines starting with `^C` are centered) above a
default `OK` button.
-/
def messageBox (title text : String) : Window α :=
  let lines := text.splitOn "\n"
  let textW := lines.foldl (fun acc l => max acc (if l.startsWith "^C" then l.length - 2 else l.length)) 0
  let w := max 32 (textW + 6)
  let h := lines.length + 7
  let controls : Array (Control α) := #[
    Control.staticText ⟨2, 1, w - 6, lines.length⟩ text,
    Control.button ((w - 2 - 12) / 2 : Nat) (h - 5 : Nat) 12 "~O~K" .ok (isDefault := true) ]
  { dialog title ⟨0, 0, w, h⟩ controls with modal := true }

end Window

end HyperVision
