import HyperVision.App
import HyperVision.Proofs.Draw

/-!
# Application-level drawing theorems
-/

namespace HyperVision

open DrawM Draw

namespace App

variable {α : Type}

/-- The desktop layer (background, windows and their shadows) only changes the
desktop area. -/
theorem drawDesktop_changesOnly (t : Theme) (d : Desktop α) (desk : Rect) :
    Sat (ChangesOnly fun vp p => (desk.translate vp.origin).contains p) (drawDesktop t d desk) :=
  Sat.bind (ChangesOnly.isPreorder _) (fill_paints _ _ _).changesOnly
    fun _ => clip_changesOnly _ _

/-- Windows, their shadows and the desktop background never draw over the menu bar
(top row) or the status line (bottom row). -/
theorem drawDesktop_keeps_bars (t : Theme) (d : Desktop α) (scr : Screen) (x : Int) :
    let size : Size := ⟨scr.width, scr.height⟩
    let s' := Draw.run scr (drawDesktop t d (desktopRect size))
    s'.get? x 0 = scr.get? x 0 ∧ s'.get? x (scr.height - 1) = scr.get? x (scr.height - 1) := by
  intro size s'
  have h := drawDesktop_changesOnly t d (desktopRect size) ⟨Point.origin, scr.bounds⟩ scr
  refine ⟨h.2.2 x 0 ?_, h.2.2 x _ ?_⟩ <;>
    simp [Rect.contains_iff, Rect.translate, desktopRect, Point.origin, size] <;> omega

end App

end HyperVision
