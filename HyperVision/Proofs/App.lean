import HyperVision.App
import HyperVision.Proofs.Draw

/-!
# Application-level drawing theorems
-/

namespace HyperVision

open DrawM Draw

namespace App

variable {α : Type}

/-! ## Background jobs

The event loop is effectful, so these theorems pin down the *pure* algebra the loop
relies on: how a handler's result is built and what command a finished job delivers.
The behavioural end (spawning, delivery, error routing) is exercised headlessly in
`HyperVisionTests.Unit`.
-/

/-- A handler that returns a bare desktop (through the coercion) spawns no jobs, and
keeps the desktop it returned. So a handler written the old way behaves exactly as
before: the loop starts nothing and the desktop is set to the returned one. -/
@[simp] theorem coe_desktop (d : Desktop α) : (↑d : Handled α).desktop = d := rfl
@[simp] theorem coe_jobs (d : Desktop α) : (↑d : Handled α).jobs = #[] := rfl

/-- Spawning a job records the job but never changes the desktop, so a handler updates
the desktop and starts work in the same step without one affecting the other. -/
@[simp] theorem spawn_desktop (d : Desktop α) (j : Job α) : (d.spawn j).desktop = d := rfl
@[simp] theorem spawn_jobs (d : Desktop α) (j : Job α) : (d.spawn j).jobs = #[j] := rfl

@[simp] theorem handled_spawn_desktop (h : Handled α) (j : Job α) :
    (h.spawn j).desktop = h.desktop := rfl
@[simp] theorem handled_spawn_jobs (h : Handled α) (j : Job α) :
    (h.spawn j).jobs = h.jobs.push j := rfl

/-- **Results route correctly.** A finished job delivers the command its action
produced on success, and `onError` applied to the exception on failure — nothing else.
This is the value the loop dispatches through `applyUser`, so a successful job reaches
the app as its own `α` and a failed one as a value it can react to. -/
@[simp] theorem deliver_ok (rj : RunningJob α) (a : α) : rj.deliver (.ok a) = a := rfl
@[simp] theorem deliver_error (rj : RunningJob α) (e : IO.Error) :
    rj.deliver (.error e) = rj.onError e := rfl

/-- The command delivered is always one of the two the job declared: either the value
its action computed, or its `onError` of some exception. There is no third outcome. -/
theorem deliver_cases (rj : RunningJob α) (res : Except IO.Error α) :
    (∃ a, res = .ok a ∧ rj.deliver res = a) ∨
    (∃ e, res = .error e ∧ rj.deliver res = rj.onError e) := by
  cases res with
  | ok a => exact .inl ⟨a, rfl, rfl⟩
  | error e => exact .inr ⟨e, rfl, rfl⟩

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
