import HyperVisionTests

/-!
The test driver (`lake test`). Building it checks the unit tests and property tests
(they run at compile time and fail the build on a counterexample); running it fuzzes
the application, compiled: `lake test -- [seed] [sessions] [length]`.
-/

def main (args : List String) : IO UInt32 := do
  let arg (i d : Nat) := (args[i]? >>= String.toNat?).getD d
  let (seed, sessions, length) := (arg 0 1, arg 1 40, arg 2 250)
  try
    HyperVisionTests.Fuzz.fuzz seed sessions length
    IO.println s!"fuzzing: {sessions} sessions of {length} gestures from seed {seed}: all invariants hold"
    return 0
  catch e =>
    IO.eprintln e
    return 1
