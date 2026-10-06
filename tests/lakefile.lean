import Lake
open System Lake DSL

/-!
The tests are a separate package so that projects depending on `hyper-vision` do not
acquire a transitive dependency on test-only tools (Plausible).
-/

package «hyper-vision-tests» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "tests"

require «hyper-vision» from ".."
require plausible from git "https://github.com/leanprover-community/plausible" @ "v4.34.0"

/-- Unit and property tests (checked at compile time) and the application fuzzer. -/
lean_lib HyperVisionTests

/-- `lake test [-- seed sessions length]`: builds the tests, then fuzzes the application. -/
lean_exe tests where
  root := `HyperVisionTests.Main
