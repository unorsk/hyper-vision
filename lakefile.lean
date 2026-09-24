import Lake
open System Lake DSL

package «hyper-vision» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "tests"

require plausible from git "https://github.com/leanprover-community/plausible" @ "v4.34.0"

input_file hv_term.c where
  path := "c" / "hv_term.c"
  text := true

target hv_term.o pkg : FilePath := do
  let src ← hv_term.c.fetch
  let oFile := pkg.buildDir / "c" / "hv_term.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile src weakArgs #["-fPIC", "-O2", "-Wall"] "cc" getLeanTrace

target libhvterm pkg : FilePath := do
  let o ← hv_term.o.fetch
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "hvterm") #[o]

lean_lib HyperVision where
  moreLinkObjs := #[libhvterm]

/-- Unit and property tests (checked at compile time) and the application fuzzer. -/
lean_lib HyperVisionTests

/-- `lake test [-- seed sessions length]`: builds the tests, then fuzzes the application. -/
lean_exe tests where
  root := `HyperVisionTests.Main

@[default_target]
lean_exe «hyper-vision-demo» where
  root := `Main

