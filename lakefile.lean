import Lake
open System Lake DSL

package «hyper-vision» where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  testDriver := "HyperVisionTests"

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

/-- Compile-time `#guard` checks; run with `lake test`. -/
lean_lib HyperVisionTests

@[default_target]
lean_exe «hyper-vision-demo» where
  root := `Main
