import Lake

open Lake DSL

package RKResearch

require verso from git
  "https://github.com/leanprover/verso" @ s!"v{Lean.versionString}"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ s!"v{Lean.versionString}"

@[default_target]
lean_lib RKResearch

lean_exe article where
  root := `Article
