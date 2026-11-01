import Lake
open Lake DSL

package vid_lean

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"

@[default_target]
lean_lib VidLean
