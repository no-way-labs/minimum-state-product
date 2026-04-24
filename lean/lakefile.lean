import Lake
open Lake DSL

package "lean-mn" where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

lean_lib LeanMn where

