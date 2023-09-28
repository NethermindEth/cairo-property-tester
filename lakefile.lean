import Lake
open Lake DSL

package «property-testing» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require verification from git
  "https://github.com/starkware-libs/formal-proofs.git"/"lean4"

@[default_target]
lean_lib «PropertyTesting» {
  -- add any library configuration options here
}
