import Lake
open Lake DSL

package pnP2023 {
  -- add package configuration options here
}

lean_lib PnP2023 {
  -- add library configuration options here
}

@[default_target]
lean_exe pnP2023 {
  root := `Main
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@ "master"

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"