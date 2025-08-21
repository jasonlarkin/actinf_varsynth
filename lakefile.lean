import Lake
open Lake DSL

package «actinf_varsynth» where
  -- add package configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"

lean_lib «ActinfVarsynth» where
  -- add library configuration options here

@[default_target]
lean_exe «actinf_varsynth» where
  root := `Main

-- Add Langevin simulator executable
lean_exe «langevin_simulator» where
  root := `src.langevin_simulator
  supportInterpreter := true
