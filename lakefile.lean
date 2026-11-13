import Lake
open Lake DSL

package «legal-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"

@[default_target]
lean_lib «LegalLean» where
  roots := #[`LegalLean]

@[default_target]
lean_exe «axiomguard» where
  root := `LegalLean.AxiomGuard
  supportInterpreter := true
