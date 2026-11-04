import Lake
open Lake DSL
package thermalFinite where
  moreLeanArgs := #["-j1", "-M6144"]
  leanOptions := #[⟨`autoImplicit,false⟩,⟨`maxRecDepth,.ofNat 100000⟩,⟨`maxHeartbeats,.ofNat 4000000⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "56a005855ea17e0b0958f73ec801ae140b0a1679"
@[default_target]
lean_lib Thermal where
  roots := #[`Thermal.Audit]
  globs := #[`Thermal.+]
lean_lib Challenge
lean_lib Solution
