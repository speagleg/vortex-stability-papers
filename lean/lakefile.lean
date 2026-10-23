import Lake
open Lake DSL

package vortexpapers where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.34.1"

/-- Paper 1: Montaldi–Tokieda Conjecture 13. -/
lean_lib Conj13 where

/-- Paper 2: finite-core heptagon. -/
lean_lib Heptagon where

/-- Paper 3: vortex rings and rows on the hyperbolic plane. -/
lean_lib HyperbolicRings where
