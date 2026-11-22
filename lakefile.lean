import Lake
open Lake DSL

package «verified-next-prime» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib «ShortIntervalPrimes»
lean_lib «VerifiedNextPrime»
lean_lib «DeterministicMR»

@[default_target]
lean_exe «nextprime» where
  root := `Main
