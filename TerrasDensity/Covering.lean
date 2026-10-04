/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Author: Benjamin Stanley Frohman
License: Apache-2.0

Vendored covering equation from BenFrohman/collatz-covering-claim.
Same equation, this namespace. An assumption, not a proof.
-/

import TerrasDensity.Basic

namespace TerrasDensity

def InReverseTree (n : Nat) : Prop :=
  ∃ k : Nat, iter k n = 1

def RemainingLemma : Prop :=
  ∀ n : Nat, 0 < n → InReverseTree n

/-- The covering equation. Same statement as collatz-covering-claim. Not proved here. -/
axiom remaining_lemma_assumption : RemainingLemma

theorem covering_from_assumption :
    ∀ n : Nat, 0 < n → InReverseTree n :=
  remaining_lemma_assumption

end TerrasDensity
