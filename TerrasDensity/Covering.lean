/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
/-
Vendored covering equation from BenFrohman/collatz-covering-claim.
Same equation, this namespace. An assumption, not a proof.
-/

import TerrasDensity.Basic

namespace TerrasDensity

def InReverseTree (n : Nat) : Prop :=
  ∃ k : Nat, iter k n = 1

def RemainingLemma : Prop :=
  ∀ n : Nat, 0 < n → InReverseTree n

/-- The covering equation, conditional on the named hypothesis `RemainingLemma`
(open; equivalent to Collatz). Same statement as collatz-covering-claim. -/
theorem covering_from_assumption (h : RemainingLemma) :
    ∀ n : Nat, 0 < n → InReverseTree n :=
  h

end TerrasDensity
