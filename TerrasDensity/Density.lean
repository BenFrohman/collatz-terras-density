/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Author: Benjamin Stanley Frohman
License: Apache-2.0

DensityZero NeverDrops is the Terras statement. It is not RemainingLemma.
-/

import TerrasDensity.Basic
import TerrasDensity.Covering

namespace TerrasDensity

/-- Every non-dropping `n ≤ X` sits in a list of length `o(X)`. -/
def DensityZero (P : Nat → Prop) : Prop :=
  ∀ c : Nat, 0 < c →
    ∃ N : Nat, ∀ X : Nat, N ≤ X →
      ∃ bad : List Nat,
        (∀ n, n ≤ X → P n → n ∈ bad) ∧ bad.length * c ≤ X + 1

/-- Terras–Everett statement. Not proved by the one-step inclusion. -/
def densityZeroNeverDrops : Prop :=
  DensityZero NeverDrops

/-- The covering assumption implies the density statement, because arrival at 1
    is a descent for `n > 1`. This uses the axiom. It does not discharge it. -/
theorem density_of_covering (h : RemainingLemma) : densityZeroNeverDrops := by
  intro c hc
  refine ⟨1, ?_⟩
  intro X _
  refine ⟨[0, 1], ?_, by omega⟩
  intro n hn hnever
  have htree := h n (by omega)
  rcases htree with ⟨k, hk⟩
  have hk0 : 0 < k := by
    cases k with
    | zero => simp [iter] at hk; omega
    | succ _ => exact Nat.succ_pos _
  have hlt : iter k n < n := by
    rw [hk]
    have : n ≠ 0 := by omega
    have : n ≠ 1 := by
      intro h1
      simp [h1, NeverDrops, iter] at hnever
    omega
  exact False.elim (Nat.not_le_of_gt hlt (hnever k hk0))

theorem density_from_assumption : densityZeroNeverDrops :=
  density_of_covering remaining_lemma_assumption

end TerrasDensity
