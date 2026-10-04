/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Author: Benjamin Stanley Frohman
License: Apache-2.0

DensityZero NeverDrops is the Terras statement. It is not RemainingLemma.
The implication below uses the covering axiom. It does not discharge it.
`1` does not drop below itself, so it is an exception, not a contradiction.
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

/-- The covering assumption implies the density statement. Arrival at 1 is a
    descent only for `n > 1`. `0` and `1` are the exception list. -/
theorem density_of_covering (h : RemainingLemma) : densityZeroNeverDrops := by
  intro c hc
  refine ⟨2 * c, ?_⟩
  intro X hX
  refine ⟨[0, 1], ?_, ?_⟩
  · intro n hn hnever
    have h01 : n = 0 ∨ n = 1 := by
      by_cases h0 : n = 0
      · exact Or.inl h0
      · have hpos : 0 < n := Nat.pos_of_ne_zero h0
        rcases h n hpos with ⟨k, hk⟩
        cases k with
        | zero =>
          right
          simpa [iter] using hk
        | succ k =>
          have hle : n ≤ iter (k + 1) n := hnever (k + 1) (Nat.succ_pos _)
          have : n ≤ 1 := by simpa [hk] using hle
          omega
    rcases h01 with rfl | rfl
    · simp
    · simp
  · have hlen : ([0, 1] : List Nat).length * c = 2 * c := by simp
    omega

theorem density_from_assumption : densityZeroNeverDrops :=
  density_of_covering remaining_lemma_assumption

end TerrasDensity
