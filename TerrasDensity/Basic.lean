/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Author: Benjamin Stanley Frohman
License: Apache-2.0

Stopping time only. No reverse-tree covering claim.
-/

namespace TerrasDensity

def T (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def iter (k n : Nat) : Nat :=
  match k with
  | 0 => n
  | k + 1 => T (iter k n)

def FiniteStoppingTime (n : Nat) : Prop :=
  ∃ k : Nat, 0 < k ∧ iter k n < n

def NeverDrops (n : Nat) : Prop :=
  ∀ k : Nat, 0 < k → n ≤ iter k n

theorem not_neverDrops_iff (n : Nat) :
    ¬ NeverDrops n ↔ FiniteStoppingTime n := by
  constructor
  · intro h
    by_cases h0 : ∃ k, 0 < k ∧ iter k n < n
    · exact h0
    · exact False.elim (h (by
        intro k hk
        have : ¬ iter k n < n := by
          intro hlt
          exact h0 ⟨k, hk, hlt⟩
        omega))
  · intro h hn
    rcases h with ⟨k, hk, hlt⟩
    exact Nat.not_le_of_gt hlt (hn k hk)

end TerrasDensity
