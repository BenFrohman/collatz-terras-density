/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Author: Benjamin Stanley Frohman
License: Apache-2.0

Terras inclusion. Not the binomial tail. Not the covering claim.
-/

import TerrasDensity.Basic

namespace TerrasDensity

def Survives (k n : Nat) : Prop :=
  ∀ j : Nat, 0 < j → j ≤ k → n ≤ iter j n

def BadClass (k m : Nat) : Prop :=
  2 ^ k ≤ 3 ^ m

def UnderBound (k m a n : Nat) : Prop :=
  (2 ^ k - 3 ^ m) * n ≤ a

def TerrasInclusion (k n m a : Nat) : Prop :=
  Survives k n →
    iter k n * 2 ^ k = 3 ^ m * n + a →
      BadClass k m ∨ UnderBound k m a n

theorem drop_of_affine (n k m a : Nat)
    (hk : 0 < k) (hpow : 3 ^ m < 2 ^ k)
    (himg : iter k n * 2 ^ k = 3 ^ m * n + a)
    (hbig : a < (2 ^ k - 3 ^ m) * n) :
    iter k n < n := by
  have hmul : iter k n * 2 ^ k < n * 2 ^ k := by
    calc
      iter k n * 2 ^ k = 3 ^ m * n + a := himg
      _ < 3 ^ m * n + (2 ^ k - 3 ^ m) * n := Nat.add_lt_add_left hbig _
      _ = 2 ^ k * n := by
        have hsub : 3 ^ m + (2 ^ k - 3 ^ m) = 2 ^ k := Nat.add_sub_of_le (Nat.le_of_lt hpow)
        rw [Nat.add_mul, hsub]
      _ = n * 2 ^ k := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_right hmul

theorem inclusion_of_affine (k n m a : Nat)
    (hk : 0 < k)
    (himg : iter k n * 2 ^ k = 3 ^ m * n + a)
    (hS : Survives k n) :
    BadClass k m ∨ UnderBound k m a n := by
  by_cases hpow : 3 ^ m < 2 ^ k
  · right
    by_contra hbig
    have hlt : a < (2 ^ k - 3 ^ m) * n := by omega
    have hdrop := drop_of_affine n k m a hk hpow himg hlt
    exact Nat.not_le_of_gt hdrop (hS k hk (Nat.le_refl k))
  · left
    exact hpow

theorem terras_inclusion (k n m a : Nat) (hk : 0 < k) :
    TerrasInclusion k n m a := by
  intro hS himg
  exact inclusion_of_affine k n m a hk himg hS

end TerrasDensity
