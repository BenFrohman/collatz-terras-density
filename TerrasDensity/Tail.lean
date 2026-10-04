/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Author: Benjamin Stanley Frohman
License: Apache-2.0

Pascal tail for the Terras count. Not a covering claim.
-/

namespace TerrasDensity

def tail : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => 2 ^ (n + 1)
  | n + 1, s + 1 => tail n s + tail n (s + 1)

theorem two_pow_le_three_pow (n : Nat) : 2 ^ n ≤ 3 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    calc
      2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]
      _ ≤ 3 * 2 ^ n := Nat.mul_le_mul_right _ (by decide)
      _ ≤ 3 * 3 ^ n := Nat.mul_le_mul_left _ ih
      _ = 3 ^ (n + 1) := by rw [Nat.pow_succ]

theorem tail_le (n s : Nat) : tail n s * 2 ^ s ≤ 3 ^ n := by
  induction n generalizing s with
  | zero =>
    cases s <;> simp [tail]
  | succ n ih =>
    cases s with
    | zero => simpa [tail] using two_pow_le_three_pow (n + 1)
    | succ s =>
      have h1 := ih s
      have h2 := ih (s + 1)
      have hsplit : tail (n + 1) (s + 1) * 2 ^ (s + 1)
          = tail n s * 2 ^ (s + 1) + tail n (s + 1) * 2 ^ (s + 1) := by
        simp [tail, Nat.add_mul]
      have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [Nat.pow_succ]
      have hfirst : tail n s * 2 ^ (s + 1) ≤ 2 * 3 ^ n := by
        rw [hpow, ← Nat.mul_assoc]
        exact Nat.mul_le_mul_left 2 h1
      have hsum : tail n s * 2 ^ (s + 1) + tail n (s + 1) * 2 ^ (s + 1)
          ≤ 2 * 3 ^ n + 3 ^ n := Nat.add_le_add hfirst h2
      have hthree : 2 * 3 ^ n + 3 ^ n = 3 ^ (n + 1) := by
        rw [Nat.pow_succ]
        omega
      exact le_trans (le_of_eq hsplit) (le_trans hsum (le_of_eq hthree))

end TerrasDensity
