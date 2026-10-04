/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Author: Benjamin Stanley Frohman
License: Apache-2.0

Pascal tail for the Terras count. Not a covering claim.
`Nat.pow_succ` is `a ^ (n + 1) = a ^ n * a`.
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
      2 ^ (n + 1) = 2 ^ n * 2 := by rw [Nat.pow_succ]
      _ ≤ 3 ^ n * 2 := Nat.mul_le_mul_right _ ih
      _ ≤ 3 ^ n * 3 := Nat.mul_le_mul_left _ (by decide)
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
      have hpow : 2 ^ (s + 1) = 2 ^ s * 2 := by rw [Nat.pow_succ]
      have hfirst : tail n s * 2 ^ (s + 1) ≤ 3 ^ n * 2 := by
        rw [hpow]
        calc
          tail n s * (2 ^ s * 2) = tail n s * 2 ^ s * 2 := by rw [Nat.mul_assoc]
          _ ≤ 3 ^ n * 2 := Nat.mul_le_mul_right 2 h1
      have hsum : tail n s * 2 ^ (s + 1) + tail n (s + 1) * 2 ^ (s + 1)
          ≤ 3 ^ n * 2 + 3 ^ n := Nat.add_le_add hfirst h2
      have hthree : 3 ^ n * 2 + 3 ^ n = 3 ^ (n + 1) := by
        rw [Nat.pow_succ]
        omega
      exact Nat.le_trans (Nat.le_of_eq hsplit) (Nat.le_trans hsum (Nat.le_of_eq hthree))

end TerrasDensity
