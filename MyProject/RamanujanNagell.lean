/-
Copyright (c) 2024 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic
/-!
# The Ramanujan-Nagell equation

Stuff

-/
set_option pp.numericTypes true

lemma sq_odd_then_odd :
  ∀ (x : ℤ), Odd (x ^ 2) → Odd (x) := by
  simp [parity_simps]

-- theorem not_even_seven : ¬Even (7 : ℤ) := by decide

theorem not_odd_two_pow (n : ℕ) : n ≠ 0 → ¬Odd ((2 : ℤ) ^ n) := by
  cases n <;> simp [pow_succ]

lemma two_pow_min_seven_odd :
  ∀ (n : ℕ), n ≠ 0 → Odd ( (2 : ℤ) ^ n - (7 : ℤ) ) := by
  intro n h
  rw [@Int.odd_sub (2^n) 7]
  apply iff_of_false
  · exact not_odd_two_pow n h
  · decide

lemma x_is_odd :
  ∀ x : ℤ, ∀ n : ℕ, n ≠ 0 → x ^ 2 + 7 = 2 ^ n →
    x % 2 = 1 := by
    intros x n h' h
    have m : (x^2) = 2^n - 7 := by
      exact eq_tsub_of_add_eq h
    have m₂ : (x ^ 2) % 2 = 1 := by
      rw [m]
      rw [← Int.odd_iff]
      apply two_pow_min_seven_odd n
      exact h'
    rw [← Int.odd_iff]
    rw [← Int.odd_iff] at m₂
    apply sq_odd_then_odd
    exact m₂

#check pow_zero

/-- The Ramanujan-Nagell theorem: If `x` and `n` are integers satisfying `x ^ 2 + 7 = 2 ^ n`, then
    `(x, n) = (±1, 3), (±3, 4), (±5, 5), (±11, 7)` or `(±181, 15)`. -/
theorem RamanujanNagell :
  ∀ x : ℤ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n →
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
  intro x n h
  have h₂ : x % 2 = 1 := by
    apply x_is_odd x n
    -- · -- show that n is not zero
    · intro h'
      rw [h', pow_zero] at h
      have blah : x ^ 2 < 0  := by sorry
      have blah2 : 0 ≤ x^2 := sq_nonneg x
      apply lt_irrefl x
      linarith
    · sorry
  rw [← Nat.odd_iff] at h₂
  rcases Nat.even_or_odd n with h | h
  · sorry
  · sorry
