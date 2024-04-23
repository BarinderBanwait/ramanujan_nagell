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
  ∀ (x : ℕ), Odd (x ^ 2) → Odd (x) := by
  simp [parity_simps]

lemma two_pow_min_seven_odd :
  ∀ (n : ℕ), n ≠ 0 → Odd (2 ^ n - 7) := by
  intro n h
  -- rw [@Int.odd_sub (2^n) 7]
  sorry


lemma x_is_odd :
  ∀ x : ℕ, ∀ n : ℕ, n ≠ 0 → x ^ 2 + 7 = 2 ^ n →
    x % 2 = 1 := by
    intros x n h' h
    have m : (x^2) = 2^n - 7 := by
      exact eq_tsub_of_add_eq h
    have m₂ : (x ^ 2) % 2 = 1 := by
      rw [m]
      rw [← Nat.odd_iff]
      apply two_pow_min_seven_odd
      exact h'
    rw [← Nat.odd_iff]
    rw [← Nat.odd_iff] at m₂
    apply sq_odd_then_odd
    exact m₂


/-- The Ramanujan-Nagell theorem: If `x` and `n` are integers satisfying `x ^ 2 + 7 = 2 ^ n`, then
    `(x, n) = (±1, 3), (±3, 4), (±5, 5), (±11, 7)` or `(±181, 15)`. -/
theorem RamanujanNagell :
  ∀ x : ℕ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n →
    (x, n) = (1, 3)
  ∨ (x, n) = (3, 4)
  ∨ (x, n) = (5, 5)
  ∨ (x, n) = (11, 7)
  ∨ (x, n) = (181, 15) := by
  intro x n h
  have h₂ : x % 2 = 1 := by
    apply x_is_odd
    · sorry -- need to prove that n is not zero
    exact h
  rw [← Nat.odd_iff] at h₂
  rcases Nat.even_or_odd n with h | h
  · sorry
  · sorry
