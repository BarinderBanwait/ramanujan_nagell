/-
Copyright (c) 2024 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Parity
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

/-!
# The Ramanujan-Nagell equation

Stuff

-/

lemma x_is_odd :
  ∀ x : ℕ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n →
    x % 2 = 1 := by
    -- intros
    -- simp [← even_iff_two_dvd, ← Nat.even_add_one, parity_simps]
    -- ring_nf
    intros x n h
    have m : (x^2) = 2^n - 7 := by
      exact eq_tsub_of_add_eq h
    -- apply Nat.odd_iff.mp
    have m₂ : (x ^ 2) % 2 = 1 := by
      rw [m]
      sorry
    rw [← Nat.odd_iff]
    rw [← Nat.odd_iff] at m₂
    have obv : 2 ≠ 0 := by simp
    -- rw [Int.odd_pow'] at m₂
    sorry


/-- The Ramanujan-Nagell theorem: If `x` and `n` are integers satisfying `x ^ 2 + 7 = 2 ^ n`, then
    `(x, n) = (±1, 3), (±3, 4), (±5, 5), (±11, 7)` or `(±181, 15)`. -/
theorem RamanujanNagell :
  ∀ x : ℕ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n →
    (x, n) = (1, 3)
  ∨ (x, n) = (3, 4)
  ∨ (x, n) = (5, 5)
  ∨ (x, n) = (11, 7)
  ∨ (x, n) = (181, 15) := by
  simp
  sorry
