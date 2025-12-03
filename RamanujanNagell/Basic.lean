/-
Copyright (c) 2024 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star

/-!
# The Ramanujan-Nagell equation

Stuff

-/
set_option pp.numericTypes true

lemma sq_odd_then_odd :
  ∀ (x : ℤ), Odd (x ^ 2) → Odd (x) := by
  simp [parity_simps]

-- theorem not_even_seven : ¬Even (7 : ℤ) := by decide

theorem not_odd_two_pow (n : ℕ) : n ≠ 0 → ¬Odd ((2 : ℕ) ^ n) := by
  cases n <;> simp [pow_succ]

lemma two_pow_min_seven_odd :
  ∀ (n : ℕ), n ≠ 0 → Odd ( (2 : ℤ) ^ n - 7 ) := by
  intro n hn
  have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have h_even : Even ((2 : ℤ) ^ n) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn'
    rw [hm, add_comm, pow_add, pow_one, mul_comm]
    exact even_two_mul ((2 : ℤ) ^ m)
  obtain ⟨k, hk⟩ := h_even
  use k - 4
  omega


lemma x_is_odd :
  ∀ x : ℤ, ∀ n : ℕ, n ≠ 0 → x ^ 2 + 7 = 2 ^ n →
    x % 2 = 1 := by
    intros x n hn h
    have m : (x^2) = 2^n - 7 := by
      exact eq_tsub_of_add_eq h
    have m₂ : (x ^ 2) % 2 = 1 := by
      rw [m]
      rw [← Int.odd_iff]
      exact two_pow_min_seven_odd n hn
    rw [← Int.odd_iff]
    rw [← Int.odd_iff] at m₂
    apply sq_odd_then_odd
    exact m₂

#check add_sub_cancel

lemma my_amazing_thing :
  ∀ x : ℤ , ∀ k : ℕ, (2^k + x) * (2^k - x) = 7 → 2^k - x = 1 ∧ 2^k + x = 7 := by
  sorry

lemma helper_1
  {x : ℤ} {n : ℕ} (h₁ : x^2 = 9) (h₂ : n = 4) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    have thing : x = 3 ∨ x = -3 := sq_eq_sq_iff_eq_or_eq_neg.mp h₁
    rcases thing with h | h
    · right
      right
      left
      exact Prod.ext h h₂
    · right
      right
      right
      left
      exact Prod.ext h h₂

lemma helper_2
  {x : ℤ} {n : ℕ} (h₁ : x^2 = 1) (h₂ : n = 3) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    have thing : x = 1 ∨ x = -1 := sq_eq_sq_iff_eq_or_eq_neg.mp h₁
    rcases thing with h | h
    · left
      exact Prod.ext h h₂
    · right
      left
      exact Prod.ext h h₂

#check sub_add_cancel


lemma omg {n : ℕ} (n_ge_4 : n ≥ (4 : ℕ)) (n_ne_4 : n ≠ (4 : ℕ)) : n ≥ 5 := by omega

/-- The Ramanujan-Nagell theorem: If `x` and `n` are integers satisfying `x ^ 2 + 7 = 2 ^ n`, then
    `(x, n) = (±1, 3), (±3, 4), (±5, 5), (±11, 7)` or `(±181, 15)`. -/
theorem RamanujanNagell :
  ∀ x : ℤ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n →
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15):= by
  intro x n h
  have n_ge_3 : n ≥ 3 := by sorry
  have h₂ : x % 2 = 1 := by
    apply x_is_odd x n
    -- show that n is not zero
    · intro h'
      rw [h', pow_zero] at h
      have blah : x ^ 2 < 0  := by linarith
      have blah2 : 0 ≤ x^2 := sq_nonneg x
      apply lt_irrefl x
      linarith
    · exact h
  rw [← Int.odd_iff] at h₂
  rcases Nat.even_or_odd n with h₃ | h₃
  -- First deal with the case that n is even
  · rcases exists_eq_mul_right_of_dvd (even_iff_two_dvd.mp h₃) with ⟨k, hk⟩
    rw [hk] at h
    have h₄ : (2^k + x) * (2^k - x) = 7 := by
      calc
        (2^k + x) * (2^k - x) = 2^(2*k) - x^2 := by ring
                            _ = 7 := by rw [← h]; ring
    apply my_amazing_thing x k at h₄
    have h₄a : 2 ^ k - x = 1 := h₄.1
    have h₄b : 2 ^ k + x = 7 := h₄.2
    have h₅ : (8 : ℤ) = (2 : ℤ) * (2 : ℤ) ^ k := by
      calc
        8 = 7 + 1 := by norm_num
        _ = (2 ^ k + x) + (2 ^ k - x) := by rw [←h₄b , ←h₄a]
        _ = 2 ^ k + (x + (2 ^ k - x)) := by rw [add_assoc]
        _ = 2 ^ k + 2 ^ k := by
          rw [← add_assoc]
          ring
        _ = 2 * 2 ^ k := by ring
    have h₆ : 2 ^ k = 4 := by
      linarith
    have k_eq_2 : k = 2 := by
      -- Rewrite 4 as 2^2
      have h₇ : 4 = 2 ^ 2 := by norm_num
      -- Substitute h₇ into h₆
      rw [h₇] at h₆
      -- Use the injectivity of the power function to conclude k = 2
      exact Nat.pow_right_injective (by norm_num) h₆
    have n_eq_4 : n = 4 := by linarith
    have x_squared_eq_9 : x^2 = 9 := by
      calc
        x^2 = (2 : ℤ) ^ ((2 : ℕ) * k) - (7 : ℤ) := by linarith
          _ = 2^4 - 7 := by rw [k_eq_2]
          _ = 9 := by norm_num
    exact helper_1 x_squared_eq_9 n_eq_4

  -- Now deal with the much harder case that n is odd

  · have m := Nat.le.dest n_ge_3
    rcases m with _ | m
    · -- case 1 : n = 3
      have n_eq_3 : n = 3 := by linarith
      have x_squared_eq_1 : x^2 = 1 := by
        calc
          x^2 = (2 : ℤ) ^ n - (7 : ℤ) := by linarith
            _ = 2^3 - 7 := by rw [n_eq_3]
            _ = 1 := by norm_num
      exact helper_2 x_squared_eq_1 n_eq_3
    · -- case 2 : n ≥ 5
      have n_ge_4 : n ≥ 4 := by linarith
      have n_ne_4 : n ≠ 4 := by
        intro j
        subst j
        contradiction
      have n_ge_5 : n ≥ 5 := omg n_ge_4 n_ne_4
      clear n_ge_4 n_ne_4 n_ge_3
      let M : ℕ := n - 2
      have M_ge_3 : M ≥ 3 := by
        calc
          M = n - 2 := by rfl
          _ ≥ 5 - 2 := by omega
          _ = 3 := by norm_num
      have n_is_M_plus_2 : n = M + 2 := by omega
      rw [n_is_M_plus_2] at h
      have blah : (x^2 + 7) / 4 = 2^M := by
        calc
          (x^2 + 7) / 4 = 2^(M+2) / 4 := by rw [h]
                      _ = 2^M := by ring_nf; simp

      sorry
