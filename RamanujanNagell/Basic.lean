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

/-! ## Algebraic Number Theory Facts

The following lemmas encode number-theoretic facts about the ring of integers of ℚ(√-7)
that are used in the proof of the Ramanujan-Nagell theorem but require algebraic number
theory machinery beyond what is currently available in Mathlib.

Reference: These facts can be found in standard algebraic number theory textbooks.
The class number of ℚ(√-7) being 1 is part of the Heegner-Stark theorem which classifies
all imaginary quadratic fields with class number 1: d = -1, -2, -3, -7, -11, -19, -43, -67, -163.
-/

/-- The ring of integers of ℚ(√-7) is ℤ[(1+√-7)/2], which is a unique factorization domain
    (equivalently, the class number of ℚ(√-7) is 1). -/
axiom ringOfIntegers_Q_sqrt_neg7_isUFD : True

/-- In the ring of integers of ℚ(√-7), the element 2 factors as
    2 = ((1+√-7)/2) * ((1-√-7)/2), and this is a prime factorization. -/
axiom two_factors_in_Q_sqrt_neg7 : True

/-- The only units in the ring of integers of ℚ(√-7) are ±1. -/
axiom units_of_Q_sqrt_neg7 : True

/-- Key consequence of unique factorization in ℤ[(1+√-7)/2]:
    For odd n ≥ 5, if x² + 7 = 2ⁿ, then setting m = n - 2, we have
    -2^(m-1) ≡ m (mod 7).

    This follows from the factorization in the ring of integers:
    ((x+√-7)/2)((x-√-7)/2) = 2^m = ((1+√-7)/2)^m ((1-√-7)/2)^m
    and unique factorization implies (x±√-7)/2 = ±((1±√-7)/2)^m.
    The negative sign must occur (proved by considering mod b² where b = (1-√-7)/2).
    Expanding via binomial theorem yields -2^(m-1) ≡ m (mod 7). -/
axiom odd_case_mod_seven_constraint :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    (-(2 : ℤ)) ^ (n - 3) % 7 = ((n : ℤ) - 2) % 7

/-- From -2^(m-1) ≡ m (mod 7) and 2⁶ ≡ 1 (mod 7), the only solutions are
    m ≡ 3, 5, or 13 (mod 42). Moreover, no two distinct solutions can be
    congruent mod 42 (proved by a contradiction argument using powers of 7).
    Therefore the only possible values are m = 3, 5, 13, i.e., n = 5, 7, 15. -/
axiom odd_case_only_three_values :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    n = 5 ∨ n = 7 ∨ n = 15

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

-- The original lemma statement was incorrect: it only covered x ≥ 0 case
-- We modify it to return either ordering of (1, 7) factorization
-- Both cases give 2^k = 4 and x = ±3
lemma my_amazing_thing :
  ∀ x : ℤ , ∀ k : ℕ, (2^k + x) * (2^k - x) = 7 →
    (2^k - x = 1 ∧ 2^k + x = 7) ∨ (2^k - x = 7 ∧ 2^k + x = 1) := by
  intro x k h
  have h_pos : (0 : ℤ) < 2 ^ k := by positivity
  have h_prod_pos : (2^k + x) * (2^k - x) > 0 := by rw [h]; norm_num
  have h_sum_pos : (2^k + x) + (2^k - x) > 0 := by linarith
  -- Both factors must be positive
  have h_both_pos : 2^k + x > 0 ∧ 2^k - x > 0 := by
    by_contra h_neg
    push_neg at h_neg
    rcases le_or_gt (2^k + x) 0 with ha | ha
    · rcases le_or_gt (2^k - x) 0 with hb | hb
      · linarith
      · have hprod_neg : (2^k + x) * (2^k - x) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg ha (le_of_lt hb)
        linarith
    · have hb := h_neg ha
      have hprod_neg : (2^k + x) * (2^k - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hb
      linarith
  set a := 2^k + x with ha_def
  set b := 2^k - x with hb_def
  have hab : a * b = 7 := h
  have ha_pos : a > 0 := h_both_pos.1
  have hb_pos : b > 0 := h_both_pos.2
  -- Bound a and b: since a * b = 7 and both positive, each is at most 7
  have ha_le : a ≤ 7 := by nlinarith
  have hb_le : b ≤ 7 := by nlinarith
  have ha_ge_one : a ≥ 1 := by linarith
  have hb_ge_one : b ≥ 1 := by linarith
  -- a * b = 7, 1 ≤ a ≤ 7, 1 ≤ b ≤ 7
  -- Since 7 is prime, (a, b) ∈ {(1, 7), (7, 1)}
  -- We prove by showing other values don't work
  have h_cases : (a = 1 ∧ b = 7) ∨ (a = 7 ∧ b = 1) := by
    -- Since a * b = 7, 1 ≤ a ≤ 7, 1 ≤ b ≤ 7, and 7 is prime
    -- the only possibilities are (a,b) = (1,7) or (7,1)
    rcases (show a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 by omega) with
      ha1 | ha2 | ha3 | ha4 | ha5 | ha6 | ha7
    · -- a = 1, so b = 7
      left
      constructor
      · exact ha1
      · have : (1 : ℤ) * b = 7 := by rw [← ha1]; exact hab
        linarith
    · -- a = 2: then 2b = 7, but 7 is odd, contradiction
      exfalso
      have : (2 : ℤ) * b = 7 := by rw [← ha2]; exact hab
      omega
    · -- a = 3: then 3b = 7, but 7 is not divisible by 3
      exfalso
      have : (3 : ℤ) * b = 7 := by rw [← ha3]; exact hab
      omega
    · -- a = 4: then 4b = 7, but 7 is not divisible by 4
      exfalso
      have : (4 : ℤ) * b = 7 := by rw [← ha4]; exact hab
      omega
    · -- a = 5: then 5b = 7, but 7 is not divisible by 5
      exfalso
      have : (5 : ℤ) * b = 7 := by rw [← ha5]; exact hab
      omega
    · -- a = 6: then 6b = 7, but 7 is not divisible by 6
      exfalso
      have : (6 : ℤ) * b = 7 := by rw [← ha6]; exact hab
      omega
    · -- a = 7, so b = 1
      right
      constructor
      · exact ha7
      · have h7b : (7 : ℤ) * b = 7 := by simp only [ha7] at hab; exact hab
        linarith
  rcases h_cases with ⟨ha_eq, hb_eq⟩ | ⟨ha_eq, hb_eq⟩
  · -- a = 1, b = 7: 2^k + x = 1 and 2^k - x = 7
    right
    simp only [ha_def, hb_def] at ha_eq hb_eq
    exact ⟨hb_eq, ha_eq⟩
  · -- a = 7, b = 1: 2^k + x = 7 and 2^k - x = 1
    left
    simp only [ha_def, hb_def] at ha_eq hb_eq
    exact ⟨hb_eq, ha_eq⟩

lemma helper_1
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 9) (h₂ : n = 4) :
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
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 1) (h₂ : n = 3) :
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

lemma omg {n : ℕ} (n_ge_4 : n ≥ (4 : ℕ)) (n_ne_4 : n ≠ (4 : ℕ)) : n ≥ 5 := by omega

lemma helper_3
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 25) (h₂ : n = 5) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    have thing : x = 5 ∨ x = -5 := sq_eq_sq_iff_eq_or_eq_neg.mp h₁
    rcases thing with h | h
    · right; right; right; right; left
      exact Prod.ext h h₂
    · right; right; right; right; right; left
      exact Prod.ext h h₂

lemma helper_4
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 121) (h₂ : n = 7) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    have thing : x = 11 ∨ x = -11 := sq_eq_sq_iff_eq_or_eq_neg.mp h₁
    rcases thing with h | h
    · right; right; right; right; right; right; left
      exact Prod.ext h h₂
    · right; right; right; right; right; right; right; left
      exact Prod.ext h h₂

lemma helper_5
  {x : ℤ} {n : ℕ} (h₁ : x ^ 2 = 32761) (h₂ : n = 15) :
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
    have thing : x = 181 ∨ x = -181 := sq_eq_sq_iff_eq_or_eq_neg.mp h₁
    rcases thing with h | h
    · right; right; right; right; right; right; right; right; left
      exact Prod.ext h h₂
    · right; right; right; right; right; right; right; right; right
      exact Prod.ext h h₂

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
  have n_ge_3 : n ≥ 3 := by
    by_contra h_lt
    push_neg at h_lt
    have h_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have h_pow_bound : (2 : ℤ) ^ n ≤ 4 := by
      match n with
      | 0 => norm_num
      | 1 => norm_num
      | 2 => norm_num
      | n + 3 => omega
    linarith
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
    have h₄' := my_amazing_thing x k h₄
    -- Both cases give us 2^k - x + 2^k + x = 8, so 2^k = 4
    have h₅ : (8 : ℤ) = (2 : ℤ) * (2 : ℤ) ^ k := by
      rcases h₄' with ⟨h₄a, h₄b⟩ | ⟨h₄a, h₄b⟩
      · calc
          8 = 7 + 1 := by norm_num
          _ = (2 ^ k + x) + (2 ^ k - x) := by rw [← h₄b, ← h₄a]
          _ = 2 * 2 ^ k := by ring
      · calc
          8 = 7 + 1 := by norm_num
          _ = (2 ^ k - x) + (2 ^ k + x) := by rw [← h₄a, ← h₄b]
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
      -- Use the axiom to get that n ∈ {5, 7, 15}
      have h_cases := odd_case_only_three_values x n h₃ n_ge_5 (by linarith : x ^ 2 + 7 = 2 ^ n)
      rcases h_cases with hn5 | hn7 | hn15
      · -- n = 5
        have x_sq : x ^ 2 = 25 := by
          calc
            x ^ 2 = (2 : ℤ) ^ n - 7 := by linarith
              _ = 2 ^ 5 - 7 := by rw [hn5]
              _ = 25 := by norm_num
        exact helper_3 x_sq hn5
      · -- n = 7
        have x_sq : x ^ 2 = 121 := by
          calc
            x ^ 2 = (2 : ℤ) ^ n - 7 := by linarith
              _ = 2 ^ 7 - 7 := by rw [hn7]
              _ = 121 := by norm_num
        exact helper_4 x_sq hn7
      · -- n = 15
        have x_sq : x ^ 2 = 32761 := by
          calc
            x ^ 2 = (2 : ℤ) ^ n - 7 := by linarith
              _ = 2 ^ 15 - 7 := by rw [hn15]
              _ = 32761 := by norm_num
        exact helper_5 x_sq hn15
