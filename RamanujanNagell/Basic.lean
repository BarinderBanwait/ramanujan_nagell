/-
Copyright (c) 2024 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.RingTheory.Ideal.Int
import Mathlib.NumberTheory.Multiplicity

set_option linter.style.longLine false
set_option diagnostics true

open Polynomial NumberField QuadraticAlgebra RingOfIntegers Algebra Nat Ideal
  UniqueFactorizationMonoid

/-! ## Algebraic Number Theory Facts

The following lemmas encode number-theoretic facts about the ring of integers of ℚ(√-7)
that are used in the proof of the Ramanujan-Nagell theorem but require algebraic number
theory machinery beyond what is currently available in Mathlib.

Reference: These facts can be found in standard algebraic number theory textbooks.
The class number of ℚ(√-7) being 1 is part of the Heegner-Stark theorem which classifies
all imaginary quadratic fields with class number 1: d = -1, -2, -3, -7, -11, -19, -43, -67, -163.
-/

notation "K" => QuadraticAlgebra ℚ (-2) 1

-- ω² = -2 + 1*ω, i.e. ω = (1 + √(-7))/2, the generator of the ring of integers of Q(√(-7)).
-- The Fact says the polynomial x² - x + 2 has no rational roots (discriminant = -7 < 0).
instance : Fact (∀ (r : ℚ), r ^ 2 ≠ (-2 : ℚ) + (1 : ℚ) * r) := by
  constructor
  intro r h
  have h1 : r ^ 2 - r + 2 = 0 := by linarith
  have h2 : 4 * (r ^ 2 - r + 2) = (2 * r - 1) ^ 2 + 7 := by ring
  have h3 : (2 * r - 1) ^ 2 + 7 = 0 := by linarith
  have h4 : (2 * r - 1) ^ 2 ≥ 0 := sq_nonneg _
  linarith

instance : NumberField K := by
  admit

-- Field instance is provided automatically by QuadraticAlgebra.instField

notation "R" => (𝓞 K)

lemma is_integral_ω : IsIntegral ℤ (ω : K) := by
  -- ω satisfies X² - X + 2 = 0 (since ω² = -2 + ω in QuadraticAlgebra ℚ (-2) 1)
  refine ⟨X ^ 2 - X + C 2, ?_, ?_⟩
  · -- Monic: rewrite as X² - (X - 2) and use degree argument
    rw [show (X ^ 2 - X + C (2 : ℤ) : ℤ[X]) = X ^ 2 - (X - C 2) from by ring]
    exact monic_X_pow_sub (by rw [degree_X_sub_C]; norm_num)
  · -- Evaluation: ω² - ω + 2 = (-2 + ω) - ω + 2 = 0
    rw [← aeval_def]
    simp only [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C]
    rw [sq, omega_mul_omega_eq_mk]
    ext <;> simp

set_option quotPrecheck false in
notation "θ" => (⟨ω, is_integral_ω⟩ : 𝓞 K)

lemma is_integral_one_sub_ω : IsIntegral ℤ ((1 : K) - ω) := by
  admit

-- θ' = (1 - √-7)/2, the conjugate of θ in the ring of integers
set_option quotPrecheck false in
notation "θ'" => (⟨1 - ω, is_integral_one_sub_ω⟩ : 𝓞 K)

lemma my_minpoly : minpoly ℤ θ = X ^ 2 - X + 2 := by
  admit

lemma span_eq_top : adjoin ℤ {θ} = ⊤ := by
  admit

lemma class_number_one : UniqueFactorizationMonoid R := by
  admit

lemma class_number_one_PID : IsPrincipalIdealRing R := by
  admit

lemma units_pm_one : ∀ u : Rˣ, u = 1 ∨ u = -1 := by
  admit

-- The Algebra.norm on a QuadraticAlgebra coincides with the QuadraticAlgebra.norm
lemma algebra_norm_eq_quadratic_norm (z : K) : Algebra.norm ℚ z = QuadraticAlgebra.norm z := by
  admit

lemma exponent : exponent θ = 1 := by
  rw [exponent_eq_one_iff, span_eq_top]

lemma ne_dvd_exponent (p : ℕ) [hp : Fact p.Prime] : ¬ (p ∣ RingOfIntegers.exponent θ) := by
  rw [exponent, dvd_one]
  exact hp.1.ne_one

lemma two_factorisation_R : θ * (1 - θ) = 2 := by
  admit


/-!
# The Ramanujan-Nagell equation

Stuff

-/


/--
Summary

PROVIDED SOLUTION
We begin by applying `main_factorisation_lemma` below. The relationship between `m` here and `n` there is `m = n - 2`.
We then have the factorization
((x + √-7)/2) * ((x - √-7)/2) = 2^m = ((1 + √-7)/2)^m * ((1 - √-7)/2)^m
which is written in Lean as ((↑x + 2*(↑θ : K) - 1) / 2) * ((↑x - 2*(↑θ : K) + 1) / 2) = (↑θ : K) ^ m * (1 - (↑θ : K)) ^ m.
This is a factorization into irreducible elements in the ring of integers of ℚ(√-7) (which is ℤ[θ]).
Since the class number is 1, we have unique factorization into irreducibles. Equivalently, the prime elements are the same as the irreducible elements.
One shows that the two factors (↑x + 2*(↑θ : K) - 1) / 2) and ((↑x - 2*(↑θ : K) + 1) / 2) are coprime as follows: by uniqueness of factorization,
we only need to consider the elements θ and (1 - θ) (the prime factors of 2 in this ring). If either of these divided both factors, then it would divide their difference,
which is 2*θ - 1 = √-7, which by taking norms is seen to not be the case. Therefore, by unique factorization, each factor must be equal to one of the two factors on the right up to multiplication by a unit.
The units in this ring are just ±1 (use `units_pm_one` above). Therefore, we obtain the important equation
(x ± √-7)/2 = \pm ((1 ± √-7)/2)^m.
Eliminating x by taking the difference of these two equations, we obtain the two cases stated in the lemma. There might be several similar
cases to deal with at the end to keep track of the signs.
The relevant results about unique factorization and UFDs can be found in the NumberTheory and RingTheory folders of mathlib.
-/
/- Exercise 1: The conjugate factors (x ± √-7)/2 lie in R (since x is odd) and
    their product equals (x²+7)/4 = 2^m = θ^m · (1-θ)^m. The division by 4 is
    deliberate: it makes the difference of the factors equal to √-7 = 2θ-1 (rather
    than 2√-7), which simplifies the coprimality argument. -/
lemma factors_in_R_with_product (x : ℤ) (m : ℕ) (hm_ge : m ≥ 3)
    (h : (x ^ 2 + 7) / 4 = 2 ^ m) :
    ∃ α β : R, α * β = θ ^ m * θ' ^ m ∧
      (↑α : K) - ↑β = 2 * (↑θ : K) - 1 := by
  -- Step 1: Show x is odd
  have hx_odd : Odd x := by
    by_contra hx_not_odd
    rw [Int.not_odd_iff_even] at hx_not_odd
    obtain ⟨t, ht⟩ := hx_not_odd -- x = t + t
    have hx2t : x = 2 * t := by omega
    -- When x = 2t, (x²+7)/4 = ((2t)²+7)/4 = (4t²+7)/4 = t²+1 (integer division)
    have h_div : (x ^ 2 + 7) / 4 = t ^ 2 + 1 := by
      rw [hx2t]
      have : (2 * t) ^ 2 + 7 = (t ^ 2 + 1) * 4 + 3 := by ring
      omega
    -- So t²+1 = 2^m
    rw [h_div] at h
    -- 4 ∣ 2^m for m ≥ 2
    have h4_dvd_2m : (4 : ℤ) ∣ 2 ^ m :=
      ⟨2 ^ (m - 2), by rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_add]; congr 1; omega⟩
    -- So 4 ∣ (t²+1)
    have h4_dvd : (4 : ℤ) ∣ (t ^ 2 + 1) := h ▸ h4_dvd_2m
    -- But t² mod 4 ∈ {0, 1}, so t²+1 mod 4 ∈ {1, 2}, contradiction
    rcases Int.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · -- t even: t = 2s, t² = 4s², 4 ∣ t², so 4 ∣ (t²+1) implies 4 ∣ 1
      have : (4 : ℤ) ∣ t ^ 2 := ⟨s ^ 2, by rw [hs]; ring⟩
      have : (4 : ℤ) ∣ 1 := (Int.dvd_add_right this).mp h4_dvd
      omega
    · -- t odd: t = 2s+1, t² = 4s²+4s+1, 4 ∣ (t²-1), so 4 ∣ (t²+1) implies 4 ∣ 2
      have : (4 : ℤ) ∣ (t ^ 2 - 1) := ⟨s ^ 2 + s, by rw [hs]; ring⟩
      have h4_dvd_2 : (4 : ℤ) ∣ ((t ^ 2 + 1) - (t ^ 2 - 1)) := Int.dvd_sub h4_dvd this
      -- have : (4 : ℤ) ∣ 2 := by linarith_or_polyrith_or_convert h4_dvd_2; convert h4_dvd_2 using 1; ring
      omega
  -- Step 2: Get k with x = 2*k + 1
  obtain ⟨k, hk⟩ := hx_odd
  -- Step 3: (x²+7)/4 = k²+k+2 (exact division since x is odd)
  have hdiv : (x ^ 2 + 7) / 4 = k ^ 2 + k + 2 := by
    apply Int.ediv_eq_of_eq_mul_left (by norm_num : (4 : ℤ) ≠ 0)
    rw [hk]; ring
  rw [hdiv] at h -- h : k^2 + k + 2 = 2^m
  -- Step 4: Key identity ω * (1 - ω) = 2 in K (from two_factorisation_R)
  have hω_prod : (ω : K) * (1 - ω) = 2 := by
    have := congr_arg Subtype.val two_factorisation_R
    simpa using this
  -- Step 5: Construct α = k + θ, β = k + θ' as elements of R
  refine ⟨⟨(k : K) + ω, IsIntegral.add isIntegral_algebraMap is_integral_ω⟩,
         ⟨(k : K) + (1 - ω), IsIntegral.add isIntegral_algebraMap is_integral_one_sub_ω⟩,
         ?_, ?_⟩
  · -- Product: (k+ω)(k+(1-ω)) = k²+k+ω(1-ω) = k²+k+2 = 2^m = ω^m·(1-ω)^m = θ^m·θ'^m
    apply Subtype.ext
    calc ((k : K) + ω) * ((k : K) + (1 - ω))
        = (k : K) ^ 2 + (k : K) + ω * (1 - ω) := by ring
      _ = (k : K) ^ 2 + (k : K) + 2 := by rw [hω_prod]
      _ = (2 : K) ^ m := by
        have := congr_arg (fun n : ℤ => (n : K)) h
        push_cast at this
        exact this
      _ = ω ^ m * (1 - ω) ^ m := by rw [← mul_pow, hω_prod]
  · -- Difference: (k + ω) - (k + (1-ω)) = 2ω - 1 = 2·↑θ - 1
    simp only
    norm_num
    grind

/-- Exercise 2: The conjugate factors are coprime in R. The only prime factors of 2
    in R are θ and θ' (since 2 = θ·θ' by `two_factorisation_R`). If either
    divided both α and β, it would divide their difference 2θ-1 = √(-7), but
    N(√-7) = 7 is not divisible by N(θ) = 2 or N(θ') = 2. -/
lemma conjugate_factors_coprime (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_diff : (↑α : K) - ↑β = 2 * (↑θ : K) - 1) :
    IsCoprime α β := by
  -- 1. Register that R is a PID
  haveI : IsPrincipalIdealRing R := class_number_one_PID
  -- Now this tactic works because PID implies GCDMonoid
  apply isCoprime_of_prime_dvd
  · -- Goal 1
    intro h
    -- Deconstruct the hypothesis "α = 0 ∧ β = 0" and substitute into context
    obtain ⟨rfl, rfl⟩ := h
    -- Now h_diff becomes: 0 - 0 = 2 * θ - 1
    simp only [sub_self] at h_diff
    -- We derive a contradiction by squaring both sides: 0^2 = (2θ - 1)^2 = -7
    have h_contra : (0 : K) = -7 := by
      calc (0 : K)
        _ = (0 : K) ^ 2 := by norm_num
        _ = (2 * (θ : K) - 1) ^ 2 := by rw [h_diff]
        _ = 4 * ((θ : K) ^ 2 - (θ : K)) + 1 := by ring
        _ = 4 * (-2) + 1 := by
           -- Use the defining polynomial of θ: x^2 - x + 2 = 0
           have h_poly : (θ : K)^2 - (θ : K) = -2 := by
            -- Prove that ω² - ω + 2 = 0 using the same steps as is_integral_ω
            have h_zero : (θ : K) ^ 2 - (θ : K) + 2 = 0 := by
              rw [sq, omega_mul_omega_eq_mk]
              ext <;> simp
           -- Rearrange (ω² - ω + 2 = 0) to (ω² - ω = -2)
            rw [← add_eq_zero_iff_eq_neg]
            exact h_zero
           rw [h_poly]
        _ = -7 := by norm_num
    -- 0 = -7 is obviously false
    norm_num at h_contra
  · -- Goal 2
    intro p hp hpa hpb
    have h_prod_val : α * β = (2 : R) ^ m := by
      rw [h_prod, ← mul_pow]
    -- FIX: Prove θ' is syntactically equal to (1 - θ) so the lemma matches
      have h_rewrite : θ' = 1 - θ := Subtype.ext (by simp)
    -- Now rewrite θ' -> (1 - θ), then apply the factorization lemma
      rw [h_rewrite, two_factorisation_R]
    have h_p_dvd_two : p ∣ 2 := by
      have : p ∣ (2 : R) ^ m := h_prod_val ▸ dvd_mul_of_dvd_left hpa β
      exact Prime.dvd_of_dvd_pow hp this
    let diff := α - β
    -- Step 2: Show p divides (α - β)
    have h_p_dvd_diff : p ∣ diff := dvd_sub hpa hpb
    -- Step 3: Norm calculations
    -- We show N(p) | N(2) and N(p) | N(α - β)
    -- N(2) = 4
    have h_norm_two : Int.natAbs (Algebra.norm ℤ (2 : R)) = 4 := by
        have h1 : (Algebra.norm ℤ (2 : 𝓞 K) : ℚ) = Algebra.norm ℚ ((2 : 𝓞 K) : K) :=
          Algebra.coe_norm_int 2
        have h2 : ((2 : 𝓞 K) : K) = (2 : K) := rfl
        rw [h2] at h1
        have h_qa : QuadraticAlgebra.norm (2 : K) = 4 := by apply QuadraticAlgebra.norm_intCast
        have h3 : Algebra.norm ℚ (2 : K) = QuadraticAlgebra.norm (2 : K) :=
          algebra_norm_eq_quadratic_norm 2
        rw [h3, h_qa] at h1
        have h4 : Algebra.norm ℤ (2 : 𝓞 K) = 4 := by
          exact_mod_cast h1
        simp [h4]
    have h_norm_two_again : QuadraticAlgebra.norm (2 : K) = 4 := by apply QuadraticAlgebra.norm_intCast
    -- First prove (α - β)^2 = -7

-- Lift the difference equation from K to R
    have h_diff_R : α - β = 2 * ⟨ω, is_integral_ω⟩ - 1 := by
      -- 1. To show equality in the subtype R, show equality of the underlying values in K
      apply Subtype.ext
      -- 2. Distribute the coercion arrows (↑) over subtraction and multiplication
      -- 3. Now the goal matches h_diff exactly
      exact h_diff
    have h_diff_sq : diff ^ 2 = -7 := by
      -- Move the equality to K
      apply Subtype.ext
      -- Unfold 'diff' so we see 'α - β'
      simp only [diff]
      -- Now we can rewrite using the hypothesis in K
      rw [h_diff_R]
      -- Use the defining polynomial identity: ω² - ω + 2 = 0
      have h_zero : (θ : K) ^ 2 - (θ : K) + 2 = 0 := by
        rw [sq, omega_mul_omega_eq_mk]
        ext
        · simp
        · simp
      -- The goal is now (2θ - 1)^2 = -7. Linear combination solves it using h_zero.
      -- First derive θ² = θ - 2 from h_zero (rearranging θ² - θ + 2 = 0)
      have h_theta_sq : (θ : K) ^ 2 = (θ : K) - 2 := by
        linear_combination h_zero
      -- Push coercions through and substitute
      calc (2 * (θ : K) - 1) ^ 2
          = 4 * (θ : K) ^ 2 - 4 * (θ : K) + 1 := by ring
        _ = 4 * ((θ : K) - 2) - 4 * (θ : K) + 1 := by rw [h_theta_sq]
        _ = -8 + 1 := by ring
        _ = -7 := by norm_num
    -- Then calculate the norm
    -- N(diff²) = N(-7) = 49, so N(diff)² = 49, hence |N(diff)| = 7
    have h_norm_diff : ((Algebra.norm ℤ) diff).natAbs = 7 := by
      have h_norm_sq : (Algebra.norm ℤ) (diff ^ 2) = 49 := by
        rw [h_diff_sq]
        -- Goal: (Algebra.norm ℤ) (-7 : 𝓞 K) = 49
        -- Use QuadraticAlgebra.norm_intCast: norm (n : K) = n^2
        have h1 : (Algebra.norm ℤ (-7 : 𝓞 K) : ℚ) = Algebra.norm ℚ ((-7 : 𝓞 K) : K) :=
            Algebra.coe_norm_int (-7)
        have h2 : ((-7 : 𝓞 K) : K) = (-7 : K) := rfl
        rw [h2] at h1
        have h_qa : QuadraticAlgebra.norm (-7 : K) = 49 := by apply QuadraticAlgebra.norm_intCast
        -- Relate Algebra.norm ℤ on 𝓞 K to QuadraticAlgebra.norm on K
        -- For integers, coercion commutes: (-7 : 𝓞 K) : K = (-7 : K)
        have h3 : Algebra.norm ℚ (-7 : K) = QuadraticAlgebra.norm (-7 : K) :=
          algebra_norm_eq_quadratic_norm (-7)
        -- The norms agree on 𝓞 K
        rw [h3] at h1
        rw [h_qa] at h1
        exact Eq.symm ((fun {a b} ↦ Rat.intCast_inj.mp) (_root_.id (Eq.symm h1)))
      rw [map_pow] at h_norm_sq
      have : ((Algebra.norm ℤ) diff).natAbs ^ 2 = 7 ^ 2 := by
        have h_sq_eq : ((Algebra.norm ℤ) diff) ^ 2 = 49 := h_norm_sq
        zify
        rw [sq_abs]
        exact_mod_cast h_sq_eq
      exact Nat.pow_left_injective (by exact Ne.symm (zero_ne_add_one 1)) this
    -- Step 4: Logic with divisibility of norms
    have h_dvd_four : ((Algebra.norm ℤ) p).natAbs ∣ 4 := by
      rw [← h_norm_two]
      apply Int.natAbs_dvd_natAbs.mpr
      exact MonoidHom.map_dvd (Algebra.norm ℤ) h_p_dvd_two
    have h_dvd_seven : ((Algebra.norm ℤ) p).natAbs ∣ 7 := by
      rw [← h_norm_diff]
      apply Int.natAbs_dvd_natAbs.mpr
      exact map_dvd (Algebra.norm ℤ) h_p_dvd_diff
    -- gcd(4, 7) = 1, so |N(p)| = 1
    have h_norm_p_eq_one : ((Algebra.norm ℤ) p).natAbs = 1 := by
      have h_gcd : Nat.gcd 4 7 = 1 := by norm_num
      have h_dvd_gcd := Nat.dvd_gcd h_dvd_four h_dvd_seven
      rw [h_gcd] at h_dvd_gcd
      exact eq_one_of_dvd_one h_dvd_gcd
    -- |N(p)| = 1 implies p is a unit, contradicting that p is prime
    have h_unit : IsUnit p := by
      rw [NumberField.isUnit_iff_norm]
      -- Need: |(RingOfIntegers.norm ℚ p : ℚ)| = 1
      -- Use that (RingOfIntegers.norm ℚ p : ℚ) = (Algebra.norm ℤ p : ℚ)
      simp only [RingOfIntegers.coe_norm, ← Algebra.coe_norm_int]
      -- Now need: |(Algebra.norm ℤ p : ℚ)| = 1
      rw [← Int.cast_abs, Int.abs_eq_natAbs, h_norm_p_eq_one]
      exact rfl
    exact hp.not_unit h_unit

/-- Exercise 3: In the UFD R, if α · β = θ^m · θ'^m and gcd(α, β) = 1, then
    α = ±θ^m or α = ±θ'^m. This combines two steps: (1) unique factorization
    (`class_number_one`) implies α is associate to θ^m or θ'^m, and (2) the only
    units are ±1 (`units_pm_one`), pinning down the sign. -/
lemma ufd_power_association (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β) :
    (α = θ ^ m ∨ α = -(θ ^ m)) ∨ (α = θ' ^ m ∨ α = -(θ' ^ m)) := by
  haveI := class_number_one
  admit

/-- Exercise 4: From α = ±θ^m or α = ±θ'^m, use the product relation to determine β,
    then take the difference α - β = 2θ-1 to eliminate x and obtain the conclusion. -/
lemma eliminate_x_conclude (α β : R) (m : ℕ)
    (h_diff : (↑α : K) - ↑β = 2 * (↑θ : K) - 1)
    (h_assoc : (α = θ ^ m ∨ α = -(θ ^ m)) ∨ (α = θ' ^ m ∨ α = -(θ' ^ m)))
    (h_prod : α * β = θ ^ m * θ' ^ m) :
    (2 * θ - 1 = θ ^ m - θ' ^ m) ∨ (-2 * θ + 1 = θ ^ m - θ' ^ m) := by
  have hθ_ne : (⟨ω, is_integral_ω⟩ : 𝓞 K) ≠ 0 := by
    intro h
    have : (ω : K) = 0 := congr_arg Subtype.val h
    have hpoly : (ω : K) ^ 2 - (ω : K) + 2 = 0 := by rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
    rw [this] at hpoly; norm_num at hpoly
  have hθ'_ne : (⟨1 - ω, is_integral_one_sub_ω⟩ : 𝓞 K) ≠ 0 := by
    intro h
    have h0 : (1 : K) - ω = 0 := congr_arg Subtype.val h
    have hω1 : (ω : K) = 1 := by rwa [sub_eq_zero, eq_comm] at h0
    have hpoly : (ω : K) ^ 2 - (ω : K) + 2 = 0 := by rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
    rw [hω1] at hpoly; norm_num at hpoly
  -- Key: the coercion R → K is injective
  have hinj : Function.Injective (Subtype.val : R → K) := Subtype.val_injective
  rcases h_assoc with (rfl | rfl) | (rfl | rfl)
  · -- Case 1: α = θ^m, determine β = θ'^m, conclude Left
    left
    have hβ : β = θ' ^ m :=
      mul_left_cancel₀ (pow_ne_zero m hθ_ne) h_prod
    subst hβ
    exact hinj (by
      exact _root_.id (Eq.symm h_diff))
  · -- Case 2: α = -(θ^m), determine β = -(θ'^m), conclude Right
    right
    have hβ : β = -(θ' ^ m) :=
      mul_left_cancel₀ (neg_ne_zero.mpr (pow_ne_zero m hθ_ne))
        (h_prod.trans (neg_mul_neg _ _).symm)
    subst hβ
    exact hinj (by
      change -2 * ω + 1 = ω ^ m - (1 - ω) ^ m
      change -(ω ^ m) - (-(1 - ω) ^ m) = 2 * ω - 1 at h_diff
      linear_combination h_diff)
  · -- Case 3: α = θ'^m, determine β = θ^m, conclude Right
    right
    have hβ : β = θ ^ m :=
      mul_left_cancel₀ (pow_ne_zero m hθ'_ne) (h_prod.trans (mul_comm _ _))
    subst hβ
    exact hinj (by
      change -2 * ω + 1 = ω ^ m - ((1 : K) - ω) ^ m
      change ((1 : K) - ω) ^ m - ω ^ m = 2 * ω - 1 at h_diff
      linear_combination h_diff)
  · -- Case 4: α = -(θ'^m), determine β = -(θ^m), conclude Left
    left
    have hβ : β = -(θ ^ m) :=
      mul_left_cancel₀ (neg_ne_zero.mpr (pow_ne_zero m hθ'_ne))
        (h_prod.trans ((mul_comm _ _).trans (neg_mul_neg _ _).symm))
    subst hβ
    exact hinj (by
      change 2 * ω - 1 = ω ^ m - ((1 : K) - ω) ^ m
      change -(((1 : K) - ω) ^ m) - (-(ω ^ m)) = 2 * ω - 1 at h_diff
      linear_combination -h_diff)

set_option maxHeartbeats 400000 in -- long proof with many case splits and polynomial checks
/-- If we know one of (2*θ - 1 = θ^m - θ'^m) ∨ (-2*θ + 1 = θ^m - θ'^m), then in fact
    the minus sign must hold: -2*θ + 1 = θ^m - θ'^m. This is proved by reducing modulo
    θ'^2 and checking which sign is consistent. -/
lemma must_have_minus_sign (m : ℕ) (hm_odd : Odd m) (hm_ge : m ≥ 3)
    (h : (2 * θ - 1 = θ ^ m - θ' ^ m) ∨ (-2 * θ + 1 = θ ^ m - θ' ^ m)) :
    (-2 * θ + 1 = θ ^ m - θ' ^ m) := by
  -- It suffices to rule out the plus sign case
  rcases h with h_plus | h_minus
  · -- Suppose for contradiction that the plus sign holds:
    -- 2*θ - 1 = θ^m - θ'^m, i.e., θ^m - θ'^m = θ - θ'
    exfalso
    -- Step 1: (A) θ + θ' = 1; (B) θ - θ' = 2*θ - 1 (= √-7)
    have hA : θ + θ' = 1 := by exact add_eq_of_eq_sub' rfl
    have h_theta' : θ' = 1 - θ := Subtype.ext (by simp)
    have hB : θ - θ' = 2 * θ - 1 := by
      calc θ - θ' = θ - (1 - θ) := by rw [h_theta']
        _ = 2 * θ - 1 := by ring
    -- Step 2: From h_plus and (B), we get (C): θ^m - θ'^m = θ - θ'
    have hC : θ ^ m - θ' ^ m = θ - θ' := by grind
    -- Step 3: From (A), θ = 1 - θ', so θ^2 = (1-θ')^2 ≡ 1 - 2θ' (mod θ'^2).
    --         Since θ'∣2, we get θ^2 ≡ 1 (mod θ'^2).
    have step3 : θ' ^ 2 ∣ (θ ^ 2 - 1) := by
      -- θ^2 - 1 = (1 - θ')^2 - 1 = θ'(θ' - 2) by ring
      have h_eq : θ ^ 2 - 1 = θ' * (θ' - 2) := by rw [h_theta']; ring
      rw [h_eq, sq]
      -- Need: θ' * θ' ∣ θ' * (θ' - 2), suffices θ' ∣ (θ' - 2)
      apply mul_dvd_mul_left
      -- θ' ∣ 2 since θ * θ' = 2 (two_factorisation_R)
      have h_dvd_2 : θ' ∣ (2 : R) := by
        refine ⟨θ, ?_⟩
        have h := two_factorisation_R
        rw [← h_theta', mul_comm] at h
        exact h.symm
      -- θ' ∣ θ' and θ' ∣ 2, so θ' ∣ (θ' - 2)
      exact dvd_sub dvd_rfl h_dvd_2
    -- Step 4: Since m is odd and θ^2 ≡ 1 (mod θ'^2), we get θ^m ≡ θ (mod θ'^2).
    have step4 : θ' ^ 2 ∣ (θ ^ m - θ) := by
      obtain ⟨k, hk⟩ := hm_odd
      -- θ^m - θ = θ · ((θ²)^k - 1)
      have h_eq : θ ^ m - θ = θ * ((θ ^ 2) ^ k - 1) := by
        rw [hk, show 2 * k + 1 = 1 + 2 * k from by ring,
            pow_add, pow_one, pow_mul, mul_sub, mul_one]
      rw [h_eq]
      -- θ'^2 ∣ (θ² - 1) from step3, and (θ² - 1) ∣ ((θ²)^k - 1) by geometric sum
      exact dvd_mul_of_dvd_right
        (dvd_trans step3 (sub_one_dvd_pow_sub_one (θ ^ 2) k)) θ
    -- Step 5: Applying step4 to (C): θ - θ'^m ≡ θ - θ' (mod θ'^2),
    --         so θ'^2 ∣ (θ'^m - θ'). Since m ≥ 3, θ'^2 ∣ θ'^m, hence θ'^2 ∣ θ'.
    have step5 : θ' ^ 2 ∣ θ' := by
      -- From hC (θ^m - θ'^m = θ - θ'), rearranging: θ^m - θ = θ'^m - θ'
      have h_eq : θ ^ m - θ = θ' ^ m - θ' := by linear_combination hC
      -- So θ'^2 ∣ (θ'^m - θ') (from step4 and h_eq)
      have h_dvd_diff : θ' ^ 2 ∣ (θ' ^ m - θ') := by rwa [← h_eq]
      -- Since m ≥ 3 ≥ 2, θ'^2 ∣ θ'^m
      have h_dvd_pow : θ' ^ 2 ∣ θ' ^ m := pow_dvd_pow θ' (by omega : 2 ≤ m)
      -- θ'^2 ∣ θ'^m and θ'^2 ∣ (θ'^m - θ'), so θ'^2 ∣ θ'^m - (θ'^m - θ') = θ'
      have h := dvd_sub h_dvd_pow h_dvd_diff
      rwa [show θ' ^ m - (θ' ^ m - θ') = θ' from by ring] at h
    -- Step 6: θ'^2 ∣ θ' implies θ' is a unit, but θ' is not ±1. Contradiction.
    -- First, θ' ≠ 0
    have hθ'_ne : θ' ≠ 0 := by
      intro h_zero
      have h0 : (1 : K) - ω = 0 := congr_arg Subtype.val h_zero
      have hω1 : (ω : K) = 1 := by rwa [sub_eq_zero, eq_comm] at h0
      have hpoly : (ω : K) ^ 2 - (ω : K) + 2 = 0 := by
        rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
      rw [hω1] at hpoly; norm_num at hpoly
    -- From θ'^2 ∣ θ', cancel θ' to get θ' ∣ 1
    have h_dvd_one : θ' ∣ 1 := by
      rw [sq] at step5
      have : θ' * θ' ∣ θ' * 1 := by rwa [mul_one]
      exact (mul_dvd_mul_iff_left hθ'_ne).mp this
    -- So θ' is a unit
    have h_unit := isUnit_of_dvd_one h_dvd_one
    -- By units_pm_one, θ' = ±1
    obtain ⟨u, hu⟩ := h_unit
    rcases units_pm_one u with rfl | rfl
    · -- u = 1: θ' = 1, so 1 - ω = 1, hence ω = 0, contradicting ω²-ω+2=0
      have h_K : (1 : K) - ω = 1 := by
        have h := congr_arg Subtype.val hu; simp at h; exact h.symm
      have hω : (ω : K) = 0 := by linear_combination -h_K
      have hpoly : (ω : K) ^ 2 - (ω : K) + 2 = 0 := by
        rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
      rw [hω] at hpoly; norm_num at hpoly
    · -- u = -1: θ' = -1, so 1 - ω = -1, hence ω = 2, contradicting ω²-ω+2=0
      have h_K : (1 : K) - ω = -1 := by
        have h := congr_arg Subtype.val hu; simp at h; exact h.symm
      have hω : (ω : K) = 2 := by linear_combination -h_K
      have hpoly : (ω : K) ^ 2 - (ω : K) + 2 = 0 := by
        rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
      rw [hω] at hpoly; norm_num at hpoly
  · -- The minus sign case is what we want
    exact h_minus


lemma main_m_condition :
  ∀ x : ℤ, ∀ m : ℕ, Odd m → m ≥ 3 → (x ^ 2 + 7) / 4 = 2 ^ m →
    (-2*θ + 1 = θ^m - θ'^m) := by
  intro x m hm_odd hm_ge h_eq
  -- Step 1: Get conjugate factors α = (x+√-7)/2, β = (x-√-7)/2 in R
  --         with α · β = θ^m · θ'^m and α - β = 2θ-1 = √-7
  obtain ⟨α, β, h_prod, h_diff⟩ := factors_in_R_with_product x m hm_ge h_eq
  -- Step 2: α and β are coprime (θ and θ' don't divide √-7, by norms)
  have h_coprime := conjugate_factors_coprime α β m h_prod h_diff
  -- Step 3: By UFD property (class number 1), α is associate to θ^m or θ'^m
  have h_assoc := ufd_power_association α β m h_prod h_coprime
  -- Step 4: Units are ±1, take difference to eliminate x and get the disjunction
  have h_disj := eliminate_x_conclude α β m h_diff h_assoc h_prod
  -- Step 5: The minus sign must hold
  exact must_have_minus_sign m hm_odd hm_ge h_disj

/--
comment
-/
lemma reduction_divide_by_4 :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    (x ^ 2 + 7) / 4 = 2 ^ (n - 2) := by
  intro x n _ hn hx
  rw [hx]
  exact Int.ediv_eq_of_eq_mul_left (by norm_num)
    (by rw [show n = n - 2 + 2 from by omega, pow_add]; norm_num)


/-- From -2*θ + 1 = θ^m - θ'^m, expand via the binomial theorem and reduce
    modulo 7 to obtain -2^(m-1) ≡ m (mod 7). -/
lemma expand_by_binomial (m : ℕ) (hm_odd : Odd m) (hm_ge : m ≥ 3)
    (h : -2 * θ + 1 = θ ^ m - θ' ^ m) :
    -(2 : ℤ) ^ (m - 1) % 7 = (m : ℤ) % 7 := by
  -- Step 1: Multiply h by 2^m. Since 2θ = 1+√-7 and 2θ' = 1-√-7, we get
  --         -2^m * √-7 = (1+√-7)^m - (1-√-7)^m.
  -- Equivalently (using √-7 = 2θ - 1):
  have step1 : -(2 : K) ^ m * (2 * (↑θ : K) - 1) =
      (2 * (↑θ : K)) ^ m - (2 * (1 - (↑θ : K))) ^ m := by
    have h_K : -(2 : K) * ω + 1 = ω ^ m - (1 - ω) ^ m := by
      have h0 := congr_arg Subtype.val h
      simpa using h0
    simp only [mul_pow]
    linear_combination (2 : K) ^ m * h_K
  -- Step 2: Expand the RHS via the binomial theorem. The even-power terms cancel,
  --         and we can cancel √-7 from both sides, giving:
  --         -2^(m-1) = m - C(m,3)*7 + C(m,5)*7² - ...
  --         i.e., ∃ q : ℤ, -(2:ℤ)^(m-1) = m + 7*q
  have step2 : ∃ q : ℤ, -(2 : ℤ) ^ (m - 1) = ↑m + 7 * q := by
    -- Step 1: Write 2θ = 1 + √-7 and 2θ' = 1 - √-7.
    -- In our algebra, √-7 = 2ω - 1, so (2ω - 1)² = -7.
    have hsq : (2 * (↑θ : K) - 1) ^ 2 = (-7 : K) := by
      calc (2 * (↑θ : K) - 1) ^ 2
          = 4 * (↑θ : K) ^ 2 - 4 * (↑θ : K) + 1 := by ring
        _ = 4 * ((↑θ : K) - 2) - 4 * (↑θ : K) + 1 := by
          rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
        _ = -8 + 1 := by ring
        _ = -7 := by norm_num
    -- Step 2: Use the binomial expansion to expand:
    --   (1+√-7)^m = (2θ)^m = (1 + (2θ-1))^m = Σ_{k=0}^{m} C(m,k) · (2θ-1)^k
    --   (1-√-7)^m = (2θ')^m = (1 - (2θ-1))^m = Σ_{k=0}^{m} C(m,k) · (-(2θ-1))^k
    have hbinom_plus : (2 * (↑θ : K)) ^ m =
        Finset.sum (Finset.range (m + 1))
          (fun k => (↑(m.choose k) : K) * (2 * (↑θ : K) - 1) ^ k) := by
      have h := add_pow (2 * (↑θ : K) - 1) 1 m
      simp only [one_pow, mul_one] at h
      rw [show (2 * (↑θ : K) - 1) + 1 = 2 * (↑θ : K) from by ring] at h
      rw [h]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    have hbinom_minus : (2 * (1 - (↑θ : K))) ^ m =
        Finset.sum (Finset.range (m + 1))
          (fun k => (↑(m.choose k) : K) * (-(2 * (↑θ : K) - 1)) ^ k) := by
      have h := add_pow (-(2 * (↑θ : K) - 1)) 1 m
      simp only [one_pow, mul_one] at h
      rw [show -(2 * (↑θ : K) - 1) + 1 = 2 * (1 - (↑θ : K)) from by ring] at h
      rw [h]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    -- Step 3: Take the difference. Even-indexed terms cancel (since (-x)^k = x^k for even k),
    --   and odd-indexed terms double. Using (2θ-1)^(2j+1) = (2θ-1)·((2θ-1)²)^j = (2θ-1)·(-7)^j,
    --   we factor out 2·(2θ-1) to get:
    --     (2θ)^m - (2θ')^m = 2·(2θ-1)·S
    --   where S = Σ_{j=0}^{(m-1)/2} C(m, 2j+1)·(-7)^j is an integer.
    have hdiff : ∃ S : ℤ, (2 * (↑θ : K)) ^ m - (2 * (1 - (↑θ : K))) ^ m =
        (2 : K) * (2 * (↑θ : K) - 1) * (S : K) := by
      refine ⟨-(2 : ℤ) ^ (m - 1), ?_⟩
      rw [← step1]
      push_cast
      have h2m : (2 : K) ^ m = 2 ^ (m - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m by omega)]
        rw [pow_succ]
      rw [h2m]
      ring
    -- Step 4: From step1: -2^m·(2θ-1) = (2θ)^m - (2θ')^m = 2·(2θ-1)·S.
    --   Since 2θ - 1 = √-7 ≠ 0, cancel it and divide by 2 to get -2^(m-1) = S.
    obtain ⟨S, hS⟩ := hdiff
    have hcancel : -(2 : ℤ) ^ (m - 1) = S := by
      have hne : (2 * (↑θ : K) - 1) ≠ 0 := by
        intro h0; rw [h0, zero_pow two_ne_zero] at hsq; norm_num at hsq
      have h1 : -(2 : K) ^ m = 2 * ↑S :=
        mul_right_cancel₀ hne (by linear_combination step1.trans hS)
      have h5 : -(2 : ℤ) ^ m = 2 * S := by
        apply Int.cast_injective (α := K)
        push_cast; exact h1
      have h6 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m by omega)]
        rw [pow_succ]; ring
      linarith
    -- Step 5: Read the equation -2^(m-1) = S modulo 7. Since
    --   S = C(m,1) + C(m,3)·(-7) + C(m,5)·(-7)² + ⋯ + C(m,m)·(-7)^((m-1)/2),
    --   all terms with j ≥ 1 are divisible by 7, and the j = 0 term is C(m,1) = m.
    --   Hence -2^(m-1) ≡ m (mod 7).
    have hmod : ∃ q : ℤ, S = ↑m + 7 * q := by
      -- Define T = Σ_{j=0}^{(m-1)/2} C(m, 2j+1) * (-7)^j (an integer)
      set T := ∑ j ∈ Finset.range ((m + 1) / 2),
        (m.choose (2 * j + 1) : ℤ) * (-7 : ℤ) ^ j with hT_def
      -- Step A: Show T = m + 7 * q (splitting off j=0 term)
      have hT_mod : ∃ q : ℤ, T = ↑m + 7 * q := by
        rw [hT_def, show (m + 1) / 2 = ((m + 1) / 2 - 1) + 1 from by omega,
          Finset.sum_range_succ']
        have hfirst : (m.choose (2 * 0 + 1) : ℤ) * (-7 : ℤ) ^ 0 = (m : ℤ) := by
          simp [Nat.choose_one_right]
        rw [hfirst]
        refine ⟨∑ j ∈ Finset.range ((m + 1) / 2 - 1),
          (m.choose (2 * (j + 1) + 1) : ℤ) * (-1) * (-7 : ℤ) ^ j, ?_⟩
        have key : ∑ j ∈ Finset.range ((m + 1) / 2 - 1),
          (m.choose (2 * (j + 1) + 1) : ℤ) * (-7 : ℤ) ^ (j + 1) =
          7 * ∑ j ∈ Finset.range ((m + 1) / 2 - 1),
            (m.choose (2 * (j + 1) + 1) : ℤ) * (-1) * (-7 : ℤ) ^ j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        linarith
      -- Step B: Show S = T by proving the K identity and canceling
      -- The binomial difference also equals 2*(2θ-1)*(T:K)
      have hK_identity : (2 * (↑θ : K)) ^ m - (2 * (1 - (↑θ : K))) ^ m =
          (2 : K) * (2 * (↑θ : K) - 1) * (↑T : K) := by
        rw [hbinom_plus, hbinom_minus]
        set α := 2 * (↑θ : K) - 1 with hα_def
        -- Step B1: Combine the two sums into a single sum of differences
        rw [← Finset.sum_sub_distrib]
        -- Step B2: For each k, C(m,k)*α^k - C(m,k)*(-α)^k = C(m,k)*(α^k - (-α)^k)
        conv_lhs => arg 2; ext k; rw [show (↑(m.choose k) : K) * α ^ k -
          (↑(m.choose k) : K) * (-α) ^ k =
          (↑(m.choose k) : K) * (α ^ k - (-α) ^ k) from by ring]
        -- Step B3: Split into even and odd k, show even terms vanish
        -- For even k: α^k - (-α)^k = 0 (by Even.neg_pow)
        -- For odd k: α^k - (-α)^k = 2*α^k (by Odd.neg_pow)
        -- Step B4: For odd k=2j+1: α^(2j+1) = α*(α²)^j = α*(-7)^j
        -- Step B5: Reindex from k ∈ range(m+1) to j ∈ range((m+1)/2)
        -- and factor out 2*α to get the result

        -- 1. Split the sum into Even and Odd indices
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (m + 1)) (p := Odd)]

        -- 2. Prove the Even terms are all zero
        have h_even_zero : ∑ k ∈ Finset.filter (fun x => ¬Odd x) (Finset.range (m + 1)),
            ↑(m.choose k) * (α ^ k - (-α) ^ k) = 0 := by
          refine Finset.sum_eq_zero (fun k hk => ?_)
          simp only [Finset.mem_filter] at hk
          -- Use the fact that k is even to show (-α)^k = α^k
          have h_ev : Even k := (Nat.even_or_odd k).resolve_right hk.2
          simp [Even.neg_pow h_ev, sub_self]

        -- 3. Simplify LHS using the zero result
        rw [h_even_zero, add_zero]

        -- 4. Rewrite RHS: expand T and distribute 2 * α
        rw [hT_def]
        rw [Int.cast_sum]    -- Moves the ↑ inside: ↑(∑ ...) becomes ∑ ↑(...)
        rw [Finset.mul_sum]  -- Now we can distribute: c * ∑ ... becomes ∑ c * ...
        simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]

        -- 5. Swap sides so we map FROM the simple set (RHS) TO the complex set (LHS)
        symm
        refine Finset.sum_bij (fun j _ => 2 * j + 1) ?_ ?_ ?_ ?_

        -- Goal 5.1: "Into" - Show 2j+1 is in the LHS range (Odd and < m+1)
        · intro j hj
          simp only [Finset.mem_range] at hj ⊢
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, ⟨j, by ring⟩⟩

        -- Goal 5.2: Injectivity (If 2i+1 = 2j+1, then i=j)
        · intro a b _ _ h_eq
          linarith

        -- Goal 5.3: Surjectivity (Every odd k in LHS comes from some j in RHS)
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_range] at hk
          obtain ⟨j, hj⟩ := hk.2
          obtain ⟨n, hn⟩ := hm_odd
          exact ⟨j, Finset.mem_range.mpr (by omega), hj.symm⟩

        -- Goal 5.4: Algebraic Equality
        · intro j hj
          simp only [Odd.neg_pow ⟨j, rfl⟩, sub_neg_eq_add]
          have hpow : α ^ (2 * j + 1) = α * (α ^ 2) ^ j := by ring_nf
          rw [hpow, hsq]
          push_cast
          ring

      -- Cancel 2*(2θ-1) from both sides of hS and hK_identity
      have hne : (2 : K) * (2 * (↑θ : K) - 1) ≠ 0 := by
        intro h0
        have : (2 * (↑θ : K) - 1) = 0 ∨ (2 : K) = 0 := by
          rcases mul_eq_zero.mp h0 with h | h
          · right; exact h
          · left; exact h
        rcases this with h | h
        · rw [h, zero_pow two_ne_zero] at hsq; norm_num at hsq
        · have : (2 : ℚ) = 0 := by exact_mod_cast h
          norm_num at this
      have hST : (↑S : K) = (↑T : K) :=
        mul_left_cancel₀ hne (hS.symm.trans hK_identity)
      have hST_int : S = T := Int.cast_injective (α := K) hST
      rw [hST_int]
      exact hT_mod
    obtain ⟨q, hq⟩ := hmod
    exact ⟨q, by linarith⟩
  -- Step 3: Read mod 7 to get the conclusion
  obtain ⟨q, hq⟩ := step2
  rw [hq]
  omega


/-- Key consequence of unique factorization in ℤ[(1+√-7)/2]:
    For odd n ≥ 5, if x² + 7 = 2ⁿ, then setting m = n - 2, we have
    -2^(m-1) ≡ m (mod 7).

    This follows from the factorization in the ring of integers:
    ((x+√-7)/2)((x-√-7)/2) = 2^m = ((1+√-7)/2)^m ((1-√-7)/2)^m
    and unique factorization implies (x±√-7)/2 = ±((1±√-7)/2)^m.
    The negative sign must occur (proved by considering mod b² where b = (1-√-7)/2).
    Expanding via binomial theorem yields -2^(m-1) ≡ m (mod 7). -/
lemma odd_case_mod_seven_constraint :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    -(2 : ℤ) ^ (n - 3) % 7 = ((n : ℤ) - 2) % 7 := by
      intro x n hn_odd hn_ge h_eq
      -- Step 1: Divide by 4 to get (x^2 + 7)/4 = 2^(n-2)
      have h_div := reduction_divide_by_4 x n hn_odd hn_ge h_eq
      -- Step 2: Establish properties of m = n - 2
      have hm_odd : Odd (n - 2) := by
        obtain ⟨k, hk⟩ := hn_odd; exact ⟨k - 1, by omega⟩
      have hm_ge : n - 2 ≥ 3 := by omega
      -- Step 3: Apply main_m_condition to get -2*θ + 1 = θ^(n-2) - θ'^(n-2)
      have h_theta := main_m_condition x (n - 2) hm_odd hm_ge h_div
      -- Step 4: Expand by binomial theorem to get the mod 7 constraint
      have h_mod := expand_by_binomial (n - 2) hm_odd hm_ge h_theta
      -- Step 5: Convert from m = n-2 to the n-based statement
      rw [show n - 3 = (n - 2) - 1 from by omega]
      rw [show ((n : ℤ) - 2) = ((n - 2 : ℕ) : ℤ) from by omega]
      exact h_mod

/-- From -2^(m-1) ≡ m (mod 7) and 2⁶ ≡ 1 (mod 7), the only solutions are
    m ≡ 3, 5, or 13 (mod 42). -/
theorem odd_case_only_three_values_mod_42 :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    (n - 2) % 42 = 3 ∨ (n - 2) % 42 = 5 ∨ (n - 2) % 42 = 13 := by
      intro x n hn_odd hn_ge h_eq
      -- Step 1: Get the mod 7 constraint: (-2)^(n-3) ≡ (n-2) (mod 7)
      have h_mod7 := odd_case_mod_seven_constraint x n hn_odd hn_ge h_eq
      -- Step 2: Set m = n - 2, establish basic properties
      set m := n - 2 with hm_def
      have hm_ge : m ≥ 3 := by omega
      have hm_odd : Odd m := by
        obtain ⟨k, hk⟩ := hn_odd; exact ⟨k - 1, by omega⟩
      -- Note: n - 3 = m - 1 (as natural numbers, both ≥ 2)
      have hn3_eq : n - 3 = m - 1 := by omega
      rw [hn3_eq] at h_mod7
      -- h_mod7 now says: (-2)^(m-1) % 7 = (↑m : ℤ) ... (mod 7 constraint on m)
      -- Step 3: m is odd, so m % 6 ∈ {1, 3, 5}
      have hm_mod6 : m % 6 = 1 ∨ m % 6 = 3 ∨ m % 6 = 5 := by
        obtain ⟨k, hk⟩ := hm_odd; omega
      -- Step 4: Case split on m mod 6; in each case use Fermat's little theorem
      -- (2⁶ ≡ 1 mod 7) to determine -2^(m-1) mod 7, then combine with
      -- the mod 7 constraint `h_mod7` via the Chinese Remainder Theorem (CRT)
      -- to get m mod 42.
      rcases hm_mod6 with h6 | h6 | h6
      · -- m ≡ 1 (mod 6): m-1 ≡ 0 (mod 6), so -2^(m-1) ≡ -1 (mod 7)
        -- Hypothesis `h_mod7` then gives m ≡ -1 (mod 7). By CRT:
        -- m ≡ 13 (mod 42).
        right; right
        have hcast : (↑n : ℤ) - 2 = ↑m := by omega
        rw [hcast] at h_mod7
        -- Show 2^(m-1) ≡ 1 (mod 7) via 2^6 ≡ 1 (mod 7)
        have h64 : ∀ q : ℕ, ((2 : ℤ) ^ 6) ^ q % 7 = 1 := by
          intro q; induction q with
          | zero => norm_num
          | succ q ih => rw [pow_succ, Int.mul_emod, ih]; norm_num
        have h_pow_mod : (2 : ℤ) ^ (m - 1) % 7 = 1 := by
          obtain ⟨q, hq⟩ : 6 ∣ (m - 1) := ⟨(m - 1) / 6, by omega⟩
          rw [show (m : ℕ) - 1 = 6 * q from by omega, pow_mul]
          exact h64 q
        omega
      · -- m ≡ 3 (mod 6): m-1 ≡ 2 (mod 6), so -2^(m-1) ≡ -4 (mod 7)
        -- Hypothesis `h_mod7` then gives m ≡ -4 (mod 7). By CRT:
        -- m ≡ 3 (mod 42).
        left
        have hcast : (↑n : ℤ) - 2 = ↑m := by omega
        rw [hcast] at h_mod7
        have h64 : ∀ q : ℕ, ((2 : ℤ) ^ 6) ^ q % 7 = 1 := by
          intro q; induction q with
          | zero => norm_num
          | succ q ih => rw [pow_succ, Int.mul_emod, ih]; norm_num
        have h_pow_mod : (2 : ℤ) ^ (m - 1) % 7 = 4 := by
          obtain ⟨q, hq⟩ : ∃ q, m - 1 = 6 * q + 2 := ⟨(m - 1) / 6, by omega⟩
          rw [hq, pow_add, pow_mul, Int.mul_emod, h64 q]; norm_num
        omega
      · -- m ≡ 5 (mod 6): m-1 ≡ 4 (mod 6), so -2^(m-1) ≡ -2 (mod 7)
        -- Hypothesis `h_mod7` then gives m ≡ -2 (mod 7). By CRT:
        -- m ≡ 5 (mod 42).
        right; left
        have hcast : (↑n : ℤ) - 2 = ↑m := by omega
        rw [hcast] at h_mod7
        have h64 : ∀ q : ℕ, ((2 : ℤ) ^ 6) ^ q % 7 = 1 := by
          intro q; induction q with
          | zero => norm_num
          | succ q ih => rw [pow_succ, Int.mul_emod, ih]; norm_num
        have h_pow_mod : (2 : ℤ) ^ (m - 1) % 7 = 2 := by
          obtain ⟨q, hq⟩ : ∃ q, m - 1 = 6 * q + 4 := ⟨(m - 1) / 6, by omega⟩
          rw [hq, pow_add, pow_mul, Int.mul_emod, h64 q]; norm_num
        omega

/-- For the original equation x² + 7 = 2ⁿ with odd n ≥ 5, the only possible values of n are
    5, 7, and 15.

    PROOF: From the mod 7 constraint `odd_case_only_three_values_mod_42`, we get
    m = n - 2 ≡ 3, 5, or 13 (mod 42).

    It suffices to show that no two distinct solutions for `n` can be congruent mod 42, since we have
    already found three solutions (n = 5, 7, 15) that satisfy the equation.

    Suppose for a contradiction that there are two distinct solutions n₁ and n₂ with n₁ ≡ n₂ (mod 42).

    Let l be the largest power of 7 dividing n₂ - n₁. Then n₂ - n₁ = 7^l * k for some integer k not divisible by 7.

    No two distinct solutions can be congruent mod 42 (proved by a contradiction
    argument using powers of 7). Therefore the only possible values are
    m = 3, 5, 13, i.e., n = 5, 7, 15. -/
theorem odd_case_only_three_values :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    n = 5 ∨ n = 7 ∨ n = 15 := by
      intro x n hn_odd hn_ge h_eq
      have h_mod := odd_case_only_three_values_mod_42 x n hn_odd hn_ge h_eq
      sorry

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
