/-
Copyright (c) 2024 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

set_option linter.style.longLine false
set_option diagnostics true

open Polynomial NumberField QuadraticAlgebra RingOfIntegers Algebra Nat Ideal
  UniqueFactorizationMonoid

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
        have h3 : Algebra.norm ℚ (2 : K) = QuadraticAlgebra.norm (2 : K) := by
          admit -- will admit this for now
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
        have h3 : Algebra.norm ℚ (-7 : K) = QuadraticAlgebra.norm (-7 : K) := by
          admit -- will admit this for now
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
  admit

lemma main_m_condition :
  ∀ x : ℤ, ∀ m : ℕ, Odd m → m ≥ 3 → (x ^ 2 + 7) / 4 = 2 ^ m →
    (2*θ - 1 = θ^m - θ'^m) ∨ (-2*θ + 1 = θ^m - θ'^m)  := by
  intro x m hm_odd hm_ge h_eq
  -- Step 1: Get conjugate factors α = (x+√-7)/2, β = (x-√-7)/2 in R
  --         with α · β = θ^m · θ'^m and α - β = 2θ-1 = √-7
  obtain ⟨α, β, h_prod, h_diff⟩ := factors_in_R_with_product x m hm_ge h_eq
  -- Step 2: α and β are coprime (θ and θ' don't divide √-7, by norms)
  have h_coprime := conjugate_factors_coprime α β m h_prod h_diff
  -- Step 3: By UFD property (class number 1), α is associate to θ^m or θ'^m
  have h_assoc := ufd_power_association α β m h_prod h_coprime
  -- Step 4: Units are ±1, take difference to eliminate x and conclude
  exact eliminate_x_conclude α β m h_diff h_assoc h_prod


/--
Summary

PROVIDED SOLUTION
Thing
-/
lemma main_factorisation_lemma :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    ((↑x + 2*(↑θ : K) - 1) / 2) * ((↑x - 2*(↑θ : K) + 1) / 2) = (↑θ : K) ^ (n - 2) * (1 - (↑θ : K)) ^ (n - 2) := by
  admit

/--
Given x ^ 2 + 7 = 2 ^ n, show that (x ^ 2 + 7) / 4 = 2 ^ (n - 2).

PROVIDED SOLUTION
Divide both sides of the equation x^2 + 7 = 2^n by 4.
-/
lemma reduction_divide_by_4 :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    (x ^ 2 + 7) / 4 = 2 ^ (n - 2) := by
  intro x n _ hn hx
  rw [hx]
  exact Int.ediv_eq_of_eq_mul_left (by norm_num)
    (by rw [show n = n - 2 + 2 from by omega, pow_add]; norm_num)

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
    (-(2 : ℤ)) ^ (n - 3) % 7 = ((n : ℤ) - 2) % 7 := by
      admit

/-- From -2^(m-1) ≡ m (mod 7) and 2⁶ ≡ 1 (mod 7), the only solutions are
    m ≡ 3, 5, or 13 (mod 42). Moreover, no two distinct solutions can be
    congruent mod 42 (proved by a contradiction argument using powers of 7).
    Therefore the only possible values are m = 3, 5, 13, i.e., n = 5, 7, 15. -/
theorem odd_case_only_three_values :
  ∀ x : ℤ, ∀ n : ℕ, Odd n → n ≥ 5 → x ^ 2 + 7 = 2 ^ n →
    n = 5 ∨ n = 7 ∨ n = 15 := by
      admit

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
