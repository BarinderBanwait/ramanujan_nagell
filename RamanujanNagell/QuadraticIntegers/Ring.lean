/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait

Standalone Phase B prototype validating Michael Stoll's suggestion to refactor
the Ramanujan-Nagell formalization onto the ring `R := QuadraticAlgebra ℤ (-2) 1`
directly (rather than through `𝓞 K` where `K = QuadraticAlgebra ℚ (-2) 1`).

This file imports ONLY mathlib — it does NOT depend on any other file in this
project. It is intended to be reviewed alongside the legacy `Helpers.lean` to
demonstrate the proof-length and conceptual-simplicity gains from following
Stoll's advice.

Status of Stoll's claims (each is a literal `rfl` in this file):
  ✓ `θ ^ 2 = θ - 2`
  ✓ `θ * θ' = 2`
  ✓ `θ + θ' = 1`
  ✓ `norm θ = 2`
  ✓ `norm θ' = 2`

The norm-form proof of `units_pm_one` (was 89 lines in the latest Helpers.lean
revision, 380 lines in the version before Stoll suggested it) reduces to ~15
lines via the `4·N = (2x+y)² + 7y²` identity.

The substantive remaining work is the `EuclideanDomain` instance, which is
the GaussianInt-style construction with one extra subtlety: at the corner
`(1/2, 1/2)` of the fundamental parallelogram, naive rounding gives `norm = 1`
exactly (not `< 1`), so the rounding rule needs a small adjustment. That work
is staged separately and is not in this prototype.
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

namespace RamanujanNagell.Prototype

open QuadraticAlgebra

/-- The integer ring `ℤ[(1 + √-7)/2]`, packaged as `QuadraticAlgebra ℤ (-2) 1`.
The generator `ω = ⟨0, 1⟩` satisfies `ω² = -2 + ω` (i.e. `ω² - ω + 2 = 0`). -/
abbrev R : Type := QuadraticAlgebra ℤ (-2) 1

/-- `θ = ω = (1 + √-7)/2`. -/
def θ : R := ⟨0, 1⟩

/-- `θ' = 1 - θ = (1 - √-7)/2`, the Galois conjugate of θ. -/
def θ' : R := ⟨1, -1⟩

/-! ## Stoll's `rfl` claims

The whole point of working over `ℤ` (rather than `𝓞 K`) is that these become
`rfl`. In the old codebase these required `Subtype.ext` and several rewrites
through `omega_mul_omega_eq_mk`. -/

example : θ ^ 2 = θ - 2 := rfl

example : θ * θ' = 2 := rfl

example : θ' * θ = 2 := rfl

example : θ + θ' = 1 := rfl

example : QuadraticAlgebra.norm θ = 2 := rfl

example : QuadraticAlgebra.norm θ' = 2 := rfl

/-! ## Norm form and positivity

For our specific parameters `(a, b) = (-2, 1)`, the norm formula specializes to
`norm ⟨x, y⟩ = x² + xy + 2y²`. The key identity for everything below is
`4·norm ⟨x, y⟩ = (2x + y)² + 7y²`, which makes the norm visibly nonnegative
and lets us solve `norm = ±1` by inspection. -/

lemma norm_eq (x y : ℤ) : QuadraticAlgebra.norm (⟨x, y⟩ : R) = x ^ 2 + x * y + 2 * y ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

/-- The completing-the-square identity. -/
lemma four_norm_eq (z : R) :
    4 * QuadraticAlgebra.norm z = (2 * z.re + z.im) ^ 2 + 7 * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring

lemma norm_nonneg (z : R) : 0 ≤ QuadraticAlgebra.norm z := by
  have h := four_norm_eq z
  have h1 : 0 ≤ (2 * z.re + z.im) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 7 * z.im ^ 2 := by positivity
  linarith

/-! ## Units are ±1

Stoll's argument (Section: "The unit group"): if `u : Rˣ` then `norm u = ±1`.
Since `norm` is nonnegative, only `norm u = 1` is possible. Completing the
square forces `z.im = 0` and `z.re = ±1`. -/

lemma units_pm_one (u : Rˣ) : u = 1 ∨ u = -1 := by
  -- Step 1: `norm u` is a unit in ℤ, hence `±1`. By `norm_nonneg`, `norm u = 1`.
  have hunit : IsUnit (QuadraticAlgebra.norm (u : R)) :=
    QuadraticAlgebra.isUnit_iff_norm_isUnit.mp u.isUnit
  rcases Int.isUnit_iff.mp hunit with hn | hn
  · -- `norm u = 1`. Use `4·N = (2x+y)² + 7y²` to extract `y = 0` and `x = ±1`.
    set x := (u : R).re
    set y := (u : R).im
    have hcoord : (u : R) = ⟨x, y⟩ := by
      apply QuadraticAlgebra.ext <;> rfl
    have hn' : x ^ 2 + x * y + 2 * y ^ 2 = 1 := by
      rw [show x = (⟨x, y⟩ : R).re from rfl, show y = (⟨x, y⟩ : R).im from rfl,
          ← norm_eq]
      rw [← hcoord]; exact hn
    have h_csq : (2 * x + y) ^ 2 + 7 * y ^ 2 = 4 := by linarith
    have hy : y = 0 := by nlinarith [sq_nonneg y, sq_nonneg (2 * x + y)]
    have hx2 : x ^ 2 = 1 := by nlinarith
    have hx : x = 1 ∨ x = -1 := by
      have hfact : (x - 1) * (x + 1) = 0 := by linarith [hx2]
      rcases mul_eq_zero.mp hfact with h | h
      · left; omega
      · right; omega
    rcases hx with hx1 | hx1
    · left
      apply Units.ext
      rw [hcoord, hx1, hy]; rfl
    · right
      apply Units.ext
      rw [hcoord, hx1, hy]; rfl
  · -- `norm u = -1` contradicts `norm_nonneg`.
    exfalso
    have := norm_nonneg (u : R)
    omega

/-! ## θ and θ' are irreducible (norm-is-prime argument)

If `θ = a * b` then `norm θ = norm a * norm b`, so `2 = norm a * norm b`. Since
2 is prime in ℤ, one of `|norm a|, |norm b|` equals 1, hence one of `a, b` is a
unit. -/

/-- Given two nonneg integers `m, n` with `m * n = 2`, one of them is `1`. -/
private lemma norm_factor_dichotomy {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) (hmn : m * n = 2) :
    m = 1 ∨ n = 1 := by
  -- m ≥ 0 and m * n = 2 force m ∈ {1, 2}; n is then 2 or 1 respectively.
  have hm_pos : 0 < m := by
    rcases lt_or_eq_of_le hm with h | h
    · exact h
    · exfalso; rw [← h, zero_mul] at hmn; exact absurd hmn (by decide)
  have hn_pos : 0 < n := by
    rcases lt_or_eq_of_le hn with h | h
    · exact h
    · exfalso; rw [← h, mul_zero] at hmn; exact absurd hmn (by decide)
  have hm_le : m ≤ 2 := by nlinarith
  interval_cases m
  · left; rfl
  · right; linarith

private lemma isUnit_of_norm_one {a : R} (h : QuadraticAlgebra.norm a = 1) : IsUnit a := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  rw [h]; exact isUnit_one

lemma theta_irreducible : Irreducible θ := by
  refine ⟨?_, ?_⟩
  · -- θ is not a unit (its norm is 2, not ±1)
    intro hu
    have h1 : IsUnit (QuadraticAlgebra.norm θ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    have h2 : IsUnit (2 : ℤ) := h1
    exact absurd (Int.isUnit_iff.mp h2) (by decide)
  · -- If θ = a * b then one of a, b is a unit
    intro a b hab
    have hnab : QuadraticAlgebra.norm a * QuadraticAlgebra.norm b = 2 := by
      rw [← map_mul, ← hab]; rfl
    rcases norm_factor_dichotomy (norm_nonneg a) (norm_nonneg b) hnab with h | h
    · exact Or.inl (isUnit_of_norm_one h)
    · exact Or.inr (isUnit_of_norm_one h)

lemma theta'_irreducible : Irreducible θ' := by
  refine ⟨?_, ?_⟩
  · intro hu
    have h1 : IsUnit (QuadraticAlgebra.norm θ') := QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu
    have h2 : IsUnit (2 : ℤ) := h1
    exact absurd (Int.isUnit_iff.mp h2) (by decide)
  · intro a b hab
    have hnab : QuadraticAlgebra.norm a * QuadraticAlgebra.norm b = 2 := by
      rw [← map_mul, ← hab]; rfl
    rcases norm_factor_dichotomy (norm_nonneg a) (norm_nonneg b) hnab with h | h
    · exact Or.inl (isUnit_of_norm_one h)
    · exact Or.inr (isUnit_of_norm_one h)

/-! ## EuclideanDomain (TODO: replace `sorry` with the GaussianInt-style construction)

The recipe follows `Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean:229`: embed
into `K = QuadraticAlgebra ℚ (-2) 1`, define `div` by rounding to nearest lattice
point of `R`, define `mod` as `a - b * (a / b)`, then prove
`|norm (a % b)| < |norm b|`. The proof reduces to: for any `z ∈ K`, the nearest
element of `R` has `norm (z - nearest z) < 1`.

For our `(a, b) = (-2, 1)`, the maximum of `x² + xy + 2y²` over the fundamental
parallelogram `[-1/2, 1/2]²` is exactly 1, attained at the corners. So naive
rounding sometimes gives `norm = 1` (not `< 1`). The fix: at those corners,
shift to a different lattice point — the standard argument for the Heegner-style
imaginary norm-Euclidean rings of discriminant `-7`.

Until that lands, the instance is `sorry`-ed below. Downstream lemmas (PID, UFD,
`Prime θ`, `Prime θ'`) consume only the `EuclideanDomain` API, so they will
become non-`sorry` automatically once the instance is filled in. -/

noncomputable instance instEuclideanDomain : EuclideanDomain R where
  quotient := sorry
  quotient_zero := sorry
  remainder := sorry
  quotient_mul_add_remainder_eq := sorry
  r := sorry
  r_wellFounded := sorry
  remainder_lt := sorry
  mul_left_not_lt := sorry

-- These derived instances are immediate from `EuclideanDomain`; they become
-- unconditional once the `sorry`s above are filled.
instance : IsPrincipalIdealRing R := EuclideanDomain.to_principal_ideal_domain

instance : UniqueFactorizationMonoid R := inferInstance

/-! ## θ and θ' are prime

In a UFD, irreducible ⟺ prime. -/

lemma theta_prime : Prime θ :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta_irreducible

lemma theta'_prime : Prime θ' :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta'_irreducible

end RamanujanNagell.Prototype
