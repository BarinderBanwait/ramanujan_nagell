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
revision, 380 lines in the version before Stoll suggested it) reduces to ~30
lines via the `4·N = (2x+y)² + 7y²` identity.

The `EuclideanDomain R` instance is constructed in full via smart rounding:
pick `n := round(s.im / N)`, then `m := round((s.re/N) + (im residual)/2)`. This
"shifted re-rounding" handles the corner `(1/2, 1/2)` where naive independent
rounding would give `norm = 1` exactly. With this choice the remainder always
satisfies `16·norm(rem) ≤ 11·norm(b)`. From `EuclideanDomain R`, both
`IsPrincipalIdealRing R` and `UniqueFactorizationMonoid R` follow immediately,
giving `theta_prime` and `theta'_prime`.
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
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

/-! ## EuclideanDomain instance

Construction follows the GaussianInt template (mathlib
`NumberTheory/Zsqrtd/GaussianInt.lean:229`), specialized to the integer ring
`R = ℤ[(1+√-7)/2]`. The subtlety relative to Gaussian integers: the
norm-form `x² + xy + 2y²` over the fundamental parallelogram `[-1/2, 1/2]²`
peaks at `1` exactly at the corners `(±1/2, ±1/2)`, so naive nearest-integer
rounding can give `norm = 1`, not `< 1`. The fix: rather than rounding each
coordinate independently, round the `im` component first (`n := round(im/N)`),
then round the `re` component shifted by half the residual:
`m := round((re/N) + (im/N - n) / 2)`. Let `u := re - N·m`, `v := im - N·n`.
Then `|v| ≤ N/2` and `|2u + v| ≤ N`, so
  `4 · (u² + uv + 2v²) = (2u+v)² + 7v² ≤ N² + 7N²/4 = 11N²/4 < 4N²`,
giving `u² + uv + 2v² < N²`, i.e. `N · norm(rem) < N²`, i.e. `norm(rem) < N`.

The proof below is sorry-free. -/

/-- Positive-definiteness: `norm z = 0 ↔ z = 0` over `R`. -/
lemma norm_eq_zero_iff (z : R) : QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ QuadraticAlgebra.norm_zero⟩
  have h4 := four_norm_eq z
  rw [h] at h4
  have hv : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]
  have hu : z.re = 0 := by nlinarith [h4, hv, sq_nonneg z.re]
  exact QuadraticAlgebra.ext hu hv

lemma norm_pos {z : R} (hz : z ≠ 0) : 0 < QuadraticAlgebra.norm z := by
  rcases lt_or_eq_of_le (norm_nonneg z) with h | h
  · exact h
  · exact absurd ((norm_eq_zero_iff z).mp h.symm) hz

/-- `b * star b` equals the norm cast back into `R`. Cornerstone of the
norm-cancellation argument below. -/
private lemma b_mul_star_eq_norm (b : R) :
    b * star b = ((QuadraticAlgebra.norm b : ℤ) : R) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.norm_def, Int.cast_id]
    ring
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.im_intCast]
    ring

/-- The algebraic core of the Euclidean argument:
    `N · (a − b·q) = b · (a · star b − N · q)` for any `q : R`. -/
private lemma N_mul_rem_eq (a b q : R) :
    ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q) =
      b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hbs := b_mul_star_eq_norm b
  calc ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)
      = (b * star b) * (a - b * q) := by rw [← hbs]
    _ = b * (a * star b - (b * star b) * q) := by ring
    _ = b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by rw [hbs]

/-- Taking norms of the identity above and cancelling one `N` from both sides:
    `N · norm(a − b·q) = norm(a · star b − N · q)`. -/
private lemma N_mul_norm_rem_eq (a b q : R) (hb : b ≠ 0) :
    QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q) =
      QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hN_ne : QuadraticAlgebra.norm b ≠ 0 := hN_pos.ne'
  have h_key := N_mul_rem_eq a b q
  have h_norm : QuadraticAlgebra.norm
      (((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)) =
      QuadraticAlgebra.norm
      (b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q)) := by
    rw [h_key]
  rw [map_mul, map_mul, QuadraticAlgebra.norm_intCast] at h_norm
  -- h_norm : N^2 * norm (a-b*q) = N * norm (a·star b - N·q); cancel N.
  have h_sq : (QuadraticAlgebra.norm b) ^ 2 =
              QuadraticAlgebra.norm b * QuadraticAlgebra.norm b := sq _
  have : QuadraticAlgebra.norm b *
         (QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q)) =
         QuadraticAlgebra.norm b *
         QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
    rw [← mul_assoc, ← h_sq]
    exact h_norm
  exact mul_left_cancel₀ hN_ne this

/-- The "smart-rounded" quotient: pick `n` rounding `s.im / N`, then pick `m`
rounding `s.re / N` shifted by half the `n`-residual. -/
noncomputable def quot (a b : R) : R :=
  let N : ℤ := QuadraticAlgebra.norm b
  if N = 0 then 0
  else
    let s : R := a * star b
    let n : ℤ := round ((s.im : ℚ) / N)
    let m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N))
    ⟨m, n⟩

noncomputable def rem (a b : R) : R := a - b * quot a b

@[simp] lemma quot_zero (a : R) : quot a 0 = 0 := by unfold quot; simp

lemma quot_mul_add_rem_eq (a b : R) : b * quot a b + rem a b = a := by
  unfold rem; ring

/-- Norm bound: `16 · norm (rem a b) ≤ 11 · norm b`. -/
private lemma sixteen_norm_rem_le (a b : R) (hb : b ≠ 0) :
    16 * QuadraticAlgebra.norm (rem a b) ≤ 11 * QuadraticAlgebra.norm b := by
  set N := QuadraticAlgebra.norm b with hN_def
  have hN_pos : 0 < N := norm_pos hb
  have hN_ne : N ≠ 0 := hN_pos.ne'
  -- Unfold `quot a b` to `⟨m, n⟩`.
  set s : R := a * star b with hs_def
  set n : ℤ := round ((s.im : ℚ) / N) with hn_def
  set m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N)) with hm_def
  have hquot : quot a b = (⟨m, n⟩ : R) := by
    change (if QuadraticAlgebra.norm b = 0 then (0 : R) else _) = _
    rw [if_neg hN_ne]
  -- Integer residuals u, v.
  set u : ℤ := s.re - N * m with hu_def
  set v : ℤ := s.im - N * n with hv_def
  have hNq_pos : (0 : ℚ) < N := by exact_mod_cast hN_pos
  have hNq : (N : ℚ) ≠ 0 := hNq_pos.ne'
  have h2Nq_pos : (0 : ℚ) < 2 * N := by linarith
  -- Bound 1: |2v| ≤ N  (i.e. (2v)² ≤ N²)
  have hv_bd : (2 * v) ^ 2 ≤ N ^ 2 := by
    have habs : |(s.im : ℚ) / N - n| ≤ 1 / 2 := abs_sub_round _
    have heq : ((s.im : ℚ) / N - n) * (2 * N) = ((2 * v : ℤ) : ℚ) := by
      push_cast [hv_def]; field_simp
    have h_abs_2v : |((2 * v : ℤ) : ℚ)| ≤ N := by
      rw [← heq, abs_mul, abs_of_pos h2Nq_pos]
      have := mul_le_mul_of_nonneg_right habs h2Nq_pos.le
      linarith
    have h_sq : ((2 * v : ℤ) : ℚ) ^ 2 ≤ (N : ℚ) ^ 2 := by
      have hsa : ((2 * v : ℤ) : ℚ) ^ 2 = |((2 * v : ℤ) : ℚ)| ^ 2 := (sq_abs _).symm
      rw [hsa]
      exact sq_le_sq' (by linarith [abs_nonneg ((2 * v : ℤ) : ℚ)]) h_abs_2v
    exact_mod_cast h_sq
  -- Bound 2: |2u + v| ≤ N  (i.e. (2u+v)² ≤ N²)
  have huv_bd : (2 * u + v) ^ 2 ≤ N ^ 2 := by
    have habs : |(2 * (s.re : ℚ) + s.im - N * n) / (2 * N) - m| ≤ 1 / 2 := abs_sub_round _
    have heq : ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N) - m) * (2 * N) =
               ((2 * u + v : ℤ) : ℚ) := by
      push_cast [hu_def, hv_def]; field_simp; ring
    have h_abs : |((2 * u + v : ℤ) : ℚ)| ≤ N := by
      rw [← heq, abs_mul, abs_of_pos h2Nq_pos]
      have := mul_le_mul_of_nonneg_right habs h2Nq_pos.le
      linarith
    have h_sq : ((2 * u + v : ℤ) : ℚ) ^ 2 ≤ (N : ℚ) ^ 2 := by
      have hsa : ((2 * u + v : ℤ) : ℚ) ^ 2 = |((2 * u + v : ℤ) : ℚ)| ^ 2 := (sq_abs _).symm
      rw [hsa]
      exact sq_le_sq' (by linarith [abs_nonneg ((2 * u + v : ℤ) : ℚ)]) h_abs
    exact_mod_cast h_sq
  -- N · norm (rem a b) = u² + u·v + 2·v²
  have h_chain : N * QuadraticAlgebra.norm (rem a b) = u ^ 2 + u * v + 2 * v ^ 2 := by
    unfold rem
    rw [hquot]
    have h := N_mul_norm_rem_eq a b (⟨m, n⟩ : R) hb
    rw [h]
    -- Now compute norm (a * star b - (N : R) * ⟨m, n⟩) explicitly.
    have hre : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).re = u := by
      change s.re - (((N : ℤ) : R) * (⟨m, n⟩ : R)).re = u
      push_cast [hu_def]
      change s.re - (N * m + (-2) * 0 * n) = s.re - N * m
      ring
    have him : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).im = v := by
      change s.im - (((N : ℤ) : R) * (⟨m, n⟩ : R)).im = v
      push_cast [hv_def]
      change s.im - (N * n + 0 * m + 1 * 0 * n) = s.im - N * n
      ring
    rw [QuadraticAlgebra.norm_def, hre, him]; ring
  -- Combine: 16·(u² + uv + 2v²) = 4·(2u+v)² + 7·(2v)² ≤ 11·N²
  have h_alg : 16 * (u ^ 2 + u * v + 2 * v ^ 2) = 4 * (2 * u + v) ^ 2 + 7 * (2 * v) ^ 2 := by
    ring
  have h_bd : 16 * (u ^ 2 + u * v + 2 * v ^ 2) ≤ 11 * N ^ 2 := by
    rw [h_alg]; nlinarith [hv_bd, huv_bd]
  -- 16·N·norm rem = 16·(u² + uv + 2v²) ≤ 11·N² ⇒ 16·norm rem ≤ 11·N
  have hN_sq : N ^ 2 = N * N := sq N
  nlinarith [h_chain, h_bd, hN_pos]

private noncomputable def measure (a : R) : ℕ := Int.natAbs (QuadraticAlgebra.norm a)

private lemma natAbs_norm_rem_lt (a : R) {b : R} (hb : b ≠ 0) :
    measure (rem a b) < measure b := by
  unfold measure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hr_nn : 0 ≤ QuadraticAlgebra.norm (rem a b) := norm_nonneg _
  have h_bd := sixteen_norm_rem_le a b hb
  have hr_lt : QuadraticAlgebra.norm (rem a b) < QuadraticAlgebra.norm b := by linarith
  zify
  rw [abs_of_nonneg hr_nn, abs_of_nonneg hN_pos.le]
  exact hr_lt

private lemma norm_mul_left_not_lt (a : R) {b : R} (hb : b ≠ 0) :
    ¬ measure (a * b) < measure a := by
  unfold measure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have ha_nn : 0 ≤ QuadraticAlgebra.norm a := norm_nonneg a
  have hab : QuadraticAlgebra.norm (a * b) =
             QuadraticAlgebra.norm a * QuadraticAlgebra.norm b := map_mul _ _ _
  have hab_nn : 0 ≤ QuadraticAlgebra.norm (a * b) := hab ▸ mul_nonneg ha_nn hN_pos.le
  intro h
  zify at h
  rw [abs_of_nonneg hab_nn, abs_of_nonneg ha_nn, hab] at h
  nlinarith [ha_nn, hN_pos]

noncomputable instance instEuclideanDomain : EuclideanDomain R where
  quotient := quot
  quotient_zero := quot_zero
  remainder := rem
  quotient_mul_add_remainder_eq := quot_mul_add_rem_eq
  r := fun a b => measure a < measure b
  r_wellFounded := (_root_.measure measure).wf
  remainder_lt := natAbs_norm_rem_lt
  mul_left_not_lt := norm_mul_left_not_lt

instance : IsPrincipalIdealRing R := EuclideanDomain.to_principal_ideal_domain

instance : UniqueFactorizationMonoid R := inferInstance

/-! ## θ and θ' are prime

In a UFD, irreducible ⟺ prime. -/

lemma theta_prime : Prime θ :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta_irreducible

lemma theta'_prime : Prime θ' :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp theta'_irreducible

end RamanujanNagell.Prototype
