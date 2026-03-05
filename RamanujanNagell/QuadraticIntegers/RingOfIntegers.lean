/-
Copyright (c) 2026 Barinder S. Banwait. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Barinder S. Banwait

Attribution: This file is adapted from
  ~/Documents/QuadraticIntegers/QuadraticIntegers/RingOfIntegers.lean
The theorem `ring_of_integers_neg7` is the specialisation of `QuadraticInteger.d_1` at
d = -7, e = (d-1)/4 = -2, giving `IsIntegralClosure (QuadraticAlgebra ℤ (-2) 1) ℤ K'`.
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.NumberField.Basic

open QuadraticAlgebra

noncomputable section

/-! ## The field ℚ(√-7) presented as QuadraticAlgebra ℚ (-7) 0

In this presentation ω' satisfies (ω')² = -7 + 0·ω' = -7, so ω' = √(-7).
-/

notation "K'" => QuadraticAlgebra ℚ (-7 : ℤ) 0

/-! ## Algebra instance: QuadraticAlgebra ℤ (-2) 1 → K'

The ring map sends the ℤ-generator ω_int (satisfying ω_int² = -2 + ω_int) to
(1 + ω')/2 in K', where ω' satisfies (ω')² = -7. Indeed:
  ((1 + ω')/2)² = (1 + 2ω' + (ω')²)/4 = (1 + 2ω' - 7)/4 = (-6 + 2ω')/4
                = -3/2 + ω'/2
  -2 + 1·((1 + ω')/2) = -2 + 1/2 + ω'/2 = -3/2 + ω'/2  ✓
This is `QuadraticInteger.d_1`'s algebra instance at d = -7, e = -2.
-/
noncomputable instance algebraIntZ_K' : Algebra (QuadraticAlgebra ℤ (-2 : ℤ) 1) K' := by
  sorry

/-! ## The ring of integers of K'

Specialisation of `QuadraticInteger.d_1` at d = -7, e = -2:
- d = -7 ≡ 1 [ZMOD 4]  (since -7 = 4·(-2) + 1)
- e = (d - 1)/4 = (-7 - 1)/4 = -2
- S = QuadraticAlgebra ℤ e 1 = QuadraticAlgebra ℤ (-2) 1

This is exactly the ring ℤ[θ] in our main file (where θ satisfies θ² = θ - 2),
which is the ring of integers of ℚ(√-7) since disc(θ² - θ + 2) = 1 - 8 = -7.
-/
theorem ring_of_integers_neg7 : IsIntegralClosure (QuadraticAlgebra ℤ (-2 : ℤ) 1) ℤ K' := by
  -- This is QuadraticInteger.d_1 specialised at d = -7.
  -- The hypothesis d ≡ 1 [ZMOD 4] holds since -7 ≡ 1 [ZMOD 4] (i.e. -7 - 1 = -8 = 4 · (-2)).
  sorry

end
