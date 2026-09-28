/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
import GradientSupremum.Main
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# MathOverflow 347178: the bounded-only variant

This file specializes `GradientSupremum.supremum_gradient_step` to the original Euclidean
statement. The redundant second boundedness hypothesis is retained in `bounded_only` so that
the statement matches the conjecture exactly. `bounded_only_strong` omits it and permits all
finite dimensions, including zero and one.

Reference: https://mathoverflow.net/questions/347178
-/

open Set

namespace Mathoverflow347178

/-- For $n ≥ 2$, a bounded-above $C^1$ function and its unit gradient-step composition
have the same real supremum. Both original boundedness hypotheses are retained. -/
theorem bounded_only :
    ∀ (n : ℕ), n ≥ 2 → ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ 1 f → BddAbove (range f) →
      BddAbove (range (fun x ↦ f (x + gradient f x))) →
      (⨆ x, f x) = ⨆ x, f (x + gradient f x) := by
  intro n _hn f hf hb _hb'
  exact (GradientSupremum.supremum_gradient_step hf hb).symm

/-- Stronger form: all dimensions, and only the necessary boundedness assumption. -/
theorem bounded_only_strong (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hb : BddAbove (range f)) :
    (⨆ x, f x) = ⨆ x, f (x + gradient f x) :=
  (GradientSupremum.supremum_gradient_step hf hb).symm

end Mathoverflow347178
