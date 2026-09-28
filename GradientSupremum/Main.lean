/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
import GradientSupremum.Deformation
import GradientSupremum.Homotopy

/-!
# Supremum preservation by a unit gradient step

For an upper-bounded $C^1$ function on a finite-dimensional real inner-product space,
`supremum_gradient_step` proves that $f$ and $x ↦ f(x + ∇f(x))$ have the same supremum.

First `lower_bound_eulerMap` rules out a strict lower gap for a nonnegative function.
The change of variables $g=M-f$ then transfers every upper bound on the gradient-step values
to an upper bound on all values of $f$. This gives equality of the two real suprema.

Reference: https://mathoverflow.net/questions/347178
-/

open Set Metric
open scoped Topology RealInnerProductSpace

noncomputable section

namespace GradientSupremum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Every lower bound on the Euler image of a nonnegative C1 function is a global lower bound. -/
theorem lower_bound_eulerMap {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg0 : ∀ x, 0 ≤ g x) (D : ℝ) (hgap : ∀ x, D ≤ g (eulerMap g x)) :
    ∀ p, D ≤ g p := by
  intro p
  by_contra! hp
  -- One intermediate level and one sufficiently large ball give the contradiction.
  let a : ℝ := (g p + D) / 2
  let R : ℝ := 2 * g p + 1
  have hR : 0 < R := by dsimp [R]; linarith [hg0 p]
  have hRp : 2 * g p < R ^ 2 := by dsimp [R]; nlinarith [sq_nonneg (g p), hg0 p]
  have hpa : g p < a := by dsimp [a]; linarith
  have haD : a < D := by dsimp [a]; linarith
  obtain ⟨H, hc, h0, hgain, hhigh⟩ :=
    exists_raising_homotopy hg hg0 p R a D hR.le hpa haD hgap
  exact no_raising_homotopy g hg0 p a R hR hRp hpa H hc h0 hgain hhigh

/-- Subtracting a function from a constant negates its gradient. -/
lemma gradient_const_sub (f : E → ℝ) (M : ℝ) (x : E) :
    gradient (fun y ↦ M - f y) x = -gradient f x := by
  simp only [gradient, fderiv_const_sub, map_neg]

/-- Upper-bound equivalence under the bounded-above assumption of Variant C. -/
theorem upper_bound_gradient_step {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hbounded : BddAbove (range f)) (a : ℝ)
    (hstep : ∀ x, f (x + gradient f x) ≤ a) : ∀ y, f y ≤ a := by
  -- Replace the upper-bounded function f by the nonnegative function M - f.
  obtain ⟨M, hM⟩ := hbounded
  let g : E → ℝ := fun y ↦ M - f y
  have hgc : ContDiff ℝ 1 g := contDiff_const.sub hf
  have hg0 (y : E) : 0 ≤ g y := sub_nonneg.mpr (hM (mem_range_self y))
  have heuler (x : E) : eulerMap g x = x + gradient f x := by
    simp only [eulerMap, g, gradient_const_sub, sub_neg_eq_add]
  have hgap (x : E) : M - a ≤ g (eulerMap g x) := by
    rw [heuler]
    dsimp [g]
    linarith [hstep x]
  have hh := lower_bound_eulerMap hgc hg0 (M - a) hgap
  intro y
  have hy := hh y
  dsimp [g] at hy
  linarith

/-- Variant C for every finite-dimensional real inner-product space. -/
theorem supremum_gradient_step {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hbounded : BddAbove (range f)) :
    sSup (range (fun x ↦ f (x + gradient f x))) = sSup (range f) := by
  have hs : BddAbove (range (fun x ↦ f (x + gradient f x))) := by
    obtain ⟨M, hM⟩ := hbounded
    refine ⟨M, ?_⟩
    rintro z ⟨x, rfl⟩
    exact hM (mem_range_self _)
  apply le_antisymm
  · apply csSup_le (range_nonempty _)
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    exact le_csSup hbounded (mem_range_self _)
  · have hb : ∀ x, f (x + gradient f x) ≤ sSup (range (fun y ↦ f (y + gradient f y))) :=
      fun x ↦ le_csSup hs (mem_range_self x)
    have hh := upper_bound_gradient_step hf hbounded _ hb
    apply csSup_le (range_nonempty _)
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    exact hh x

end GradientSupremum
