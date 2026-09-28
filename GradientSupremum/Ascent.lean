/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.UniformSpace.HeineCantor

import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform finite-step ascent

For $S(x)=x-∇g(x)$ and $Q_y(x)=g(x)-‖x-y‖²/2$, the gradient of $Q_y$ is $y-S(x)$.
A hypothetical gap in the values of $g ∘ S$ separates compact sets of low centers from every
Euler image. The resulting ascent direction is continuous in both variables and has norm at
most one. Uniform continuity on a compact ball then gives a common positive step size.

The main results are `exists_uniform_image_separation` and `exists_uniform_ascent_step`.
No global modulus of continuity or bound on the Hessian is needed.
-/

@[expose] public section

open Set Metric
open scoped Topology RealInnerProductSpace

noncomputable section

namespace GradientSupremum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The unit negative-gradient step $x ↦ x - ∇g(x)$. -/
def eulerMap (g : E → ℝ) (x : E) : E := x - gradient g x

/-- The potential $Q_y(x) = g(x) - ‖x-y‖²/2$, with the center fixed during ascent. -/
def shiftedPotential (g : E → ℝ) (y x : E) : ℝ := g x - ‖x - y‖ ^ 2 / 2

/-- The gradient of a $C^1$ function is continuous. -/
lemma continuous_gradient {g : E → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (gradient g) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hg.continuous_fderiv (by norm_num))

/-- The Euler map is continuous under the original $C^1$ hypothesis. -/
lemma continuous_eulerMap {g : E → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (eulerMap g) := continuous_id.sub (continuous_gradient hg)

/-- The derivative of $Q_y$ along a line is the inner product with $y - S(x)$. -/
lemma hasDerivAt_shiftedPotential_line {g : E → ℝ} (hg : ContDiff ℝ 1 g) (y x v : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ shiftedPotential g y (x + u • v))
      ⟪y - eulerMap g (x + t • v), v⟫ t := by
  have hp : HasDerivAt (fun u : ℝ ↦ x + u • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hgf :=
    ((hg.differentiable (by norm_num) (x + t • v)).hasGradientAt.hasFDerivAt).comp_hasDerivAt t hp
  have hq := ((hp.sub_const y).norm_sq).div_const 2
  have hd : ⟪y - eulerMap g (x + t • v), v⟫ =
      ((InnerProductSpace.toDual ℝ E) (gradient g (x + t • v))) v -
        2 * ⟪x + t • v - y, v⟫ / 2 := by
    simp only [eulerMap, InnerProductSpace.toDual_apply_apply, inner_sub_left]
    ring
  rw [hd]
  exact hgf.sub hq

/-- The all-input gap uniformly separates every compact set of low centers from the image. -/
lemma exists_uniform_image_separation {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (p : E) (R a D : ℝ) (hR : 0 ≤ R) (hpa : g p ≤ a) (haD : a < D)
    (hgap : ∀ x, D ≤ g (eulerMap g x)) :
    ∃ c > 0, ∀ y ∈ closedBall p R, g y ≤ a → ∀ x, c ≤ ‖y - eulerMap g x‖ := by
  -- A compact low set and a closed high set have positive separation.
  let K := closedBall p R ∩ {y | g y ≤ a}
  let A := {x | D ≤ g x}
  have hK : IsCompact K :=
    (isCompact_closedBall p R).inter_right (isClosed_le hg.continuous continuous_const)
  have hKn : K.Nonempty := ⟨p, mem_closedBall_self hR, hpa⟩
  have hA : IsClosed A := isClosed_le continuous_const hg.continuous
  have hAn : A.Nonempty := ⟨eulerMap g p, hgap p⟩
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hKn
    (continuous_infDist_pt A).continuousOn
  have hzA : z ∉ A := by
    intro h
    have hza : g z ≤ a := hz.2
    have hDz : D ≤ g z := h
    linarith
  refine ⟨infDist z A, (hA.notMem_iff_infDist_pos hAn).mp hzA, ?_⟩
  intro y hy hya x
  have h := (hmin ⟨hy, hya⟩).trans (infDist_le_dist_of_mem (show eulerMap g x ∈ A from hgap x))
  simpa only [dist_eq_norm] using h

/-- A continuous, bounded direction. The cutoff prevents division by zero at high centers. -/
def ascentDirection (c : ℝ) (g : E → ℝ) (y x : E) : E :=
  (max c ‖y - eulerMap g x‖)⁻¹ • (y - eulerMap g x)

/-- Joint continuity in both the fixed center and the current iterate. -/
lemma continuous_ascentDirection {g : E → ℝ} (hg : ContDiff ℝ 1 g) {c : ℝ} (hc : 0 < c) :
    Continuous (fun z : E × E ↦ ascentDirection c g z.1 z.2) := by
  have hF : Continuous (fun z : E × E ↦ z.1 - eulerMap g z.2) :=
    continuous_fst.sub ((continuous_eulerMap hg).comp continuous_snd)
  exact ((continuous_const.max hF.norm).inv₀
    (fun z ↦ ne_of_gt (lt_of_lt_of_le hc (le_max_left _ _)))).smul hF

/-- Normalization bounds every step direction by one. -/
lemma norm_ascentDirection_le_one {g : E → ℝ} {c : ℝ} (hc : 0 < c) (y x : E) :
    ‖ascentDirection c g y x‖ ≤ 1 := by
  have hp : 0 < max c ‖y - eulerMap g x‖ := lt_of_lt_of_le hc (le_max_left _ _)
  rw [ascentDirection, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have hn := le_max_right c ‖y - eulerMap g x‖
  exact (inv_mul_le_iff₀ hp).mpr (by simpa only [mul_one] using hn)

/-- At separated centers, normalization gives the full gradient norm as ascent rate. -/
lemma inner_ascentDirection {g : E → ℝ} {c : ℝ} (hc : 0 < c) (y x : E)
    (hF : c ≤ ‖y - eulerMap g x‖) :
    ⟪y - eulerMap g x, ascentDirection c g y x⟫ = ‖y - eulerMap g x‖ := by
  have hp : 0 < ‖y - eulerMap g x‖ := hc.trans_le hF
  simp only [ascentDirection, max_eq_right hF, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- Uniform one-step increase on a compact ball; only C1 regularity is used. -/
lemma exists_uniform_ascent_step {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (p : E) (L c : ℝ) (hc : 0 < c) :
    ∃ ε > 0, ∀ y x, x ∈ closedBall p L → ∀ v : E, ‖v‖ ≤ 1 →
      c ≤ ⟪y - eulerMap g x, v⟫ → ∀ h : ℝ, 0 ≤ h → h ≤ ε →
      shiftedPotential g y x + h * c / 2 ≤ shiftedPotential g y (x + h • v) := by
  -- Only this enlarged compact ball needs uniform continuity.
  have hu := (isCompact_closedBall p (L + 1)).uniformContinuousOn_of_continuous
    (continuous_eulerMap hg).continuousOn
  obtain ⟨δ, hδ, huδ⟩ := uniformContinuousOn_iff_le.mp hu (c / 2) (by linarith)
  refine ⟨min 1 δ, lt_min zero_lt_one hδ, ?_⟩
  intro y x hx v hv hbase h hh he
  have hh1 : h ≤ 1 := he.trans (min_le_left _ _)
  have hhδ : h ≤ δ := he.trans (min_le_right _ _)
  have hxb : x ∈ closedBall p (L + 1) :=
    (closedBall_subset_closedBall (by linarith : L ≤ L + 1)) hx
  have hder (t : ℝ) := hasDerivAt_shiftedPotential_line hg y x v t
  have hbound (t : ℝ) (ht : t ∈ Icc 0 h) : c / 2 ≤ ⟪y - eulerMap g (x + t • v), v⟫ := by
    have htx : dist (x + t • v) x ≤ t := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_right ht.1 hv
    have htb : x + t • v ∈ closedBall p (L + 1) := by
      have hd := dist_triangle (x + t • v) x p
      have hxp : dist x p ≤ L := hx
      change dist (x + t • v) p ≤ L + 1
      linarith [ht.2]
    have hdist := huδ x hxb (x + t • v) htb (by rw [dist_comm]; exact htx.trans (ht.2.trans hhδ))
    have hdiff : ‖(y - eulerMap g (x + t • v)) - (y - eulerMap g x)‖ ≤ c / 2 := by
      have heq : (y - eulerMap g (x + t • v)) - (y - eulerMap g x) =
          eulerMap g x - eulerMap g (x + t • v) := by abel
      rw [heq, ← dist_eq_norm]
      exact hdist
    have habs := abs_real_inner_le_norm ((y - eulerMap g (x + t • v)) - (y - eulerMap g x)) v
    have hmul : ‖(y - eulerMap g (x + t • v)) - (y - eulerMap g x)‖ * ‖v‖ ≤ c / 2 :=
      (mul_le_of_le_one_right (norm_nonneg _) hv).trans hdiff
    have hh' := (abs_le.mp (habs.trans hmul)).1
    rw [inner_sub_left] at hh'
    linarith
  -- Integrate the lower derivative bound along the short segment.
  have hm := (convex_Icc (0 : ℝ) h).mul_sub_le_image_sub_of_le_deriv
    (fun t _ ↦ (hder t).continuousAt.continuousWithinAt)
    (fun t _ ↦ (hder t).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ by rw [(hder t).deriv]; exact hbound t (interior_subset ht))
    0 ⟨le_rfl, hh⟩ h ⟨hh, le_rfl⟩ hh
  simp only [sub_zero, zero_smul, add_zero] at hm
  linarith

end GradientSupremum
