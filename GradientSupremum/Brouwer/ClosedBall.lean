/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
module

public import GradientSupremum.Brouwer.Cube
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Brouwer's theorem on a closed ball

Embed the ball in a finite coordinate cube. Decode a point of that cube and
project it radially back to the ball. This is a retraction, so a fixed point
of the induced cube map gives a fixed point of the original ball map.

The construction works for any finite-dimensional real normed space.
-/

@[expose] public section

open Set Metric

namespace GradientSupremum.Brouwer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection onto the closed unit ball, fixing all points already inside. -/
noncomputable def radialProjection (x : E) : E := (max 1 ‖x‖)⁻¹ • x

lemma radialProjection_mem (x : E) : radialProjection x ∈ closedBall 0 1 := by
  have hd : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [mem_closedBall, dist_zero_right, radialProjection, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hd.le), inv_mul_eq_div]
  exact (div_le_one hd).mpr (le_max_right _ _)

lemma continuous_radialProjection : Continuous (radialProjection : E → E) :=
  ((continuous_const.max continuous_norm).inv₀
    (fun x ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)))).smul continuous_id

lemma radialProjection_eq_self (x : E) (hx : x ∈ closedBall 0 1) :
    radialProjection x = x := by
  have hnorm : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
  simp only [radialProjection, max_eq_left hnorm, inv_one, one_smul]

/-- Every continuous self-map of the closed unit ball has a fixed point. -/
theorem exists_fixedPoint_closedBall [FiniteDimensional ℝ E]
    (f : C(closedBall (0 : E) 1, closedBall (0 : E) 1)) : ∃ x, f x = x := by
  let e := (Module.finBasis ℝ E).equivFunL
  let K : ℝ := max 1 ‖e.toContinuousLinearMap‖
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  -- Bound all coordinates of the ball in one finite cube.
  have hcoord (x : closedBall (0 : E) 1) (i : Fin (Module.finrank ℝ E)) :
      |e x i| ≤ K := by
    have hnorm : ‖(x : E)‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using x.property
    calc
      |e x i| = ‖e x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖e x‖ := norm_le_pi_norm (e x) i
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖(x : E)‖ := e.toContinuousLinearMap.le_opNorm x
      _ ≤ ‖e.toContinuousLinearMap‖ * 1 :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ ≤ K := by simpa only [mul_one] using le_max_right 1 ‖e.toContinuousLinearMap‖
  let encode : closedBall (0 : E) 1 → Cube (Module.finrank ℝ E) := fun x ↦
    ⟨fun i ↦ (e x i / K + 1) / 2, by
      have hb (i : Fin (Module.finrank ℝ E)) : -1 ≤ e x i / K ∧ e x i / K ≤ 1 := by
        have hi := abs_le.mp (hcoord x i)
        constructor
        · apply (le_div_iff₀ hK).mpr
          linarith [hi.1]
        · apply (div_le_iff₀ hK).mpr
          linarith [hi.2]
      constructor
      · intro i
        have := (hb i).1
        change 0 ≤ (e x i / K + 1) / 2
        linarith
      · intro i
        have := (hb i).2
        change (e x i / K + 1) / 2 ≤ 1
        linarith⟩
  have hencode : Continuous encode := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact (((continuous_apply i).comp
      (e.continuous.comp continuous_subtype_val)).div_const K |>.add_const 1).div_const 2
  let decode : Cube (Module.finrank ℝ E) → E :=
    fun u ↦ e.symm (fun i ↦ K * (2 * u.val i - 1))
  have hdecode : Continuous decode := by
    apply e.symm.continuous.comp
    apply continuous_pi
    intro i
    exact continuous_const.mul ((continuous_const.mul
      ((continuous_apply i).comp continuous_subtype_val)).sub continuous_const)
  let retract : C(Cube (Module.finrank ℝ E), closedBall (0 : E) 1) :=
    ⟨fun u ↦ ⟨radialProjection (decode u), radialProjection_mem _⟩,
      (continuous_radialProjection.comp hdecode).subtype_mk _⟩
  have hdecode_encode (x : closedBall (0 : E) 1) : decode (encode x) = x := by
    change e.symm (fun i ↦ K * (2 * ((e x i / K + 1) / 2) - 1)) = x
    have heq : (fun i ↦ K * (2 * ((e x i / K + 1) / 2) - 1)) = e x := by
      funext i
      field_simp
      ring
    rw [heq]
    exact e.symm_apply_apply x
  have hsection (x : closedBall (0 : E) 1) : retract (encode x) = x := by
    apply Subtype.ext
    change radialProjection (decode (encode x)) = x
    rw [hdecode_encode]
    exact radialProjection_eq_self (x : E) x.property
  -- Transfer a cube fixed point through the retraction.
  let F : C(Cube (Module.finrank ℝ E), Cube (Module.finrank ℝ E)) :=
    (⟨encode, hencode⟩ : C(closedBall (0 : E) 1, Cube (Module.finrank ℝ E))).comp
      (f.comp retract)
  obtain ⟨u, hu⟩ := exists_fixedPoint_cube F
  refine ⟨retract u, ?_⟩
  have heq := congrArg retract hu
  change retract (encode (f (retract u))) = retract u at heq
  rwa [hsection] at heq

end GradientSupremum.Brouwer
