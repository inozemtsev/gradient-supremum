/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
import FixedPointTheorems.brouwer

/-!
# A topological obstruction to raising all low values

Brouwer implies that a homotopy from the identity cannot lose a target without crossing the
boundary of a ball. A quadratic value-gain estimate excludes that crossing. The result
`no_raising_homotopy` is the topological step used in the proof of the supremum equality.

The imported Brouwer theorem is proved in harfe's MIT-licensed cubical Sperner development.
See `THIRD_PARTY.md` for the upstream dependency and its license.
-/

open Set Metric
open scoped Topology

noncomputable section

namespace GradientSupremum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- No continuous retraction of a closed unit ball onto its sphere. -/
theorem no_unit_sphere_retraction
    (r : closedBall (0 : E) 1 → E) (hc : Continuous r)
    (hn : ∀ x, ‖r x‖ = 1)
    (hfix : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → r x = x) : False := by
  have hm (x : closedBall (0 : E) 1) : -r x ∈ closedBall (0 : E) 1 := by
    change dist (-r x) 0 ≤ 1
    rw [dist_zero_right, norm_neg, hn x]
  -- Brouwer applied to the antipode of a putative retraction gives a contradiction.
  let F : C(closedBall (0 : E) 1, closedBall (0 : E) 1) :=
    ⟨fun x ↦ ⟨-r x, hm x⟩, hc.neg.subtype_mk hm⟩
  obtain ⟨x, hx⟩ := brouwer_fixed_point (closedBall (0 : E) 1)
    (convex_closedBall 0 1) (isCompact_closedBall 0 1)
    ⟨0, mem_closedBall_self zero_le_one⟩ F
  have heq : -r x = (x : E) := congrArg Subtype.val hx
  have hxnorm : ‖(x : E)‖ = 1 := by rw [← heq, norm_neg, hn]
  have hneg : -(x : E) = (x : E) := by simpa [hfix x hxnorm] using heq
  have htwo : (2 : ℝ) • (x : E) = 0 := by
    simpa [two_smul] using (neg_eq_iff_add_eq_zero.mp hneg)
  have hxzero : (x : E) = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  simp [hxzero] at hxnorm

/-- Homotopy invariance of target existence on a ball, derived from Brouwer. -/
theorem exists_zero_of_homotopy_on_unitBall (H : ℝ × E → E) (hc : Continuous H)
    (h0 : ∀ x, H (0, x) = x)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ = 1 → H (t, x) ≠ 0) :
    ∃ x ∈ closedBall (0 : E) 1, H (1, x) = 0 := by
  by_contra! he
  -- Glue the final map on the inner half-ball to the homotopy on the outer annulus.
  let B := closedBall (0 : E) 1
  let d : B → ℝ := fun x ↦ max 1 (2 * ‖(x : E)‖)
  have hd1 (x : B) : 1 ≤ d x := le_max_left _ _
  have hdpos (x : B) : 0 < d x := lt_of_lt_of_le zero_lt_one (hd1 x)
  have hdn (x : B) : 2 * ‖(x : E)‖ ≤ d x := le_max_right _ _
  have hdx (x : B) : ‖(x : E)‖ ≤ 1 := by
    have hx : dist (x : E) 0 ≤ 1 := x.property
    rwa [dist_zero_right] at hx
  have hd2 (x : B) : d x ≤ 2 := max_le (by norm_num) (by nlinarith [hdx x])
  let v : B → E := fun x ↦ (2 / d x) • (x : E)
  have hvnorm (x : B) : ‖v x‖ = (2 * ‖(x : E)‖) / d x := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_two (hdpos x))]
    ring
  have hvball (x : B) : v x ∈ closedBall (0 : E) 1 := by
    simp only [mem_closedBall, dist_zero_right, hvnorm]
    exact (div_le_one (hdpos x)).mpr (hdn x)
  have ht (x : B) : 2 - d x ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hd1 x, hd2 x]
  let z : B → E := fun x ↦ H (2 - d x, v x)
  have hz (x : B) : z x ≠ 0 := by
    by_cases h : 2 * ‖(x : E)‖ ≤ 1
    · have hd : d x = 1 := max_eq_left h
      change H (2 - d x, v x) ≠ 0
      rw [hd, show (2 : ℝ) - 1 = 1 by norm_num]
      exact he (v x) (hvball x)
    · have hd : d x = 2 * ‖(x : E)‖ := max_eq_right (le_of_not_ge h)
      have hv : ‖v x‖ = 1 := by
        rw [hvnorm, ← hd]
        exact div_self (ne_of_gt (hdpos x))
      exact hb (2 - d x) (ht x) (v x) hv
  have hdc : Continuous d := continuous_const.max (continuous_const.mul continuous_subtype_val.norm)
  have hvc : Continuous v :=
    (continuous_const.div hdc (fun x ↦ ne_of_gt (hdpos x))).smul continuous_subtype_val
  have hzc : Continuous z := hc.comp ((continuous_const.sub hdc).prodMk hvc)
  -- Normalization would now give a retraction onto the unit sphere.
  let r : B → E := fun x ↦ (‖z x‖)⁻¹ • z x
  have hrc : Continuous r := (hzc.norm.inv₀ (fun x ↦ norm_ne_zero_iff.mpr (hz x))).smul hzc
  have hrn (x : B) : ‖r x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hz x))
  have hrf (x : B) (hx : ‖(x : E)‖ = 1) : r x = x := by
    have hd : d x = 2 := by simp [d, hx]
    have hv : v x = (x : E) := by simp [v, hd]
    have hz0 : z x = (x : E) := by simp [z, hd, hv, h0]
    simp [r, hz0, hx]
  exact no_unit_sphere_retraction r hrc hrn hrf

/-- Rescale the unit-ball result to a ball with arbitrary center and positive radius. -/
theorem exists_preimage_of_homotopy_on_ball (H : ℝ × E → E) (hc : Continuous H)
    (h0 : ∀ x, H (0, x) = x) (p : E) (R : ℝ) (hR : 0 < R)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, dist x p = R → H (t, x) ≠ p) :
    ∃ x ∈ closedBall p R, H (1, x) = p := by
  let G : ℝ × E → E := fun z ↦ R⁻¹ • (H (z.1, p + R • z.2) - p)
  have hGc : Continuous G := by fun_prop
  have hG0 (x : E) : G (0, x) = x := by
    simp [G, h0, smul_smul, inv_mul_cancel₀ (ne_of_gt hR)]
  have hGb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖x‖ = 1 → G (t, x) ≠ 0 := by
    intro t ht x hx hz
    have hdist : dist (p + R • x) p = R := by
      simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hx]
    have hh : H (t, p + R • x) - p = 0 :=
      (smul_eq_zero.mp hz).resolve_left (inv_ne_zero (ne_of_gt hR))
    exact hb t ht (p + R • x) hdist (sub_eq_zero.mp hh)
  obtain ⟨x, hx, he⟩ := exists_zero_of_homotopy_on_unitBall G hGc hG0 hGb
  refine ⟨p + R • x, ?_, ?_⟩
  · have hn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith
  · exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_left (inv_ne_zero (ne_of_gt hR)))

/-- A continuous homotopy with quadratic value gain cannot omit a lower target. -/
theorem no_raising_homotopy (g : E → ℝ) (hg : ∀ x, 0 ≤ g x)
    (p : E) (a R : ℝ) (hR : 0 < R) (hRp : 2 * g p < R ^ 2)
    (ha : g p < a) (H : ℝ × E → E) (hc : Continuous H)
    (h0 : ∀ x, H (0, x) = x)
    (hgain : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall p R,
      g x + ‖H (t, x) - x‖ ^ 2 / 2 ≤ g (H (t, x)))
    (hhigh : ∀ x ∈ closedBall p R, a ≤ g (H (1, x))) : False := by
  -- The quadratic gain keeps every preimage of p off the boundary.
  have hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, dist x p = R → H (t, x) ≠ p := by
    intro t ht x hx he
    have hxb : x ∈ closedBall p R := mem_closedBall.mpr hx.le
    have h := hgain t ht x hxb
    have hn : ‖p - x‖ = R := by rw [norm_sub_rev, ← dist_eq_norm, hx]
    rw [he, hn] at h
    nlinarith [hg x]
  obtain ⟨x, hx, he⟩ := exists_preimage_of_homotopy_on_ball H hc h0 p R hR hb
  have hh := hhigh x hx
  rw [he] at hh
  exact (not_le.mpr ha) hh

end GradientSupremum
