/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
import GradientSupremum.Ascent
import GradientSupremum.Iteration

import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Raising low values by finitely many continuous steps

Under a hypothetical output gap, construct a homotopy on any prescribed closed ball.
At every time its value gain dominates half the squared displacement. At the final time it
sends the whole ball into a higher superlevel set. The construction uses a fixed number of
Euler steps, not an ODE flow, so continuity of the gradient is enough.

The proof of `exists_raising_homotopy` first chooses a uniform separation constant, then a
compact-ball step size, and finally iterates with a center-dependent step length.
-/

open Set Metric
open scoped Topology RealInnerProductSpace

noncomputable section

namespace GradientSupremum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An output gap gives a homotopy with quadratic value gain on a prescribed ball. -/
theorem exists_raising_homotopy {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hg0 : ∀ x, 0 ≤ g x) (p : E) (R a D : ℝ) (hR : 0 ≤ R)
    (hpa : g p < a) (haD : a < D) (hgap : ∀ x, D ≤ g (eulerMap g x)) :
    ∃ H : ℝ × E → E, Continuous H ∧ (∀ x, H (0, x) = x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall p R,
        g x + ‖H (t, x) - x‖ ^ 2 / 2 ≤ g (H (t, x))) ∧
      (∀ x ∈ closedBall p R, a ≤ g (H (1, x))) := by
  -- First fix a separation constant for every low center in the chosen ball.
  obtain ⟨c, hc, hsep⟩ := exists_uniform_image_separation hg p R a D hR hpa.le haD hgap
  have ha0 : 0 < a := (hg0 p).trans_lt hpa
  let T : ℝ := 2 * a / c
  have hT : T * c / 2 = a := by dsimp [T]; field_simp
  -- All walks have total length at most T, so one compact-ball step size suffices.
  obtain ⟨ε, hε, hstep⟩ := exists_uniform_ascent_step hg p (R + T) c hc
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (T / ε))
  have hNpos : (0 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNT : T < (N : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hN)
  -- The step size vanishes continuously at g(y) = a and fixes higher centers.
  let h : E → ℝ := fun y ↦ 2 * max 0 (a - g y) / ((N : ℝ) * c)
  have hhc : Continuous h := by fun_prop
  have hh0 (y : E) : 0 ≤ h y :=
    div_nonneg (mul_nonneg (by norm_num) (le_max_left _ _)) (mul_pos hNpos hc).le
  have hid (y : E) : (N : ℝ) * h y * c / 2 = max 0 (a - g y) := by
    dsimp [h]
    field_simp [ne_of_gt hNpos, ne_of_gt hc]
  have hNH (y : E) : (N : ℝ) * h y ≤ T := by
    have hm : max 0 (a - g y) ≤ a := max_le ha0.le (sub_le_self a (hg0 y))
    apply (mul_le_mul_iff_of_pos_right hc).mp
    nlinarith [hid y]
  have hhε (y : E) : h y ≤ ε :=
    (mul_le_mul_iff_of_pos_left hNpos).mp ((hNH y).trans hNT.le)
  have hhighzero (y : E) (hy : a ≤ g y) : h y = 0 := by
    simp [h, max_eq_left (sub_nonpos.mpr hy)]
  let V : E × E → E := fun z ↦ ascentDirection c g z.1 z.2
  have hVc : Continuous V := continuous_ascentDirection hg hc
  have hVn (z : E × E) : ‖V z‖ ≤ 1 := norm_ascentDirection_le_one hc z.1 z.2
  have hpos (s : ℝ) (hs : s ∈ Icc 0 1) (y : E) : 0 ≤ s * h y := mul_nonneg hs.1 (hh0 y)
  have hle (s : ℝ) (hs : s ∈ Icc 0 1) (y : E) : s * h y ≤ h y :=
    mul_le_of_le_one_left (hh0 y) hs.2
  have hball (s : ℝ) (hs : s ∈ Icc 0 1) (y : E)
      (hy : y ∈ closedBall p R) (n : ℕ) (hn : n ≤ N) :
      eulerWalk V h n (s, y) ∈ closedBall p (R + T) :=
    eulerWalk_mem_closedBall V h hVn N T hh0 hNH p R s hs y hy n hn
  -- Accumulate the shifted-potential gain while keeping the original center fixed.
  have hgain_low (s : ℝ) (hs : s ∈ Icc 0 1) (y : E)
      (hy : y ∈ closedBall p R) (hylow : g y < a) :
      ∀ n : ℕ, n ≤ N →
        g y + (n : ℝ) * (s * h y) * c / 2 ≤
          shiftedPotential g y (eulerWalk V h n (s, y)) := by
    intro n
    induction n with
    | zero => intro _; simp [eulerWalk, shiftedPotential]
    | succ n ih =>
      intro hn
      have hnN : n ≤ N := (Nat.le_succ n).trans hn
      have hprev := ih hnN
      have hbase :
          c ≤ ⟪y - eulerMap g (eulerWalk V h n (s, y)), V (y, eulerWalk V h n (s, y))⟫ := by
        have hf := hsep y hy hylow.le (eulerWalk V h n (s, y))
        change c ≤ ⟪y - eulerMap g (eulerWalk V h n (s, y)),
          ascentDirection c g y (eulerWalk V h n (s, y))⟫
        rw [inner_ascentDirection hc y (eulerWalk V h n (s, y)) hf]
        exact hf
      have hinc := hstep y (eulerWalk V h n (s, y)) (hball s hs y hy n hnN)
        (V (y, eulerWalk V h n (s, y))) (hVn _) hbase (s * h y) (hpos s hs y)
        ((hle s hs y).trans (hhε y))
      change g y + ((n + 1 : ℕ) : ℝ) * (s * h y) * c / 2 ≤
        shiftedPotential g y (eulerWalk V h n (s, y) + (s * h y) • V (y, eulerWalk V h n (s, y)))
      push_cast
      nlinarith
  -- At time zero the walk is the identity; at time one every center is high.
  refine ⟨eulerWalk V h N, continuous_eulerWalk hVc hhc N, eulerWalk_zero_time V h N, ?_, ?_⟩
  · intro s hs y hy
    by_cases hylow : g y < a
    · have hlow := hgain_low s hs y hy hylow N le_rfl
      have hp := hpos s hs y
      have hnon : 0 ≤ (N : ℝ) * (s * h y) * c / 2 := by positivity
      simp only [shiftedPotential] at hlow
      linarith
    · rw [eulerWalk_of_step_eq_zero V h y (hhighzero y (le_of_not_gt hylow)) N s]
      simp
  · intro y hy
    by_cases hylow : g y < a
    · have hlow := hgain_low 1 ⟨zero_le_one, le_rfl⟩ y hy hylow N le_rfl
      simp only [one_mul] at hlow
      rw [hid, max_eq_right (sub_nonneg.mpr hylow.le)] at hlow
      simp only [shiftedPotential] at hlow
      nlinarith [sq_nonneg ‖eulerWalk V h N (1, y) - y‖]
    · rw [eulerWalk_of_step_eq_zero V h y (hhighzero y (le_of_not_gt hylow)) N 1]
      exact le_of_not_gt hylow

end GradientSupremum
