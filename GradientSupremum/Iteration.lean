/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Finite Euler walks

`eulerWalk V h n (s, y)` takes $n$ steps of length $s h(y)$ in the field $V(y, ·)$.
The center $y$ is retained throughout the iteration; it is not updated to the current point.
These elementary continuity and displacement lemmas need no finite-dimensional assumption.
-/

@[expose] public section

open Set Metric
open scoped Topology

noncomputable section

namespace GradientSupremum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite normalized Euler construction, with the center retained as a parameter. -/
def eulerWalk (V : E × E → E) (h : E → ℝ) : ℕ → ℝ × E → E
  | 0 => fun z ↦ z.2
  | n + 1 => fun z ↦ eulerWalk V h n z + (z.1 * h z.2) • V (z.2, eulerWalk V h n z)

/-- Each finite walk depends continuously on its center and time parameter. -/
lemma continuous_eulerWalk {V : E × E → E} {h : E → ℝ}
    (hV : Continuous V) (hh : Continuous h) (n : ℕ) : Continuous (eulerWalk V h n) := by
  induction n with
  | zero => exact continuous_snd
  | succ n ih =>
    exact ih.add ((continuous_fst.mul (hh.comp continuous_snd)).smul
      (hV.comp (continuous_snd.prodMk ih)))

/-- At time zero, every finite walk is the identity. -/
lemma eulerWalk_zero_time (V : E × E → E) (h : E → ℝ) (n : ℕ) (y : E) :
    eulerWalk V h n (0, y) = y := by
  induction n with
  | zero => rfl
  | succ n ih => simp [eulerWalk, ih]

/-- A center with zero step size stays fixed. -/
lemma eulerWalk_of_step_eq_zero (V : E × E → E) (h : E → ℝ) (y : E) (hh : h y = 0)
    (n : ℕ) (t : ℝ) : eulerWalk V h n (t, y) = y := by
  induction n with
  | zero => rfl
  | succ n ih => simp [eulerWalk, ih, hh]

/-- Unit-bounded directions give the total-length bound after $n$ steps. -/
lemma norm_eulerWalk_sub_le (V : E × E → E) (h : E → ℝ)
    (hV : ∀ z, ‖V z‖ ≤ 1) (n : ℕ) (t : ℝ) (y : E) (hs : 0 ≤ t * h y) :
    ‖eulerWalk V h n (t, y) - y‖ ≤ (n : ℝ) * (t * h y) := by
  induction n with
  | zero => simp [eulerWalk]
  | succ n ih =>
    have hn : ‖(t * h y) • V (y, eulerWalk V h n (t, y))‖ ≤ t * h y := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
      exact mul_le_of_le_one_right hs (hV _)
    have heq : eulerWalk V h (n + 1) (t, y) - y =
        (eulerWalk V h n (t, y) - y) + (t * h y) • V (y, eulerWalk V h n (t, y)) := by
      simp only [eulerWalk]
      abel
    rw [heq]
    calc
      _ ≤ ‖eulerWalk V h n (t, y) - y‖ + ‖(t * h y) • V (y, eulerWalk V h n (t, y))‖ :=
        norm_add_le _ _
      _ ≤ (n : ℝ) * (t * h y) + t * h y := add_le_add ih hn
      _ = ((n + 1 : ℕ) : ℝ) * (t * h y) := by push_cast; ring

/-- A bound on the total length keeps all intermediate iterates in an enlarged ball. -/
lemma eulerWalk_mem_closedBall (V : E × E → E) (h : E → ℝ)
    (hVn : ∀ z, ‖V z‖ ≤ 1) (N : ℕ) (T : ℝ)
    (hh0 : ∀ y, 0 ≤ h y) (htotal : ∀ y, (N : ℝ) * h y ≤ T)
    (p : E) (R s : ℝ) (hs : s ∈ Icc 0 1) (y : E)
    (hy : y ∈ closedBall p R) (n : ℕ) (hn : n ≤ N) :
    eulerWalk V h n (s, y) ∈ closedBall p (R + T) := by
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hns : (n : ℝ) * (s * h y) ≤ (N : ℝ) * h y :=
    mul_le_mul hnR (mul_le_of_le_one_left (hh0 y) hs.2)
      (mul_nonneg hs.1 (hh0 y)) (Nat.cast_nonneg N)
  have hw := norm_eulerWalk_sub_le V h hVn n s y (mul_nonneg hs.1 (hh0 y))
  have hd := dist_triangle (eulerWalk V h n (s, y)) y p
  have hyp : dist y p ≤ R := hy
  simp only [dist_eq_norm] at hd hyp
  simp only [mem_closedBall, dist_eq_norm]
  nlinarith [htotal y]

end GradientSupremum
