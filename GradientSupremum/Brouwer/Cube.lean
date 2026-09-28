/-
Copyright (c) 2026 Igor Inozemtsev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Inozemtsev
-/
module

public import GradientSupremum.Brouwer.Sperner
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A fixed point on the unit cube

The cubical Sperner lemma provides nearby vertices with opposite coordinate
inequalities. Uniform continuity makes the displacement small at one of them.
Its norm attains a minimum on the cube, and this minimum must be zero.

Only the finite combinatorial argument is imported from `Sperner.lean`.
-/

@[expose] public section

open Set Metric

namespace GradientSupremum.Brouwer

/-- The closed unit cube, with the subspace topology of the finite product. -/
abbrev Cube (n : ℕ) := ↥(Icc (0 : Fin n → ℝ) 1)

instance (n : ℕ) : CompactSpace (Cube n) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

instance (n : ℕ) : Nonempty (Cube n) :=
  ⟨⟨0, le_rfl, fun _ ↦ zero_le_one⟩⟩

variable {n : ℕ}

/-- Coordinate `i` can label `x` when it does not move upwards, or is on the top face. -/
def LabelCandidate (f : Cube n → Cube n) (x : Cube n) (k : ℕ) : Prop :=
  k = n ∨ ∃ i : Fin n, i.val = k ∧ ((f x).val i < x.val i ∨ x.val i = 1)

open scoped Classical in
/-- Choose the first eligible coordinate, using `n` when none exists. -/
noncomputable def label (f : Cube n → Cube n) (x : Cube n) : ℕ :=
  Nat.find (⟨n, Or.inl rfl⟩ : ∃ k, LabelCandidate f x k)

private lemma label_le_dimension (f : Cube n → Cube n) (x : Cube n) : label f x ≤ n := by
  classical
  exact Nat.find_min' _ (Or.inl rfl)

private lemma label_le_coordinate (f : Cube n → Cube n) (x : Cube n) (i : Fin n)
    (hi : (f x).val i < x.val i ∨ x.val i = 1) : label f x ≤ i.val := by
  classical
  exact Nat.find_min' _ (Or.inr ⟨i, rfl, hi⟩)

private lemma label_coordinate (f : Cube n → Cube n) (x : Cube n) (i : Fin n)
    (hi : label f x = i.val) : (f x).val i < x.val i ∨ x.val i = 1 := by
  classical
  have h : LabelCandidate f x (label f x) := Nat.find_spec _
  rcases h with h | ⟨j, hj, hdown⟩
  · exact (i.is_lt.ne (hi.symm.trans h)).elim
  · have hji : j = i := Fin.ext (hj.trans hi)
    simpa only [hji] using hdown

private lemma label_down (f : Cube n → Cube n) (x : Cube n) (i : Fin n)
    (hi : label f x = i.val) : (f x).val i ≤ x.val i := by
  rcases label_coordinate f x i hi with h | h
  · exact h.le
  · rw [h]
    exact (f x).property.2 i

private lemma label_top_up (f : Cube n → Cube n) (x : Cube n)
    (hx : label f x = n) (i : Fin n) : x.val i ≤ (f x).val i := by
  by_contra! h
  have := label_le_coordinate f x i (Or.inl h)
  rw [hx] at this
  exact (not_le.mpr i.is_lt) this

/-- Embed a grid with mesh `1 / m` in the unit cube. -/
noncomputable def gridPoint (m : ℕ) (hm : 0 < m) (v : Fin n → Fin (m + 1)) : Cube n :=
  ⟨fun i ↦ (v i).val / (m : ℝ), by
    constructor
    · intro i
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro i
      apply (div_le_one (Nat.cast_pos.mpr hm)).mpr
      exact Nat.cast_le.mpr (Nat.le_of_lt_succ (v i).is_lt)⟩

/-- The displacement labeling satisfies both boundary conditions of cubical Sperner. -/
noncomputable def labeledGrid (f : Cube n → Cube n) (m : ℕ) (hm : 0 < m) :
    Cubical.SpernerCube where
  n := n
  p := m
  RL := fun v ↦ label f (gridPoint m hm v)
  rl_proper := by
    intro v
    refine ⟨label_le_dimension f _, fun i ↦ ⟨?_, ?_⟩⟩
    · intro hzero heq
      have hz : (gridPoint m hm v).val i = 0 := by simp [gridPoint, hzero]
      rcases label_coordinate f _ i heq with h | h
      · have hnonneg : (0 : ℝ) ≤ (f (gridPoint m hm v)).val i :=
          (f (gridPoint m hm v)).property.1 i
        linarith
      · rw [hz] at h
        exact zero_ne_one h
    · intro htop
      apply label_le_coordinate f _ i
      right
      simp [gridPoint, htop, Nat.ne_of_gt hm]

/-- Two vertices of a grid simplex are at most one mesh width apart. -/
lemma gridPoint_dist_le (m : ℕ) (hm : 0 < m) (u v : Fin n → Fin (m + 1))
    (hnear : ∀ i, (u i).val ≤ (v i).val + 1 ∧ (v i).val ≤ (u i).val + 1) :
    dist (gridPoint m hm u) (gridPoint m hm v) ≤ 1 / (m : ℝ) := by
  change dist (fun i ↦ (u i).val / (m : ℝ)) (fun i ↦ (v i).val / (m : ℝ)) ≤ _
  apply (dist_pi_le_iff (by positivity : 0 ≤ 1 / (m : ℝ))).mpr
  intro i
  have hleft : ((u i).val : ℝ) ≤ (v i).val + 1 := by exact_mod_cast (hnear i).1
  have hright : ((v i).val : ℝ) ≤ (u i).val + 1 := by exact_mod_cast (hnear i).2
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hmreal]
  exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩)
    (Nat.cast_nonneg m)

/-- A fully labeled simplex supplies every downward witness near an upward vertex. -/
lemma exists_signWitnesses (f : Cube n → Cube n) (m : ℕ) (hm : 0 < m) :
    ∃ x : Cube n, (∀ i, x.val i ≤ (f x).val i) ∧
      ∀ i, ∃ y : Cube n, dist x y ≤ 1 / (m : ℝ) ∧ (f y).val i ≤ y.val i := by
  let G := labeledGrid f m hm
  obtain ⟨v, hv⟩ := Cubical.weaker_cubical_sperner G
  have hlabel (k : ℕ) (hk : k ≤ n) : ∃ j, G.RL (v j) = k := by
    have hmem : k ∈ range (fun j ↦ G.RL (v j)) := by
      rw [hv.2]
      exact hk
    exact hmem
  obtain ⟨jtop, hjtop⟩ := hlabel n le_rfl
  let x := gridPoint m hm (v jtop)
  refine ⟨x, label_top_up f x hjtop, ?_⟩
  intro i
  obtain ⟨j, hj⟩ := hlabel i.val i.is_lt.le
  refine ⟨gridPoint m hm (v j), ?_, label_down f _ i hj⟩
  apply gridPoint_dist_le
  intro k
  exact ⟨Cubical.le_add_one_of_simplex G v hv.1 jtop j k,
    Cubical.le_add_one_of_simplex G v hv.1 j jtop k⟩

/-- Every continuous cube map has arbitrarily small displacement. -/
theorem exists_approximate_fixedPoint (f : C(Cube n, Cube n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Cube n, ‖(f x).val - x.val‖ ≤ ε := by
  have hc : Continuous (fun x : Cube n ↦ (f x).val - x.val) :=
    (continuous_subtype_val.comp f.continuous).sub continuous_subtype_val
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / δ)
  have hmpos : (0 : ℝ) < m := (one_div_pos.mpr hδ).trans hm
  have hmnat : 0 < m := Nat.cast_pos.mp hmpos
  have hmesh : 1 / (m : ℝ) < δ := by
    apply (div_lt_iff₀ hmpos).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hm
  obtain ⟨x, hx, hw⟩ := exists_signWitnesses f m hmnat
  refine ⟨x, (pi_norm_le_iff_of_nonneg hε.le).mpr ?_⟩
  intro i
  have hnonneg : 0 ≤ (f x).val i - x.val i := sub_nonneg.mpr (hx i)
  change ‖(f x).val i - x.val i‖ ≤ ε
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  obtain ⟨y, hxy, hy⟩ := hw i
  have hdist := huc (hxy.trans_lt hmesh)
  have hcoord := (norm_le_pi_norm ((f x).val - x.val - ((f y).val - y.val)) i)
  rw [dist_eq_norm] at hdist
  have habs : |(f x).val i - x.val i - ((f y).val i - y.val i)| < ε := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoord.trans_lt hdist
  have := (le_abs_self _).trans_lt habs
  linarith

/-- Brouwer's fixed-point theorem on the closed unit cube, including dimension zero. -/
theorem exists_fixedPoint_cube (f : C(Cube n, Cube n)) : ∃ x, f x = x := by
  have hc : Continuous (fun x : Cube n ↦ ‖(f x).val - x.val‖) :=
    ((continuous_subtype_val.comp f.continuous).sub continuous_subtype_val).norm
  obtain ⟨x, _, hmin⟩ :=
    isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set (Cube n)).Nonempty) hc.continuousOn
  have hz : ‖(f x).val - x.val‖ = 0 := by
    by_contra hne
    have hp : 0 < ‖(f x).val - x.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨y, hy⟩ := exists_approximate_fixedPoint f _ (half_pos hp)
    have hxy : ‖(f x).val - x.val‖ ≤ ‖(f y).val - y.val‖ := hmin (mem_univ y)
    linarith
  exact ⟨x, Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp hz))⟩

end GradientSupremum.Brouwer
