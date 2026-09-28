import GradientSupremum

open Set

-- The smallest excluded dimensions satisfy the stronger theorem as well.
example (f : EuclideanSpace ℝ (Fin 0) → ℝ)
    (hf : ContDiff ℝ 1 f) (hb : BddAbove (range f)) :
    (⨆ x, f x) = ⨆ x, f (x + gradient f x) :=
  Mathoverflow347178.bounded_only_strong 0 f hf hb

example (f : EuclideanSpace ℝ (Fin 1) → ℝ)
    (hf : ContDiff ℝ 1 f) (hb : BddAbove (range f)) :
    (⨆ x, f x) = ⨆ x, f (x + gradient f x) :=
  Mathoverflow347178.bounded_only_strong 1 f hf hb

-- Retain every hypothesis of the original n >= 2 formulation.
example (n : ℕ) (hn : n ≥ 2) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hb : BddAbove (range f))
    (hb' : BddAbove (range (fun x ↦ f (x + gradient f x)))) :
    (⨆ x, f x) = ⨆ x, f (x + gradient f x) :=
  Mathoverflow347178.bounded_only n hn f hf hb hb'

-- A concrete family witnesses consistency of the regularity and boundedness hypotheses.
example (n : ℕ) :
    let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ -‖x‖ ^ 2
    sSup (range (fun x ↦ f (x + gradient f x))) = sSup (range f) := by
  apply GradientSupremum.supremum_gradient_step (contDiff_norm_sq ℝ |>.neg)
  refine ⟨0, ?_⟩
  rintro z ⟨x, rfl⟩
  exact neg_nonpos.mpr (sq_nonneg ‖x‖)
