# Supremum preservation under a gradient step

A Lean proof of the bounded-only variant of
[MathOverflow 347178](https://mathoverflow.net/questions/347178).
For a bounded-above C¹ function on a finite-dimensional real inner-product space,

```lean
theorem GradientSupremum.supremum_gradient_step
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hbounded : BddAbove (Set.range f)) :
    sSup (Set.range (fun x ↦ f (x + gradient f x))) = sSup (Set.range f)
```

## Reading the proof

Read the [mathematical proof](docs/proof.md), or start with
[`GradientSupremum/Main.lean`](GradientSupremum/Main.lean).
The [local Brouwer proof](docs/brouwer.md) explains the fixed-point foundation.
The modules are organized as follows:

| File | Purpose |
| --- | --- |
| [`Ascent.lean`](GradientSupremum/Ascent.lean) | Compact separation and a uniform C¹ small-step estimate. |
| [`Iteration.lean`](GradientSupremum/Iteration.lean) | Continuous finite Euler walks and their displacement bound. |
| [`Deformation.lean`](GradientSupremum/Deformation.lean) | A homotopy that raises low values with quadratic value gain. |
| [`Homotopy.lean`](GradientSupremum/Homotopy.lean) | Brouwer's obstruction to such a homotopy on a ball. |
| [`Main.lean`](GradientSupremum/Main.lean) | Exclusion of a positive gap and equality of real suprema. |
| [`Mathoverflow347178.lean`](GradientSupremum/Mathoverflow347178.lean) | The exact Euclidean statement, including both original bounds. |

The main argument uses finitely many short ascent steps for
`g(x) - ‖x - y‖² / 2`, keeping y fixed during each walk. A hypothetical gap gives a
uniform separation constant for the low centers in a chosen compact ball. The walk
raises them to a higher level and gains at least half the squared displacement.
That estimate keeps a low target off the boundary throughout the homotopy.
Brouwer then forces a final preimage of the target, which contradicts the higher level.

## Build and audit

The project uses Lean 4.33.1 and Mathlib v4.33.1. Mathlib is its only direct
dependency; all dependencies are locked in `lake-manifest.json`.
The full fixed-point foundation is included in
[`GradientSupremum/Brouwer/`](GradientSupremum/Brouwer/README.md).
From this directory, with elan installed:

```bash
lake exe cache get
lake --wfail build
lake env lean -j2 scripts/AxiomAudit.lean
lake env lean -j2 scripts/StatementTests.lean
python3 scripts/verify.py
```

The expected transitive axiom list is `propext`, `Classical.choice`, `Quot.sound`.
Audit commands are kept outside the proof modules. There are no proof placeholders
or custom axioms in this project. See `VALIDATION.json` for the recorded checks.

## Attribution

Proof and formalization: gpt-6 astra.
The local cubical Sperner foundation is adapted from harfe; see `THIRD_PARTY.md`.
