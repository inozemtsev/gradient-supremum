# Local fixed-point foundation

The supremum proof uses `exists_fixedPoint_closedBall` from `ClosedBall.lean`:

```lean
theorem exists_fixedPoint_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : C(Metric.closedBall (0 : E) 1, Metric.closedBall (0 : E) 1)) :
    ∃ x, f x = x
```

Read the files in this order:

| Module | Main step |
| --- | --- |
| `ClosedBall.lean` | Transfer a cube fixed point using an embedding and radial retraction. |
| `Cube.lean` | Construct approximate fixed points, then minimize displacement on the cube. |
| `Sperner.lean` | Find a fully labeled simplex by an odd-count argument. |
| `Triangulation.lean` | Define grid simplices and count their incident faces. |

The two combinatorial modules are adapted from harfe's cubical Sperner
formalization and retain its MIT license. The analytic modules are part of
this repository. Source details are in the root `THIRD_PARTY.md`.

All four modules compile from local source on Lean/Mathlib 4.33.1. They require
no package other than Mathlib and no build-time source transformations.
