# Sources and licenses

The local combinatorial modules
`GradientSupremum/Brouwer/Triangulation.lean` and
`GradientSupremum/Brouwer/Sperner.lean` are adapted from harfe's
[fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838).
They formalize Kuhn's cubical Sperner argument. The original MIT license is
retained in `GradientSupremum/Brouwer/LICENSE-MIT`.

`Cube.lean` gives a local analytic proof using uniformly small displacement
and a minimum on the compact cube. `ClosedBall.lean` transfers the result
through a coordinate embedding and radial retraction. These files and the
supremum argument use the repository's Apache 2.0 license.

Mathlib is the sole direct Lake dependency. Its revision and transitive
dependencies are pinned in `lake-manifest.json`. All local proof sources
are compiled directly; the build does not modify dependency sources.
