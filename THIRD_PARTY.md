# Third-party proof dependency

The five Lean files under `FixedPointTheorems/` come from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4)
at commit `770940ddf9878cf61952ed53d910b92bca841838`.
They prove Brouwer's fixed-point theorem from a cubical Sperner argument.
The original MIT license is retained as `FixedPointTheorems/LICENSE`.

The local port to Lean 4.33.1 makes these compatibility changes:

- Add module declarations and public imports/exports required by the module system.
- Mark two counting definitions noncomputable and make classical decidability explicit.
- Replace deprecated set lemmas and an unnecessary `haveI`.
- Make the dimension and finite-set equality explicit in the induction step.

`FixedPointTheorems/lean-4.33.1.patch` records every change against that commit.
`VENDOR_MANIFEST.json` records the original and ported file hashes.
No theorem hypothesis or conclusion is weakened. The final theorem's transitive
axioms are checked in `scripts/AxiomAudit.lean`; Brouwer is not a custom axiom.

The rest of the proof project is licensed under Apache 2.0; see the root `LICENSE`.
