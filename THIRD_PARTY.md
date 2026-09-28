# Third-party proof dependency

Brouwer's fixed-point theorem is imported from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4)
at commit `770940ddf9878cf61952ed53d910b92bca841838`.
The library proves it from a cubical Sperner argument and is licensed under
[MIT](https://github.com/harfe/fixed-point-theorems-lean4/blob/770940ddf9878cf61952ed53d910b92bca841838/LICENSE).

Lake fetches the original library as a Git dependency. Its source is not copied
into this repository or modified during the build. The project uses Lean 4.32.0
and Mathlib v4.32.0, matching the library's own configuration.

`lakefile.toml` pins the library's commit; `lake-manifest.json` locks all transitive
dependencies. `scripts/verify.py` checks the dependency revisions, confirms that
their tracked files are unchanged, and audits the final theorem's transitive axioms.

The proof and code in this repository are licensed under Apache 2.0; see `LICENSE`.
