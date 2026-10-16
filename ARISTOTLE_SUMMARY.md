# Summary of changes for run 28eb5f6e-f18c-4bb4-8ec6-7e181bf9714a
I worked on all three parts. A full `lake build` from the repository root succeeds (9920 jobs). The new files contain no `sorry`, and their theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**1. Mathlib.** It was already installed. `lakefile.toml` and `lake-manifest.json` pin revision `520045ab…`, which is built for the `lean-toolchain` version (v4.32.1), and its compiled files are present, so I changed nothing. As before, the `CCLib` library itself does not import Mathlib; the code that uses real numbers is under the second entry point `export/CCLibReal.lean`.

**2. Duplicated code.** The Mathlib/Batteries/core duplicates were already listed in `MATHLIB_DUPLICATION.md`, with Lean proofs that the two versions agree. This time I checked for duplication inside the port and found the largest case:
- **What is duplicated:** the target-independent back-end passes and their proofs have one copy per target: `backend/` (the aarch64 instance), `arm/`, `powerpc/`, `riscV/` and `x86/`. The copies differ only in namespace and imports.
- **Size:** 163 file names occur more than once. After normalizing the target names, 58 of them are at least 95% identical across every copy (about 63,000 extra non-blank lines), and 96 are at least 85% identical (about 108,000).
- **Where it's documented:** the summary and a suggested fix are a new section of `MATHLIB_DUPLICATION.md`. The fix is to make the shared files take the target's `Op`/`Machregs`/`Conventions1` as a parameter. No library code can replace these files. The full per-file list with similarity scores is in the new `TARGET_DUPLICATION.md`.
- **How it was measured:** the scores come from a one-off text comparison script, not a Lean proof.
- **Not done:** I did not refactor these files or replace any duplicates in place.

**3. Porting continued.** The next real-number gap was in Flocq's `Round_odd.v` and `Double_rounding.v`. Before this, `round_N_odd` was proved only for rational inputs. The square-root double-rounding theorems were stated through the stand-in relation `is_round_sqrt` rather than as `round (sqrt x)`. The new files follow the Rocq folder layout:
- `flocq/Core/Generic_fmtRealTransfer.lean`:
  - `roundR_near_irrational'` works for irrationals of either sign.
  - `roundR_roundR_of_rat`: if rounding twice gives the same result as rounding once for every rational input, it does so for every real input too.
- `flocq/Prop/Round_oddReal.lean` (from `Round_odd.v`):
  - `Zrnd_oddR`, Rocq's `Zrnd_odd` on the reals, proved to be a valid rounding that agrees with the rational version.
  - `round_odd_opp` on the reals.
  - **`round_N_oddR`**: Rocq's `round_N_odd` for every real `x`.
  - Instances for the FLX and FLT formats. These assume `1 < prec`, which is needed for round-to-nearest-even to exist.
- `flocq/Prop/Double_roundingReal.lean` (from `Double_rounding.v`):
  - `round_round_eqR`, Rocq's `round_round_eq` on the reals.
  - **`round_round_sqrtR`**: Rocq's `round_round_sqrt` with `Real.sqrt`, plus its FLX, FLT and FTZ instances.
  - The `radix_ge_4` variants and their instances.
  - Real-number forms of `round_round_plus`, `minus`, `mult` and `div`.
  - As in the rest of the port, the float arguments are rational, while `Real.sqrt x` can be any real.
  - The FTZ square-root theorem drops Rocq's unused hypothesis `4 ≤ beta`.

The changes are recorded as "Status update 71" in `PORT_GAP_ANALYSIS.md`, and `export/CCLibReal.lean` and `export/LEAN.md` are updated. The main results are in the properties table, marked proved. The biggest remaining gap is unchanged: the ARM/PowerPC correctness proofs are still blocked, because they need a value layer that works for both 32-bit and 64-bit pointers.