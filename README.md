# NumPy Lean Check

A Lean 4 model of the integer and shape machinery inside NumPy, tested against the real library and used to look for bugs.

The method follows [python-formalization](https://github.com/Broyojo/python-formalization) and [julia-in-lean](https://github.com/MilesCranmer/julia-in-lean). Each NumPy function in scope is copied into Lean line by line from one pinned source version. The Lean model and the real NumPy then run side by side on generated inputs. Properties are stated over all inputs and are either proved in Lean or refuted with a counterexample. A refuted property that is NumPy's fault becomes a bug record with a reproducer.

## Results

Everything is about NumPy 2.5.4 (commit `a3d0ef1df045b858e68115001fdabc930bb3b68c`) on arm64 macOS, with Lean 4.35.0 and no Mathlib. The Lean side is about 9,400 lines and the Python test side about 3,600 lines.

The model has nine areas. There are 50 differential test files, and each one agrees with NumPy on 50,000 of 50,000 generated cases on each of seeds 0, 1 and 2. The Lean files state 208 properties, of which 121 are proved and 87 are refuted with a concrete counterexample. There is no `sorry` and no new axiom. Thirty-four proofs use `native_decide` for exhaustive checks over small finite ranges, and each one says so in a comment.

There are 55 bug records, with 5 of high, 18 of medium and 32 of low severity. They are listed in [bugs/FINDINGS.md](bugs/FINDINGS.md). The high ones are writes outside the output buffer in `np.bincount` and `np.repeat`, two silent wraps of `datetime64` values into a different century, and a buffer format string that drops struct padding, so a `memoryview` round trip reads the wrong bytes.

Every record was searched for in the open and closed issues and pull requests of numpy/numpy on 12 November 2026, and the cited code was compared with NumPy main. 26 records are new, 13 are related to an existing report without being described by it, 7 are covered by an open issue or pull request, 2 by a closed issue, and 7 were fixed on main after 2.5.4. Of the high ones, only the `bincount` write is new.

| Area | What it covers | Proven | Refuted | Bug records |
| --- | --- | --- | --- | --- |
| Shape | `reshape` with an unknown dimension and the constructor size check | 1 | 1 | 1 |
| IntArith | integer floor_divide, remainder, divmod, power, gcd, lcm, shifts, absolute, sign and multiply, on the scalar and array paths | 18 | 4 | 1 |
| DType | `can_cast`, `promote_types`, `result_type`, NEP 50 Python scalars and very large Python ints in float and complex types | 18 | 9 | 4 |
| Indexing | integer and slice indices, `ravel_multi_index`, `unravel_index`, `take`, `put`, `choose`, `repeat`, `diagonal` and `searchsorted` | 8 | 11 | 10 |
| Broadcast | broadcasting, `broadcast_to`, contiguity flags, no-copy reshape, `moveaxis`, `transpose`, `squeeze`, `split`, `insert`, `delete` and `pad` widths | 15 | 14 | 10 |
| Datetime | calendar conversion, unit casts, comparisons across units, ISO 8601 parsing and printing, and business days | 14 | 15 | 7 |
| LibInt | `arange`, `binary_repr`, `base_repr`, `packbits`, `unpackbits`, `isin`, `digitize`, `bincount`, `unique`, `fill_diagonal` and integer `histogram` | 16 | 15 | 10 |
| Strings | find, count, padding, replace, partition, strip and slice on the S, U and StringDType kinds | 16 | 6 | 4 |
| NpyFormat | the `.npy` header writer and reader, `frombuffer` bounds, `loadtxt` integer parsing and the PEP 3118 buffer format round trip | 15 | 12 | 8 |

The model covers a small part of NumPy, chosen because its logic is integer and index arithmetic that can be checked exactly. Floating point arithmetic, linear algebra, FFT, random, sorting, masked arrays and most of the ufunc machinery are out of scope.

## Layout

- `lean/NumpyLean/<Area>/` holds `Model.lean` (the mirrored source), `Props.lean` (the properties) and `Diff.lean` (the handlers for the test executable).
- `difftest/` holds the differential tests, which run through `difftest/harness.py`.
- `bugs/` holds one YAML record per bug, with a reproducer in `bugs/repro/`.
- `docs/MODELLING.md` is the instruction sheet for adding an area.

## Running it

```sh
scripts/fetch_numpy.sh
cd lean && lake build && cd ..
.venv/bin/python difftest/shape_reshape_diff.py --cases 50000 --seed 0
.venv/bin/python scripts/check_props.py
.venv/bin/python scripts/check_bugs.py
.venv/bin/python scripts/findings.py
```
