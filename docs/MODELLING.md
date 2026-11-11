# How an area is modelled

This file is the instruction sheet for anyone, human or agent, who adds an area to this repository. `lean/NumpyLean/Shape/` and `difftest/shape_reshape_diff.py` are the worked example, so read them first.

## The pinned version

Everything is about NumPy 2.5.4, commit `a3d0ef1df045b858e68115001fdabc930bb3b68c`. `scripts/fetch_numpy.sh` puts the source in `vendor/numpy/` and builds `.venv/` with the same version. Always run Python as `.venv/bin/python`. Every model cites the source as `path:line` relative to `vendor/numpy/numpy/`.

## Files for an area called `Foo`

- `lean/NumpyLean/Foo/Model.lean` holds the models.
- `lean/NumpyLean/Foo/Props.lean` holds the properties.
- `lean/NumpyLean/Foo/Diff.lean` holds the `npdiff` handlers and exports `handlers : List (String × Handler)`.
- `difftest/foo_<topic>_diff.py` holds one differential test per handler or per group of handlers.
- `bugs/foo-<slug>.yaml` and `bugs/repro/foo-<slug>.py` hold one bug record each.

Do not edit `lean/NumpyLean.lean`, `lean/Main.lean` or files of another area. The maintainer wires new areas in. To build and test an area before it is wired in, see "Building" below.

## Step 1: mirror the source

Write the Lean model by following the C or Python source line by line. Keep the same branch order, the same order of checks and the same error cases. Do not model what the documentation says. Model what the code does.

- Keep values as `Int` and apply `wrapSigned`, `wrapUnsigned` or `wrap64` from `NumpyLean/Common/Intp.lean` at every point where the C code can wrap. C signed overflow is undefined behaviour, so write down in a comment that the model assumes two's complement wrap, which is what the arm64 and x86-64 builds do.
- C `/` and `%` truncate toward zero. Use `Int.tdiv` and `Int.tmod` for them. Python `//` and `%` floor. Use `Int.fdiv` and `Int.fmod` for those.
- Model an error as a constructor of an error type, one constructor per distinct error site, with the message in a doc comment.
- Leave floating point out unless the function only compares or copies floats. Lean `Float` is IEEE double and can be used for exact operations (`+`, `-`, `*`, `/`, `sqrt`, comparisons), but never for `libm` functions.
- Use only core Lean and `Std`. Mathlib is not a dependency, because the build must stay small enough for a 16 GB laptop.

## Step 2: differential test

Write `gen(rng)` so that it returns the `npdiff` input line and the string that real NumPy gives for the same input. Bias the generator toward edges: empty inputs, zero, negative values, the minimum and maximum of each integer type, values near `2**31`, `2**32`, `2**62` and `2**63`. Check that each outcome class shows up in the printed outcome counts. A test where 99 percent of the cases take the same branch does not test much.

The area passes when at least 50,000 cases agree on each of three seeds:

```sh
.venv/bin/python difftest/foo_topic_diff.py --cases 50000 --seed 0
```

A mismatch means the model is wrong, so fix the model. Never change the expected side to make a test pass. If the mismatch shows NumPy doing something surprising, that is a lead for step 3.

Never run a case that can allocate a large array. Keep every real array under about 10 MB. The machine has 16 GB and other work runs on it.

## Step 3: prove or refute

State properties over all inputs in `Props.lean`. Good sources of properties are the docstring of the public function, the comments in the source, algebraic laws that users rely on (round trips, commutativity, agreement between two code paths, agreement with the Python builtin of the same name) and safety conditions (no index outside the buffer, no wrapped size).

Each property has a doc comment whose first line is exactly:

```
PROP <area>.<function>.<name> : PROVEN
```

with `PROVEN`, `REFUTED` or `OPEN`. The second line gives the source of the claim.

- `PROVEN`: the theorem states the property.
- `REFUTED`: the theorem states the negation and proves it with a concrete counterexample. Never weaken a false statement until it becomes true. A refuted property is a result.
- `OPEN`: the statement is inside a comment and no theorem exists yet.

`sorry` and new axioms are not allowed. `decide` is preferred for concrete facts. `native_decide` and `bv_decide` are allowed when `decide` is too slow, and the file must say so in a comment next to the use, because they trust the compiler.

After a property is proved or refuted on the model, run the same statement on the real NumPy for the counterexample or for a sample of inputs. A theorem about a model that does not match the library is worth nothing.

## Step 4: bug records

A refuted property is a bug candidate when real NumPy shows the same behaviour and the behaviour is wrong by the documentation, by a comment in the source, by memory safety or by plain consistency. Write two files.

`bugs/foo-<slug>.yaml`:

```yaml
id: foo-<slug>
title: one line that names the function and the wrong behaviour
area: Foo
kind: crash | memory | wrong-result | wrong-error | docs-mismatch | inconsistent
severity: high | medium | low
numpy_version: 2.5.4
source: path/to/file.c:123
property: NumpyLean.Foo.theorem_name
summary: >
  What happens, what the documentation or the source says should happen, and the cause with line numbers.
upstream: a link to an existing NumPy issue if one is known, or "not searched"
```

`bugs/repro/foo-<slug>.py` is a short script that prints `REPRODUCED` when the wrong behaviour is present and `NOT REPRODUCED` otherwise. A reproducer for a crash must run the crashing code in a child process and look at the return code, so that the script itself always finishes.

Severity guide: `high` is a crash, memory corruption or silent wrong numbers on ordinary input. `medium` is a wrong result or wrong error on unusual input. `low` is a documentation mismatch or an inconsistency that is unlikely to hurt anyone.

Be honest about known behaviour. If the documentation already warns about the behaviour, it is not a bug. Record it as a `REFUTED` property and say so, without a bug record.

## Building

Build one module without touching the root files:

```sh
cd lean && lake build NumpyLean.Foo.Props NumpyLean.Foo.Diff
```

To run a differential test before the area is wired into `Main.lean`, ask the maintainer, or test the handler with `#eval` in a scratch file that is not committed.

## Writing style

Comments, commit messages and markdown use plain English in full sentences. Do not wrap prose lines. Do not mention any tool used to write the code.
