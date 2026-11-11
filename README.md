# NumPy Lean Check

A Lean 4 model of the integer and shape machinery inside NumPy, tested against the real library and used to look for bugs.

The method follows [python-formalization](https://github.com/Broyojo/python-formalization) and [julia-in-lean](https://github.com/MilesCranmer/julia-in-lean). Each NumPy function in scope is copied into Lean line by line from one pinned source version. The Lean model and the real NumPy then run side by side on generated inputs. Properties are stated over all inputs and are either proved in Lean or refuted with a counterexample. A refuted property that is NumPy's fault becomes a bug record with a reproducer.

This repository is at an early stage. The sections below will fill in as the work moves on.
