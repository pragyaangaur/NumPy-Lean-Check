import NumpyLean

/-
`npdiff` is the Lean side of the differential tests, with the handlers of every area. Each area also has its own executable `npdiff_<area>` under `exe/`, so that one area can be built and tested while another is broken.
-/
open NumpyLean.Wire

def allHandlers : List (String × Handler) :=
  NumpyLean.Shape.handlers ++
  NumpyLean.IntArith.handlers ++
  NumpyLean.Indexing.handlers ++
  NumpyLean.Broadcast.handlers ++
  NumpyLean.Datetime.handlers ++
  NumpyLean.Strings.handlers ++
  NumpyLean.DType.handlers ++
  NumpyLean.LibInt.handlers ++
  NumpyLean.NpyFormat.handlers

def main : IO Unit := NumpyLean.runHandlers allHandlers
