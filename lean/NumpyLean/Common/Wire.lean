/-
Text format used between the Python differential tests and the `npdiff` executable.

One test case is one line of tokens separated by single spaces. The first token is the operation name. A list of integers is written as comma separated values, and the empty list is written as `_`.
-/
namespace NumpyLean.Wire

def parseInt (s : String) : Int := s.toInt?.getD 0

def parseInts (s : String) : List Int :=
  if s == "_" then [] else (s.splitOn ",").map parseInt

def fmtInts (l : List Int) : String :=
  if l.isEmpty then "_" else ",".intercalate (l.map toString)

def fmtBool (b : Bool) : String := if b then "True" else "False"

/-- A handler takes the tokens after the operation name and returns one line of output. -/
abbrev Handler := List String → String

end NumpyLean.Wire
