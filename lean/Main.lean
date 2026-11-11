import NumpyLean

/-
`npdiff` is the Lean side of the differential tests. It reads one test case per line on standard input and writes one result per line on standard output.
-/
open NumpyLean.Wire

def allHandlers : List (String × Handler) :=
  NumpyLean.Shape.handlers

def runLine (line : String) : String :=
  match line.splitOn " " with
  | [] => "BADLINE"
  | op :: args =>
    match allHandlers.lookup op with
    | some h => h args
    | none => s!"NOHANDLER {op}"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (runLine ((line.splitOn "\n").headD ""))
  loop stdin stdout

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  loop stdin stdout
  stdout.flush
