import NumpyLean.Common.Wire

/-
The read loop shared by `npdiff` and by the per-area executables. It reads one test case per line on standard input and writes one result per line on standard output.
-/
namespace NumpyLean
open NumpyLean.Wire

def runLine (handlers : List (String × Handler)) (line : String) : String :=
  match line.splitOn " " with
  | [] => "BADLINE"
  | op :: args =>
    match handlers.lookup op with
    | some h => h args
    | none => s!"NOHANDLER {op}"

partial def driverLoop (handlers : List (String × Handler)) (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (runLine handlers ((line.splitOn "\n").headD ""))
  driverLoop handlers stdin stdout

def runHandlers (handlers : List (String × Handler)) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  driverLoop handlers stdin stdout
  stdout.flush

end NumpyLean
