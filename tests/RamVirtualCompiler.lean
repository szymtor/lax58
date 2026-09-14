import Lax560851Proofs.RamArenaToNativeCompiler
import Lax560851Proofs.RamNativeToArenaCompiler
import Lax560851.StructuralCombinators
import Lax560851.WordArena

open Lax865980.Ram Lax560851Proofs.RamVirtualCompiler
open Lax560851.StructuralCombinators Lax560851.WordArena

-- Executable regression tests, not substitutes for the general simulation
-- proof. Failure throws an elaboration-time IO error, so the suite fails.
private def outputAfterHalt (w : Nat) (p : Program) : Nat → State → Option (List Nat)
  | 0, _ => none
  | fuel + 1, s => match step w p s with
      | none => some s.out
      | some next => outputAfterHalt w p fuel next

private def checkTranslation (label : String) (v : Nat) (p : Program)
    (input expected : List Nat) : IO Unit := do
  let source := outputAfterHalt v p 100 (initState input)
  let compiled := outputAfterHalt (v + 1) (compile p) 2000 (initState input)
  unless source == some expected do
    throw (IO.userError s!"{label}: incorrect source test fixture: {source}")
  unless compiled == source do
    throw (IO.userError s!"{label}: compiled output {compiled}, expected {source}")

#eval checkTranslation "empty program" 3 [] [] []
#eval checkTranslation "explicit halt" 3 [.halt] [123] []
#eval checkTranslation "exhausted read" 3 [.set 0 7, .write 0, .read 0, .write 0] [] [7]
#eval checkTranslation "input truncation" 3 [.read 0, .write 0, .halt] [127] [7]
#eval checkTranslation "wrapped direct address" 3
  [.set 17 15, .write 1, .halt] [] [7]
#eval checkTranslation "virtual overflow" 3
  [.set 0 7, .set 1 3, .add 2 0 1, .mul 3 0 1, .write 2, .write 3, .halt] [] [2, 5]
#eval checkTranslation "subtraction and division" 3
  [.set 0 3, .set 1 7, .sub 2 0 1, .div 3 1 0, .div 4 1 2,
   .write 2, .write 3, .write 4, .halt] [] [0, 2, 0]
#eval checkTranslation "bit operations" 3
  [.set 0 3, .set 1 2, .shiftl 2 0 1, .not 3 0, .and 4 0 1,
   .write 2, .write 3, .write 4, .halt] [] [4, 4, 2]
#eval checkTranslation "indirect storage" 3
  [.set 0 7, .set 1 6, .store 0 1, .load 2 0, .write 2, .write 7, .halt] [] [6, 6]
#eval checkTranslation "both conditional branches" 3
  [.jzero 0 2, .set 1 7, .set 0 1, .jzero 0 6, .write 0, .jump 7,
   .set 0 5, .write 0, .halt] [] [1, 1]
#eval checkTranslation "out-of-range jump" 3 [.jump 1000] [] []
#eval checkTranslation "larger width" 7
  [.set 255 1000, .write 127, .not 0 127, .write 0, .halt] [] [104, 23]

private def checkArenaToNative (label : String) (v : Nat) (p : Program)
    (xs expected : List Nat) : IO Unit := do
  let native := xs.length :: xs
  let arena := (encode (list nat) xs).toInput
  let source := outputAfterHalt v p 300 (initState native)
  let compiled := outputAfterHalt (v + 1)
    (Lax560851Proofs.RamArenaToNativeCompiler.compile p) 5000 (initState arena)
  unless source == some expected do
    throw (IO.userError s!"{label}: incorrect source test fixture: {source}")
  unless compiled == source do
    throw (IO.userError s!"{label}: arena adapter output {compiled}, expected {source}")

#eval checkArenaToNative "arena to native reads" 5
  [.read 0, .write 0, .read 0, .write 0, .read 0, .write 0, .halt]
  [4, 7] [2, 4, 7]
#eval checkArenaToNative "arena to native exhaustion" 5
  [.read 0, .write 0, .read 0, .write 0, .read 0, .write 0,
   .read 0, .write 0, .halt]
  [4, 7] [2, 4, 7]
#eval checkArenaToNative "empty arena list" 5
  [.read 0, .write 0, .read 0, .write 0, .halt]
  [] [0]

private def checkNativeToArena (label : String) (v : Nat) (p : Program)
    (xs expected : List Nat) : IO Unit := do
  let native := xs.length :: xs
  let arena := (encode (list nat) xs).toInput
  let source := outputAfterHalt v p 1000 (initState arena)
  let compiled := outputAfterHalt (v + 1)
    (Lax560851Proofs.RamNativeToArenaCompiler.compile p) 10000 (initState native)
  unless source == some expected do
    throw (IO.userError s!"{label}: incorrect source test fixture: {source}")
  unless compiled == source do
    throw (IO.userError s!"{label}: native adapter output {compiled}, expected {source}")

private def echoWords (count : Nat) : Program :=
  List.flatten (List.replicate count [.read 0, .write 0]) ++ [.halt]

#eval checkNativeToArena "native to arena full tape" 6 (echoWords 16)
  [4, 7] [12, 0, 4, 0, 0, 7, 0, 0, 0, 0, 1, 3, 6, 1, 0, 9]
#eval checkNativeToArena "native to arena empty list" 6 (echoWords 4)
  [] [0, 0, 0, 0]
#eval checkNativeToArena "native to arena exhaustion" 6 (echoWords 17)
  [4, 7] [12, 0, 4, 0, 0, 7, 0, 0, 0, 0, 1, 3, 6, 1, 0, 9]

-- The emitted block layout itself is proved for every instruction/program.
example (p : Program) : (compile p).length = 4 + 18 * p.length := compile_length p

/-- info: 'Lax560851Proofs.RamVirtualCompiler.mask_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lax560851Proofs.RamVirtualCompiler.mask_result
/-- info: 'Lax560851Proofs.RamVirtualCompiler.compile_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lax560851Proofs.RamVirtualCompiler.compile_get

#print axioms Lax560851Proofs.RamVirtualMacros.readCell_execute
#print axioms Lax560851Proofs.RamVirtualMacros.writeCell_execute
#print axioms Lax560851Proofs.RamVirtualMacros.compile_start
#print axioms Lax560851Proofs.RamVirtualMacros.run_eq_execute
#print axioms Lax560851Proofs.RamVirtualSimulation.runsTo_compile
