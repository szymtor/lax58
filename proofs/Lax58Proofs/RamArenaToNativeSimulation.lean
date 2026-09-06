import Lax58Proofs.RamArenaToNativeCompiler
import Lax58Proofs.RamListArena

namespace Lax58Proofs.RamArenaToNativeSimulation

open Lax13.Ram
open RamVirtualMemory RamVirtualMacros
open RamListArena
open RamArenaToNativeCompiler

structure AdapterScratch (v originalLength remaining firstFlag : Nat)
    (scratch : Nat → Nat) : Prop where
  compiler : CompilerScratch v scratch
  originalLength_eq : scratch 6 = originalLength
  remaining_eq : scratch 7 = remaining
  six_eq : scratch 8 = 6
  one_eq : scratch 9 = 1
  firstFlag_eq : scratch 10 = firstFlag

theorem AdapterScratch.preserve {v originalLength remaining firstFlag : Nat}
    {before after : Nat → Nat} (hbefore : AdapterScratch v originalLength remaining firstFlag before)
    (hcompiler : CompilerScratch v after)
    (hpreserved : ScratchPreservedFrom 6 before after) :
    AdapterScratch v originalLength remaining firstFlag after := by
  exact ⟨hcompiler,
    (hpreserved 6 (by omega)).trans hbefore.originalLength_eq,
    (hpreserved 7 (by omega)).trans hbefore.remaining_eq,
    (hpreserved 8 (by omega)).trans hbefore.six_eq,
    (hpreserved 9 (by omega)).trans hbefore.one_eq,
    (hpreserved 10 (by omega)).trans hbefore.firstFlag_eq⟩

inductive InputRelation (v originalLength : Nat) :
    List Nat → List Nat → (Nat → Nat) → Prop
  | first (values suffix : List Nat) (scratch : Nat → Nat)
      (hlength : values.length = originalLength)
      (hscratch : AdapterScratch v originalLength (originalLength + 1) 1 scratch) :
      InputRelation v originalLength (originalLength :: values)
        (naturalTriples values ++ suffix) scratch
  | rest (values suffix : List Nat) (scratch : Nat → Nat)
      (hlength : values.length ≤ originalLength)
      (hscratch : AdapterScratch v originalLength values.length 0 scratch) :
      InputRelation v originalLength values (naturalTriples values ++ suffix) scratch

theorem InputRelation.preserve {v originalLength : Nat}
    {logical physical : List Nat} {before after : Nat → Nat}
    (hrelation : InputRelation v originalLength logical physical before)
    (hcompiler : CompilerScratch v after)
    (hpreserved : ScratchPreservedFrom 6 before after) :
    InputRelation v originalLength logical physical after := by
  cases hrelation with
  | first values suffix scratch hlength hscratch =>
      exact InputRelation.first values suffix after hlength
        (hscratch.preserve hcompiler hpreserved)
  | rest =>
      rename_i suffix hlength hscratch
      exact InputRelation.rest logical suffix after hlength
        (hscratch.preserve hcompiler hpreserved)

theorem InputRelation.compiler {v originalLength : Nat}
    {logical physical : List Nat} {scratch : Nat → Nat}
    (h : InputRelation v originalLength logical physical scratch) :
    CompilerScratch v scratch := by
  cases h with
  | first _ _ _ _ hscratch => exact hscratch.compiler
  | rest _ _ _ _ hscratch => exact hscratch.compiler

theorem InputRelation.view {v originalLength : Nat}
    {logical physical : List Nat} {scratch : Nat → Nat}
    (h : InputRelation v originalLength logical physical scratch) :
    (∃ values suffix,
      logical = originalLength :: values ∧
      physical = naturalTriples values ++ suffix ∧
      values.length = originalLength ∧
      AdapterScratch v originalLength (originalLength + 1) 1 scratch) ∨
    (∃ values suffix,
      logical = values ∧
      physical = naturalTriples values ++ suffix ∧
      values.length ≤ originalLength ∧
      AdapterScratch v originalLength values.length 0 scratch) := by
  cases h with
  | first values suffix scratch hlength hscratch =>
      exact Or.inl ⟨values, suffix, rfl, rfl, hlength, hscratch⟩
  | rest =>
      rename_i suffix hlength hscratch
      exact Or.inr ⟨logical, suffix, rfl, rfl, hlength, hscratch⟩

theorem prelude_execute (v n : Nat) (rest : List Nat)
    (hcapacity : 32 ≤ 2 ^ (v + 1)) (hn : n < 2 ^ v)
    (hroot : 6 * n < 2 ^ (v + 1)) :
    ∃ scratch,
      AdapterScratch v n (n + 1) 1 scratch ∧
      execute (v + 1) RamArenaToNativeCompiler.prelude
        (state 0 (fun _ => 0) (fun _ => 0) (6 * n :: rest) []) =
        some (state 10 (fun _ => 0) scratch rest []) := by
  let initialScratch := put (put (fun _ => 0) 1 2) 0 (2 ^ v - 1)
  let afterSix := put initialScratch 8 6
  let afterRoot := put afterSix 6 (6 * n)
  let afterLength := put afterRoot 6 n
  let afterOne := put afterLength 9 1
  let afterRemaining := put afterOne 7 (n + 1)
  let finalScratch := put afterRemaining 10 1
  have hsmallN : n < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))
  have hremaining : n + 1 < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    have := Nat.two_pow_pos v
    omega
  have hsixWord : 6 % 2 ^ (v + 1) = 6 := Nat.mod_eq_of_lt (by omega)
  have honeWord : 1 % 2 ^ (v + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  refine ⟨finalScratch, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor <;> simp [finalScratch, afterRemaining, afterOne, afterLength,
        afterRoot, afterSix, initialScratch, put]
    all_goals simp [finalScratch, afterRemaining, afterOne, afterLength,
      afterRoot, afterSix, initialScratch, put]
  · rw [show RamArenaToNativeCompiler.prelude = RamVirtualCompiler.prelude ++
        [.set sixRegister 6, .read nativeLengthRegister,
         .div nativeLengthRegister nativeLengthRegister sixRegister,
         .set oneRegister 1, .add remainingRegister nativeLengthRegister oneRegister,
         .set firstRegister 1] by rfl,
      execute_append,
      RamVirtualMacros.prelude_execute v 0 (fun _ => 0) (fun _ => 0)
        (6 * n :: rest) [] (by omega)]
    simp only [Option.bind_some]
    change execute (v + 1)
      [.set 17 6, .read 13, .div 13 13 17, .set 19 1, .add 15 13 19, .set 21 1]
      (state 4 (fun _ => 0) initialScratch (6 * n :: rest) []) = _
    rw [show [Instr.set 17 6, Instr.read 13, Instr.div 13 13 17, Instr.set 19 1,
        Instr.add 15 13 19, Instr.set 21 1] =
        [Instr.set 17 6] ++ ([Instr.read 13] ++ ([Instr.div 13 13 17] ++
          ([Instr.set 19 1] ++ ([Instr.add 15 13 19] ++ [Instr.set 21 1])))) by rfl,
      execute_append,
      setRegister_execute v 4 8 6 (fun _ => 0) initialScratch
        (6 * n :: rest) [] (by omega), hsixWord, Option.bind_some,
      execute_append,
      readRegister_execute v (4 + 1) 6 (6 * n) rest (fun _ => 0) afterSix []
        (by omega), Nat.mod_eq_of_lt hroot, Option.bind_some,
      execute_append]
    have hdiv : execute (v + 1) [.div 13 13 17]
        (state (4 + 1 + 1) (fun _ => 0) afterRoot rest []) =
        some (state (4 + 1 + 1 + 1) (fun _ => 0) afterLength rest []) := by
      rw [show [.div 13 13 17] =
          [BinaryKind.instruction .div (2 * 6 + 1) (2 * 6 + 1) (2 * 8 + 1)] by rfl,
        binaryRegister_execute .div v (4 + 1 + 1) 6 6 8 (fun _ => 0)
          afterRoot rest [] (by omega) (by omega) (by omega)]
      change some (state (4 + 1 + 1 + 1) (fun _ => 0)
        (put afterRoot 6 (afterRoot 6 / afterRoot 8 % 2 ^ (v + 1))) rest []) = _
      have hsix : afterRoot 8 = 6 := by simp [afterRoot, afterSix]
      have hrootValue : afterRoot 6 = 6 * n := by simp [afterRoot]
      rw [hrootValue, hsix, show 6 * n / 6 = n by simp [Nat.mul_comm],
        Nat.mod_eq_of_lt hsmallN]
    rw [hdiv, Option.bind_some, execute_append,
      setRegister_execute v (4 + 1 + 1 + 1) 9 1 (fun _ => 0) afterLength
        rest [] (by omega), honeWord, Option.bind_some, execute_append]
    have hadd : execute (v + 1) [.add 15 13 19]
        (state (4 + 1 + 1 + 1 + 1) (fun _ => 0) afterOne rest []) =
        some (state (4 + 1 + 1 + 1 + 1 + 1) (fun _ => 0)
          afterRemaining rest []) := by
      rw [show [.add 15 13 19] =
          [BinaryKind.instruction .add (2 * 7 + 1) (2 * 6 + 1) (2 * 9 + 1)] by rfl,
        binaryRegister_execute .add v (4 + 1 + 1 + 1 + 1) 7 6 9 (fun _ => 0)
          afterOne rest [] (by omega) (by omega) (by omega)]
      change some (state (4 + 1 + 1 + 1 + 1 + 1) (fun _ => 0)
        (put afterOne 7 ((afterOne 6 + afterOne 9) % 2 ^ (v + 1))) rest []) = _
      rw [show afterOne 6 = n by simp [afterOne, afterLength],
        show afterOne 9 = 1 by simp [afterOne], Nat.mod_eq_of_lt hremaining]
    rw [hadd, Option.bind_some,
      setRegister_execute v (4 + 1 + 1 + 1 + 1 + 1) 10 1 (fun _ => 0)
        afterRemaining rest [] (by omega), honeWord]

def Simulates (v originalLength : Nat) (source physical : State) : Prop :=
  ∃ scratch physicalInput,
    Normalized v source.mem ∧
    InputRelation v originalLength source.inp physicalInput scratch ∧
    physical = state (location source.pc) source.mem scratch physicalInput source.out

def withInput (source : State) (input : List Nat) : State :=
  { source with inp := input }

theorem effect_withInput_of_notRead {v : Nat} {instruction : Instr}
    {source next : State} (physicalInput : List Nat)
    (hnotRead : NotRead instruction) (heffect : instruction.effect v source = some next) :
    instruction.effect v (withInput source physicalInput) =
      some (withInput next physicalInput) := by
  cases instruction <;> simp [NotRead] at hnotRead
  all_goals simp only [Instr.effect] at heffect ⊢
  all_goals try { cases heffect; rfl }
  all_goals simp at heffect

theorem run_paddedBody_of_notRead {v : Nat} {program : Program} {instruction : Instr}
    {source next : State} {scratch : Nat → Nat} (physicalInput : List Nat)
    (hcapacity : 32 ≤ 2 ^ (v + 1)) (hfetch : program[source.pc]? = some instruction)
    (hnotRead : NotRead instruction) (hscratch : CompilerScratch v scratch)
    (hnormal : Normalized v source.mem) (heffect : instruction.effect v source = some next) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      RamVirtualSimulation.BranchReady v instruction source nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      run (v + 1) (compile program) 16
        (state (location source.pc) source.mem scratch physicalInput source.out) =
        some (state (location source.pc + 16) next.mem nextScratch
          physicalInput next.out) := by
  let sourceWithInput := withInput source physicalInput
  let nextWithInput := withInput next physicalInput
  have heffectWithInput : instruction.effect v sourceWithInput = some nextWithInput :=
    effect_withInput_of_notRead physicalInput hnotRead heffect
  have hnormalWithInput : Normalized v sourceWithInput.mem := by
    simpa [sourceWithInput, withInput] using hnormal
  rcases RamVirtualSimulation.paddedBody_effect (v := v)
      (physicalPc := location source.pc) (i := instruction)
      (source := sourceWithInput) (next := nextWithInput)
      (by omega : 16 ≤ 2 ^ (v + 1)) hscratch hnormalWithInput heffectWithInput with
    ⟨nextScratch, hsNext, hready, hhigh, hexecute⟩
  have hlinear : ∀ i ∈ paddedBody program.length source.pc instruction,
      StraightLine i := by
    rw [paddedBody_eq_of_notRead program.length source.pc instruction hnotRead]
    intro i hi
    simp only [RamVirtualCompiler.paddedBody, List.mem_append,
      List.mem_replicate] at hi
    rcases hi with hi | ⟨_, rfl⟩
    · exact body_straightLine instruction i hi
    · trivial
  have hpaddedFetch : ∀ k, k < (paddedBody program.length source.pc instruction).length →
      (compile program)[location source.pc + k]? =
        (paddedBody program.length source.pc instruction)[k]? := by
    intro k hk
    exact compile_get_paddedBody program source.pc instruction hfetch k (by simpa using hk)
  refine ⟨nextScratch, hsNext, ?_, hhigh, ?_⟩
  · simpa [sourceWithInput, withInput, RamVirtualSimulation.BranchReady] using hready
  · rw [show 16 = (paddedBody program.length source.pc instruction).length by simp,
      run_eq_execute (v + 1) (compile program)
        (paddedBody program.length source.pc instruction)
        (state (location source.pc) source.mem scratch physicalInput source.out)
        hlinear hpaddedFetch]
    rw [paddedBody_eq_of_notRead program.length source.pc instruction hnotRead]
    simpa [sourceWithInput, nextWithInput, withInput] using hexecute

theorem run_read_first_prefix {v n pc target : Nat} {program : Program}
    {memory scratch : Nat → Nat} {physicalInput output : List Nat}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hfetch : program[pc]? = some (.read target))
    (hn : n < 2 ^ v)
    (hscratch : AdapterScratch v n (n + 1) 1 scratch) :
    run (v + 1) (compile program) 6
      (state (location pc) memory scratch physicalInput output) =
      some (state (location pc + 9) memory
        (put (put (put scratch 2 13) 5 n) 10 0) physicalInput output) := by
  have h0 := compile_get_paddedBody program pc (.read target) hfetch 0 (by omega)
  have h1 := compile_get_paddedBody program pc (.read target) hfetch 1 (by omega)
  have h2 := compile_get_paddedBody program pc (.read target) hfetch 2 (by omega)
  have h3 := compile_get_paddedBody program pc (.read target) hfetch 3 (by omega)
  have h4 := compile_get_paddedBody program pc (.read target) hfetch 4 (by omega)
  have h5 := compile_get_paddedBody program pc (.read target) hfetch 5 (by omega)
  have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
  have h21 : 21 % 2 ^ (v + 1) = 21 := Nat.mod_eq_of_lt (by omega)
  have h13 : 13 % 2 ^ (v + 1) = 13 := Nat.mod_eq_of_lt (by omega)
  have hnPhysical : n < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))
  have hremainingValue : merge memory scratch (15 % 2 ^ (v + 1)) = n + 1 := by
    rw [h15]
    simpa [hscratch.remaining_eq] using merge_odd memory scratch 7
  have hfirstValue : merge memory scratch (21 % 2 ^ (v + 1)) = 1 := by
    rw [h21]
    simpa [hscratch.firstFlag_eq] using merge_odd memory scratch 10
  have hset13 := set_odd v memory scratch 5 13 (by decide) (by omega)
  have hloadN := set_odd v memory (put scratch 2 13) 11 n (by decide) (by omega)
  have hset0 := set_odd v memory (put (put scratch 2 13) 5 n) 21 0
    (by decide) (by omega)
  simp [paddedBody, body, readBody] at h0 h1 h2 h3 h4 h5
  simp only [run, step, h0, h1, h2, h3, h4, h5, Instr.effect, state,
    hremainingValue, hfirstValue, h15, h21, h13, hscratch.remaining_eq, hscratch.firstFlag_eq,
    hscratch.originalLength_eq, hset13, hloadN, hset0,
    merge_odd, put_same, Option.bind_some]
  simp [remainingRegister, firstRegister, nativeLengthRegister,
    RamVirtualCompiler.addressRegister, RamVirtualCompiler.resultRegister,
    hremainingValue, hfirstValue,
    hscratch.remaining_eq, hscratch.firstFlag_eq, hscratch.originalLength_eq,
    h0, h1, h2, h3, h4, h5, hset13, hloadN, hset0, hnPhysical, put]
  have h5mod : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
  have haddress : merge memory (put scratch 2 13) 5 = 13 := by
    simpa using merge_odd memory (put scratch 2 13) 2
  have hnative : merge memory (put scratch 2 13) 13 = n := by
    simpa [hscratch.originalLength_eq] using merge_odd memory (put scratch 2 13) 6
  have hloadN' : setCell (v + 1) (merge memory (put scratch 2 13)) 11 n =
      merge memory (put (put scratch 2 13) 5 n) := by
    simpa [Nat.mod_eq_of_lt hnPhysical] using hloadN
  have hset0' : setCell (v + 1) (merge memory (put (put scratch 2 13) 5 n)) 21 0 =
      merge memory (put (put (put scratch 2 13) 5 n) 10 0) := by
    simpa using hset0
  rw [h13, h5mod, haddress, h13, hnative, hloadN', hset0']

theorem run_read_first_body {v n pc target : Nat} {program : Program}
    {memory scratch : Nat → Nat} {physicalInput output : List Nat}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hfetch : program[pc]? = some (.read target))
    (hn : n < 2 ^ v)
    (hscratch : AdapterScratch v n (n + 1) 1 scratch) :
    ∃ nextScratch,
      AdapterScratch v n n 0 nextScratch ∧
      run (v + 1) (compile program) 13
        (state (location pc) memory scratch physicalInput output) =
        some (state (location pc + 16) (setCell v memory target n)
          nextScratch physicalInput output) := by
  let prefixScratch := put (put (put scratch 2 13) 5 n) 10 0
  let afterSub := put prefixScratch 7 n
  let afterWrite := put (put afterSub 2 (2 * (target % 2 ^ v))) 5 n
  let nextScratch := put afterWrite 2 0
  let tail : Program := [.sub remainingRegister remainingRegister oneRegister] ++
    RamVirtualCompiler.writeCell target ++ [.set 5 0]
  have hprefix := run_read_first_prefix (memory := memory)
    (physicalInput := physicalInput) (output := output) hcapacity hfetch hn hscratch
  have htailLength : tail.length = 7 := by simp [tail, RamVirtualCompiler.writeCell]
  have hlinear : ∀ instruction ∈ tail, StraightLine instruction := by
    intro instruction hinstruction
    simp [tail, RamVirtualCompiler.writeCell, StraightLine] at hinstruction
    rcases hinstruction with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have htailFetch : ∀ k, k < tail.length →
      (compile program)[location pc + 9 + k]? = tail[k]? := by
    intro k hk
    have hcompiled := compile_get_paddedBody program pc (.read target) hfetch (9 + k)
      (by rw [htailLength] at hk; omega)
    rw [show location pc + 9 + k = location pc + (9 + k) by omega]
    rw [htailLength] at hk
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
      omega
    rcases hkCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [tail, paddedBody, body, readBody, RamVirtualCompiler.writeCell,
        List.getElem?_append] using hcompiled
  have hprefixCompiler : CompilerScratch v prefixScratch := by
    exact compilerScratch_put v _
      (compilerScratch_put v _
        (compilerScratch_put v scratch hscratch.compiler 2 13 (by omega)) 5 n (by omega))
      10 0 (by omega)
  have hprefixRemaining : prefixScratch 7 = n + 1 := by
    simp [prefixScratch, put, hscratch.remaining_eq]
  have hprefixOne : prefixScratch 9 = 1 := by
    simp [prefixScratch, put, hscratch.one_eq]
  have hprefixResult : prefixScratch 5 = n := by simp [prefixScratch]
  have hafterSubResult : afterSub 5 = n := by simp [afterSub, hprefixResult]
  have hnPhysical : n < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))
  have hsubMod : (n + 1 - 1) % 2 ^ (v + 1) = n := by
    rw [show n + 1 - 1 = n by omega, Nat.mod_eq_of_lt hnPhysical]
  have htailExecute : execute (v + 1) tail
      (state (location pc + 9) memory prefixScratch physicalInput output) =
      some (state (location pc + 16) (setCell v memory target n)
        nextScratch physicalInput output) := by
    rw [show tail = [.sub 15 15 19] ++ RamVirtualCompiler.writeCell target ++
        [.set 5 0] by rfl, execute_append, execute_append]
    have hsubExecute := binaryRegister_execute .sub v (location pc + 9) 7 7 9
      memory prefixScratch physicalInput output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction] at hsubExecute
    rw [hsubExecute]
    simp only [BinaryKind.value, hprefixRemaining, hprefixOne, hsubMod,
      Option.bind_some]
    change (execute (v + 1) (RamVirtualCompiler.writeCell target)
      (state (location pc + 9 + 1) memory afterSub physicalInput output)).bind
        (execute (v + 1) [Instr.set 5 0]) = _
    rw [RamVirtualMacros.writeCell_execute v (location pc + 9 + 1) target memory
      afterSub physicalInput output (by omega)]
    · simp only [hafterSubResult, Nat.mod_eq_of_lt hn, Option.bind_some]
      change execute (v + 1) [Instr.set 5 0]
        (state (location pc + 9 + 1 + 5) (setCell v memory target n)
          afterWrite physicalInput output) = _
      rw [setRegister_execute v (location pc + 9 + 1 + 5) 2 0
        (setCell v memory target n) afterWrite physicalInput output (by omega)]
      simp [nextScratch]
    · exact hprefixCompiler.1
    · exact hprefixCompiler.2
  refine ⟨nextScratch, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v afterWrite
        (compilerScratch_put v _
          (compilerScratch_put v afterSub
            (compilerScratch_put v prefixScratch hprefixCompiler 7 n (by omega))
            2 _ (by omega)) 5 n (by omega)) 2 0 (by omega)
    all_goals simp [nextScratch, afterWrite, afterSub, prefixScratch, put,
      hscratch.originalLength_eq, hscratch.six_eq, hscratch.one_eq]
  · rw [show 13 = 6 + 7 by omega, run_add, hprefix, Option.bind_some,
      show 7 = tail.length by omega,
      run_eq_execute (v + 1) (compile program) tail
        (state (location pc + 9) memory prefixScratch physicalInput output)
        hlinear htailFetch,
      htailExecute]

theorem run_read_rest_prefix {v originalLength pc target value : Nat}
    {program : Program} {values : List Nat} {memory scratch : Nat → Nat}
    {physicalInput output : List Nat}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hfetch : program[pc]? = some (.read target))
    (hscratch : AdapterScratch v originalLength (value :: values).length 0 scratch) :
    run (v + 1) (compile program) 2
      (state (location pc) memory scratch physicalInput output) =
      some (state (location pc + 6) memory scratch physicalInput output) := by
  have h0 := compile_get_paddedBody program pc (.read target) hfetch 0 (by omega)
  have h1 := compile_get_paddedBody program pc (.read target) hfetch 1 (by omega)
  have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
  have h21 : 21 % 2 ^ (v + 1) = 21 := Nat.mod_eq_of_lt (by omega)
  have hremaining : merge memory scratch (15 % 2 ^ (v + 1)) = values.length + 1 := by
    rw [h15]
    simpa using (merge_odd memory scratch 7).trans hscratch.remaining_eq
  have hfirst : merge memory scratch (21 % 2 ^ (v + 1)) = 0 := by
    rw [h21]
    simpa using (merge_odd memory scratch 10).trans hscratch.firstFlag_eq
  simp [paddedBody, body, readBody] at h0 h1
  simp [run, step, h0, h1, Instr.effect, state, remainingRegister, firstRegister,
    hremaining, hfirst]

theorem run_read_rest_body {v originalLength pc target value : Nat}
    {program : Program} {values suffix : List Nat} {memory scratch : Nat → Nat}
    {output : List Nat}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hfetch : program[pc]? = some (.read target))
    (hvaluesLength : values.length < 2 ^ v)
    (hscratch : AdapterScratch v originalLength (value :: values).length 0 scratch) :
    ∃ nextScratch,
      AdapterScratch v originalLength values.length 0 nextScratch ∧
      run (v + 1) (compile program) 12
        (state (location pc) memory scratch
          (naturalTriples (value :: values) ++ suffix) output) =
        some (state (location pc + 16) (setCell v memory target value)
          nextScratch (naturalTriples values ++ suffix) output) := by
  let physicalRest := naturalTriples values ++ suffix
  let afterTag := put scratch 2 0
  let afterValue := put afterTag 5 (value % 2 ^ (v + 1))
  let afterPadding := put afterValue 2 0
  let afterSub := put afterPadding 7 values.length
  let afterWrite := put (put afterSub 2 (2 * (target % 2 ^ v))) 5 (value % 2 ^ v)
  let nextScratch := put afterWrite 2 0
  let tail : Program := [.read RamVirtualCompiler.addressRegister,
      .read RamVirtualCompiler.resultRegister, .read RamVirtualCompiler.addressRegister,
      .sub remainingRegister remainingRegister oneRegister] ++
    RamVirtualCompiler.writeCell target ++ [.set 5 0]
  have hprefix := run_read_rest_prefix (memory := memory) (physicalInput :=
      naturalTriples (value :: values) ++ suffix) (output := output)
    hcapacity hfetch hscratch
  have htailLength : tail.length = 10 := by simp [tail, RamVirtualCompiler.writeCell]
  have hlinear : ∀ instruction ∈ tail, StraightLine instruction := by
    intro instruction hinstruction
    simp [tail, RamVirtualCompiler.writeCell] at hinstruction
    rcases hinstruction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      trivial
  have htailFetch : ∀ k, k < tail.length →
      (compile program)[location pc + 6 + k]? = tail[k]? := by
    intro k hk
    have hcompiled := compile_get_paddedBody program pc (.read target) hfetch (6 + k)
      (by rw [htailLength] at hk; omega)
    rw [show location pc + 6 + k = location pc + (6 + k) by omega]
    rw [htailLength] at hk
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
        k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
    rcases hkCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [tail, paddedBody, body, readBody, RamVirtualCompiler.writeCell,
        List.getElem?_append] using hcompiled
  have hafterTagCompiler : CompilerScratch v afterTag :=
    compilerScratch_put v scratch hscratch.compiler 2 0 (by omega)
  have hafterValueCompiler : CompilerScratch v afterValue :=
    compilerScratch_put v afterTag hafterTagCompiler 5 _ (by omega)
  have hafterPaddingCompiler : CompilerScratch v afterPadding :=
    compilerScratch_put v afterValue hafterValueCompiler 2 0 (by omega)
  have hafterPaddingRemaining : afterPadding 7 = values.length + 1 := by
    simp [afterPadding, afterValue, afterTag, put, hscratch.remaining_eq]
  have hafterPaddingOne : afterPadding 9 = 1 := by
    simp [afterPadding, afterValue, afterTag, put, hscratch.one_eq]
  have hsubMod : (values.length + 1 - 1) % 2 ^ (v + 1) = values.length := by
    have hlength : values.length < 2 ^ (v + 1) := by
      exact Nat.lt_of_lt_of_le hvaluesLength
        (Nat.pow_le_pow_right (by decide) (by omega))
    rw [show values.length + 1 - 1 = values.length by omega,
      Nat.mod_eq_of_lt hlength]
  have hafterSubCompiler : CompilerScratch v afterSub :=
    compilerScratch_put v afterPadding hafterPaddingCompiler 7 values.length (by omega)
  have hafterSubResult : afterSub 5 = value % 2 ^ (v + 1) := by
    simp [afterSub, afterPadding, afterValue]
  have hmemory : setCell v memory target (value % 2 ^ (v + 1)) =
      setCell v memory target value := by
    funext address
    simp [setCell, RamVirtualMemory.mod_physical_virtual]
  have htailExecute : execute (v + 1) tail
      (state (location pc + 6) memory scratch
        (naturalTriples (value :: values) ++ suffix) output) =
      some (state (location pc + 16) (setCell v memory target value)
        nextScratch physicalRest output) := by
    rw [show naturalTriples (value :: values) ++ suffix =
        0 :: value :: 0 :: physicalRest by simp [naturalTriples, physicalRest],
      show tail = [.read 5] ++ ([.read 11] ++ ([.read 5] ++
        ([.sub 15 15 19] ++ (RamVirtualCompiler.writeCell target ++ [.set 5 0])))) by rfl,
      execute_append,
      readRegister_execute v (location pc + 6) 2 0 (value :: 0 :: physicalRest)
        memory scratch output (by omega), Nat.zero_mod, Option.bind_some, execute_append,
      readRegister_execute v (location pc + 6 + 1) 5 value (0 :: physicalRest)
        memory afterTag output (by omega), Option.bind_some, execute_append,
      readRegister_execute v (location pc + 6 + 1 + 1) 2 0 physicalRest
        memory afterValue output (by omega), Nat.zero_mod, Option.bind_some, execute_append]
    have hsubExecute := binaryRegister_execute .sub v (location pc + 6 + 1 + 1 + 1)
      7 7 9 memory afterPadding physicalRest output (by omega) (by omega) (by omega)
    simp only [BinaryKind.instruction] at hsubExecute
    rw [hsubExecute]
    simp only [BinaryKind.value, hafterPaddingRemaining, hafterPaddingOne, hsubMod,
      Option.bind_some]
    rw [execute_append]
    change (execute (v + 1) (RamVirtualCompiler.writeCell target)
      (state (location pc + 6 + 1 + 1 + 1 + 1) memory afterSub physicalRest output)).bind
        (execute (v + 1) [Instr.set 5 0]) = _
    rw [RamVirtualMacros.writeCell_execute v (location pc + 6 + 1 + 1 + 1 + 1)
      target memory afterSub physicalRest output (by omega)]
    · simp only [hafterSubResult, hmemory, RamVirtualMemory.mod_physical_virtual,
        Option.bind_some]
      change execute (v + 1) [Instr.set 5 0]
        (state (location pc + 6 + 1 + 1 + 1 + 1 + 5)
          (setCell v memory target value) afterWrite physicalRest output) = _
      rw [setRegister_execute v (location pc + 6 + 1 + 1 + 1 + 1 + 5) 2 0
        (setCell v memory target value) afterWrite physicalRest output (by omega)]
      simp [nextScratch]
    · exact hafterSubCompiler.1
    · exact hafterSubCompiler.2
  refine ⟨nextScratch, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v afterWrite
        (compilerScratch_put v _
          (compilerScratch_put v afterSub hafterSubCompiler 2 _ (by omega))
          5 _ (by omega)) 2 0 (by omega)
    all_goals simp [nextScratch, afterWrite, afterSub, afterPadding, afterValue,
      afterTag, put, hscratch.originalLength_eq, hscratch.six_eq,
      hscratch.one_eq, hscratch.firstFlag_eq, physicalRest]
  · rw [show 12 = 2 + 10 by omega, run_add, hprefix, Option.bind_some,
      show 10 = tail.length by omega,
      run_eq_execute (v + 1) (compile program) tail
        (state (location pc + 6) memory scratch
          (naturalTriples (value :: values) ++ suffix) output) hlinear htailFetch,
      htailExecute]

/-- The common two-instruction suffix implements source control flow after
either the ordinary virtual body or one of the arena-reading bodies. -/
theorem run_branch {v : Nat} {program : Program} {instruction : Instr}
    {source next : State} {scratch : Nat → Nat}
    (physicalInput : List Nat)
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some instruction)
    (hready : RamVirtualSimulation.BranchReady v instruction source scratch)
    (heffect : instruction.effect v source = some next) :
    ∃ cost, 1 ≤ cost ∧ cost ≤ 2 ∧
      run (v + 1) (compile program) cost
        (state (location source.pc + 16) next.mem scratch physicalInput next.out) =
        some (state (location next.pc) next.mem scratch physicalInput next.out) := by
  have hfirst := compile_get_branch program source.pc instruction hfetch 0 (by omega)
  have hsecond := compile_get_branch program source.pc instruction hfetch 1 (by omega)
  have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
  cases instruction with
  | set address value =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | load target addressCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | store addressCell valueCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | add target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | sub target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | mul target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | div target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | and target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | shiftl target left right =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | not target sourceCell =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | jump target =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]
  | jzero address target =>
      simp only [Instr.effect] at heffect
      cases heffect
      simp only [RamVirtualSimulation.BranchReady] at hready
      have htest : merge source.mem scratch 11 = source.mem (address % 2 ^ v) := by
        calc
          merge source.mem scratch 11 = scratch 5 := by
            simpa using merge_odd source.mem scratch 5
          _ = source.mem (address % 2 ^ v) := hready
      by_cases hzero : source.mem (address % 2 ^ v) = 0
      · refine ⟨1, by omega, by omega, ?_⟩
        simp [run, step, hfirst, branch, Instr.effect, state,
          RamVirtualCompiler.resultRegister, h11, htest, hzero]
      · refine ⟨2, by omega, by omega, ?_⟩
        simp [run, step, hfirst, hsecond, branch, Instr.effect, state,
          RamVirtualCompiler.resultRegister, h11, htest, hzero]
  | halt =>
      simp only [Instr.effect] at heffect
      contradiction
  | read address =>
      simp only [Instr.effect] at heffect
      cases hinput : source.inp with
      | nil => simp [hinput] at heffect
      | cons value rest =>
          simp [hinput] at heffect
          cases heffect
          refine ⟨1, by omega, by omega, ?_⟩
          simp [run, step, hfirst, branch, Instr.effect, state]
  | write address =>
      simp only [Instr.effect] at heffect
      cases heffect
      refine ⟨1, by omega, by omega, ?_⟩
      simp [run, step, hfirst, branch, Instr.effect, state]

/-- One successful source step on the native list tape is simulated directly
from the list's structural-arena tape. -/
theorem simulation_step {v originalLength : Nat} {program : Program}
    {source next physical : State}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hlength : originalLength < 2 ^ v)
    (hsimulates : Simulates v originalLength source physical)
    (hstep : step v program source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 18 ∧ run (v + 1) (compile program) cost physical = some nextPhysical ∧
      Simulates v originalLength next nextPhysical := by
  rcases hsimulates with ⟨scratch, physicalInput, hnormal, hinput, rfl⟩
  simp only [step] at hstep
  cases hfetch : program[source.pc]? with
  | none => simp [hfetch] at hstep
  | some instruction =>
      rw [hfetch] at hstep
      simp only [Option.bind_some] at hstep
      by_cases hnotRead : NotRead instruction
      · rcases run_paddedBody_of_notRead (physicalInput := physicalInput) hcapacity
          hfetch hnotRead hinput.compiler hnormal hstep with
          ⟨bodyScratch, hsBody, hready, hbodyHigh, hbody⟩
        have hnextInput : next.inp = source.inp := by
          cases instruction <;> simp [NotRead] at hnotRead
          all_goals simp only [Instr.effect] at hstep
          all_goals try { cases hstep; rfl }
          all_goals simp at hstep
        rcases run_branch physicalInput hcapacity hfetch hready hstep with
          ⟨branchCost, hcostPositive, hcost, hbranch⟩
        let nextPhysical := state (location next.pc) next.mem bodyScratch
          physicalInput next.out
        refine ⟨16 + branchCost, nextPhysical, by omega, ?_, ?_⟩
        · rw [run_add, hbody, Option.bind_some, hbranch]
        · refine ⟨bodyScratch, physicalInput,
            RamVirtualSimulation.normalized_effect hnormal hstep,
            ?_, rfl⟩
          simpa [hnextInput] using hinput.preserve hsBody hbodyHigh
      · cases instruction with
        | read target =>
            rcases hinput.view with hfirst | hrest
            · rcases hfirst with
                ⟨values, suffix, hsourceInput, hphysicalInput, hvaluesLength, hscratch⟩
              simp only [Instr.effect] at hstep
              have hhead : source.inp.head? = some originalLength := by
                simp [hsourceInput]
              have htail : source.inp.tail = values := by simp [hsourceInput]
              rw [hhead, htail] at hstep
              change some (State.mk (source.pc + 1)
                (setCell v source.mem target originalLength) values source.out) =
                some next at hstep
              injection hstep with hnext
              subst physicalInput
              subst next
              rcases run_read_first_body (memory := source.mem)
                  (physicalInput := naturalTriples values ++ suffix)
                  (output := source.out) hcapacity hfetch hlength hscratch with
                  ⟨bodyScratch, hsBody, hbody⟩
              have heffect : (Instr.read target).effect v source =
                  some (State.mk (source.pc + 1)
                    (setCell v source.mem target originalLength) values source.out) := by
                simp [Instr.effect, hsourceInput]
              rcases run_branch (naturalTriples values ++ suffix) hcapacity hfetch
                  (by trivial) heffect with
                ⟨branchCost, hcostPositive, hcost, hbranch⟩
              let nextPhysical := state (location (source.pc + 1))
                (setCell v source.mem target originalLength) bodyScratch
                (naturalTriples values ++ suffix) source.out
              refine ⟨13 + branchCost, nextPhysical, by omega, ?_, ?_⟩
              · rw [run_add, hbody, Option.bind_some, hbranch]
              · refine ⟨bodyScratch, naturalTriples values ++ suffix,
                  normalized_setCell v source.mem hnormal target
                    originalLength,
                  InputRelation.rest values suffix bodyScratch (by omega)
                    (by rw [hvaluesLength]; exact hsBody), rfl⟩
            · rcases hrest with
                ⟨values, suffix, hsourceInput, hphysicalInput, hvaluesLength, hscratch⟩
              simp only [Instr.effect] at hstep
              subst physicalInput
              cases values with
              | nil => simp [hsourceInput] at hstep
              | cons value values =>
                  have hhead : source.inp.head? = some value := by
                    simp [hsourceInput]
                  have htail : source.inp.tail = values := by simp [hsourceInput]
                  rw [hhead, htail] at hstep
                  change some (State.mk (source.pc + 1)
                    (setCell v source.mem target value) values source.out) =
                    some next at hstep
                  injection hstep with hnext
                  subst next
                  have htailOriginal : values.length < originalLength :=
                    Nat.lt_of_lt_of_le (by simp) hvaluesLength
                  have htailLength : values.length < 2 ^ v :=
                    Nat.lt_trans htailOriginal hlength
                  rcases run_read_rest_body (memory := source.mem) (output := source.out)
                      hcapacity hfetch htailLength hscratch with
                    ⟨bodyScratch, hsBody, hbody⟩
                  have heffect : (Instr.read target).effect v source =
                      some (State.mk (source.pc + 1)
                        (setCell v source.mem target value) values source.out) := by
                    simp [Instr.effect, hsourceInput]
                  rcases run_branch (naturalTriples values ++ suffix) hcapacity hfetch (by trivial)
                      heffect with
                    ⟨branchCost, hcostPositive, hcost, hbranch⟩
                  let nextPhysical := state (location (source.pc + 1))
                    (setCell v source.mem target value) bodyScratch
                    (naturalTriples values ++ suffix) source.out
                  refine ⟨12 + branchCost, nextPhysical, by omega, ?_, ?_⟩
                  · rw [run_add, hbody, Option.bind_some, hbranch]
                  · refine ⟨bodyScratch, naturalTriples values ++ suffix,
                      normalized_setCell v source.mem hnormal target value,
                      InputRelation.rest values suffix bodyScratch
                        (Nat.le_trans (by simp) hvaluesLength) hsBody, rfl⟩
        | set _ _ => simp [NotRead] at hnotRead
        | load _ _ => simp [NotRead] at hnotRead
        | store _ _ => simp [NotRead] at hnotRead
        | add _ _ _ => simp [NotRead] at hnotRead
        | sub _ _ _ => simp [NotRead] at hnotRead
        | mul _ _ _ => simp [NotRead] at hnotRead
        | div _ _ _ => simp [NotRead] at hnotRead
        | and _ _ _ => simp [NotRead] at hnotRead
        | shiftl _ _ _ => simp [NotRead] at hnotRead
        | not _ _ => simp [NotRead] at hnotRead
        | jump _ => simp [NotRead] at hnotRead
        | jzero _ _ => simp [NotRead] at hnotRead
        | halt => simp [NotRead] at hnotRead
        | write _ => simp [NotRead] at hnotRead

/-- Successful runs compose with the same constant-factor bound as the
underlying virtual-memory compiler. -/
theorem simulation_run {v originalLength : Nat} {program : Program} {time : Nat}
    {source next physical : State}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hlength : originalLength < 2 ^ v)
    (hsimulates : Simulates v originalLength source physical)
    (hrun : run v program time source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 18 * time ∧
      run (v + 1) (compile program) cost physical = some nextPhysical ∧
      Simulates v originalLength next nextPhysical := by
  induction time generalizing source next physical with
  | zero =>
      simp only [run] at hrun
      cases hrun
      exact ⟨0, physical, by omega, by simp [run], hsimulates⟩
  | succ time ih =>
      simp only [run] at hrun
      cases hsourceStep : step v program source with
      | none => simp [hsourceStep] at hrun
      | some intermediate =>
          rw [hsourceStep] at hrun
          simp only [Option.bind_some] at hrun
          rcases simulation_step hcapacity hlength hsimulates hsourceStep with
            ⟨firstCost, intermediatePhysical, hfirstCost, hfirstRun,
              hfirstSimulates⟩
          rcases ih hfirstSimulates hrun with
            ⟨restCost, nextPhysical, hrestCost, hrestRun, hnextSimulates⟩
          refine ⟨firstCost + restCost, nextPhysical, by omega, ?_, hnextSimulates⟩
          rw [run_add, hfirstRun, Option.bind_some, hrestRun]

theorem compile_start (v : Nat) (program : Program) (values : List Nat)
    (hcapacity : 32 ≤ 2 ^ (v + 1)) (hlength : values.length < 2 ^ v)
    (hroot : 6 * values.length < 2 ^ (v + 1)) :
    ∃ physical,
      run (v + 1) (compile program) 10
        (initState ((Lax58.WordArena.encode
          (Lax58.StructuralCombinators.list Lax58.StructuralCombinators.nat)
          values).toInput)) = some physical ∧
      Simulates v values.length (initState (values.length :: values)) physical := by
  rcases encode_list_input_prefix values with ⟨suffix, harena⟩
  let remainingInput := naturalTriples values ++ suffix
  rcases prelude_execute v values.length remainingInput hcapacity hlength (by simpa using hroot) with
    ⟨scratch, hscratch, hexecute⟩
  let physical := state 10 (fun _ => 0) scratch remainingInput []
  have hlinear : ∀ instruction ∈ prelude, StraightLine instruction := by
    intro instruction hinstruction
    simp [prelude, RamVirtualCompiler.prelude] at hinstruction
    rcases hinstruction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      trivial
  have hfetch : ∀ k, k < prelude.length →
      (compile program)[(initState ((Lax58.WordArena.encode
        (Lax58.StructuralCombinators.list Lax58.StructuralCombinators.nat)
        values).toInput)).pc + k]? = prelude[k]? := by
    intro k hk
    have hk10 : k < 10 := by simpa using hk
    simp [compile, initState, List.getElem?_append, hk10]
  refine ⟨physical, ?_, ?_⟩
  · rw [show 10 = prelude.length by simp,
      run_eq_execute (v + 1) (compile program) prelude
        (initState ((Lax58.WordArena.encode
          (Lax58.StructuralCombinators.list Lax58.StructuralCombinators.nat)
          values).toInput)) hlinear hfetch]
    have hinitial : initState ((Lax58.WordArena.encode
        (Lax58.StructuralCombinators.list Lax58.StructuralCombinators.nat)
        values).toInput) =
        state 0 (fun _ => 0) (fun _ => 0) (6 * values.length :: remainingInput) [] := by
      simp only [initState, state]
      rw [harena]
      congr 1
      funext address
      simp [merge]
    rw [hinitial, hexecute]
  · refine ⟨scratch, remainingInput,
      RamVirtualSimulation.normalized_init v (values.length :: values), ?_, ?_⟩
    · exact InputRelation.first values suffix scratch rfl hscratch
    · rfl

/-- A halted logical computation reaches a halted compiled state. In the
exhausted-read case, the adapter's leading zero test exits the program before
touching the unused suffix of the arena tape. -/
theorem simulation_halt {v originalLength : Nat} {program : Program}
    {source physical : State}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hsimulates : Simulates v originalLength source physical)
    (hhalt : step v program source = none) :
    ∃ cost final,
      cost ≤ 16 ∧ run (v + 1) (compile program) cost physical = some final ∧
      step (v + 1) (compile program) final = none ∧ final.out = source.out := by
  rcases hsimulates with ⟨scratch, physicalInput, hnormal, hinput, rfl⟩
  simp only [step] at hhalt
  cases hfetch : program[source.pc]? with
  | none =>
      have hcompiled : (compile program)[location source.pc]? = none := by
        have hcompiledAtZero := compile_get program source.pc 0 (by omega)
        simpa [hfetch] using hcompiledAtZero
      refine ⟨0, state (location source.pc) source.mem scratch physicalInput source.out,
        by omega, by simp [run], ?_, rfl⟩
      simp [step, state, hcompiled]
  | some instruction =>
      rw [hfetch] at hhalt
      simp only [Option.bind_some] at hhalt
      cases instruction with
      | halt =>
          let padding := List.replicate 16 (Instr.set 5 0)
          have hpaddingDef : paddedBody program.length source.pc Instr.halt = padding := by
            rfl
          have hlinear : ∀ i ∈ padding, StraightLine i := by
            intro i hi
            simp only [padding, List.mem_replicate] at hi
            rcases hi with ⟨_, rfl⟩
            trivial
          have hprefix : ∀ k, k < padding.length →
              (compile program)[location source.pc + k]? = padding[k]? := by
            intro k hk
            rw [← hpaddingDef]
            exact compile_get_paddedBody program source.pc Instr.halt hfetch k
              (by simpa [padding] using hk)
          rcases padding_execute v 16 (location source.pc)
              source.mem scratch physicalInput source.out (by omega) hinput.compiler with
            ⟨nextScratch, hsNext, hfive, hpaddingHigh, hpadding⟩
          let final := state (location source.pc + 16) source.mem nextScratch
            physicalInput source.out
          have hrun : run (v + 1) (compile program) 16
              (state (location source.pc) source.mem scratch physicalInput source.out) =
              some final := by
            rw [show 16 = padding.length by simp [padding],
              run_eq_execute (v + 1) (compile program) padding
                (state (location source.pc) source.mem scratch physicalInput source.out)
                hlinear hprefix]
            exact hpadding
          have hbranch := compile_get_branch program source.pc Instr.halt hfetch 0 (by omega)
          have hfinalHalt : step (v + 1) (compile program) final = none := by
            simp [step, final, hbranch, branch, Instr.effect, state]
          exact ⟨16, final, by omega, hrun, hfinalHalt, rfl⟩
      | read target =>
          rcases hinput.view with hfirst | hrest
          · rcases hfirst with
              ⟨values, suffix, hsourceInput, hphysicalInput, hvaluesLength, hscratch⟩
            simp [Instr.effect, hsourceInput] at hhalt
          · rcases hrest with
              ⟨values, suffix, hsourceInput, hphysicalInput, hvaluesLength, hscratch⟩
            have hvaluesNil : values = [] := by
              cases values with
              | nil => rfl
              | cons value values => simp [Instr.effect, hsourceInput] at hhalt
            have hsourceNil : source.inp = [] := hsourceInput.trans hvaluesNil
            subst values
            subst physicalInput
            have hcompiledRead := compile_get_paddedBody program source.pc (.read target)
              hfetch 0 (by omega)
            have hfirstInstruction :
                (compile program)[location source.pc]? =
                  some (.jzero remainingRegister (location program.length)) := by
              simpa [paddedBody, body, readBody] using hcompiledRead
            have hremaining : merge source.mem scratch
                (remainingRegister % 2 ^ (v + 1)) = 0 := by
              have h15 : remainingRegister % 2 ^ (v + 1) = remainingRegister :=
                Nat.mod_eq_of_lt (by simpa [remainingRegister] using
                  (show 15 < 2 ^ (v + 1) by omega))
              rw [h15]
              simpa [remainingRegister, hsourceNil] using
                (merge_odd source.mem scratch 7).trans hscratch.remaining_eq
            let final := State.mk (location program.length) (merge source.mem scratch)
              (naturalTriples [] ++ suffix) source.out
            have hrun : run (v + 1) (compile program) 1
                (state (location source.pc) source.mem scratch
                  (naturalTriples [] ++ suffix) source.out) = some final := by
              simp [run, step, hfirstInstruction, Instr.effect, state, hremaining, final]
            have houtside : (compile program)[location program.length]? = none := by
              rw [show location program.length = (compile program).length by simp]
              exact List.getElem?_eq_none (by omega)
            have hfinalHalt : step (v + 1) (compile program) final = none := by
              simp [step, final, houtside]
            exact ⟨1, final, by omega, by simpa [hsourceNil] using hrun,
              hfinalHalt, rfl⟩
      | set address value => simp [Instr.effect] at hhalt
      | load target addressCell => simp [Instr.effect] at hhalt
      | store addressCell valueCell => simp [Instr.effect] at hhalt
      | add target left right => simp [Instr.effect] at hhalt
      | sub target left right => simp [Instr.effect] at hhalt
      | mul target left right => simp [Instr.effect] at hhalt
      | div target left right => simp [Instr.effect] at hhalt
      | and target left right => simp [Instr.effect] at hhalt
      | shiftl target left right => simp [Instr.effect] at hhalt
      | not target sourceCell => simp [Instr.effect] at hhalt
      | jump target => simp [Instr.effect] at hhalt
      | jzero address target => simp [Instr.effect] at hhalt
      | write address => simp [Instr.effect] at hhalt

/-- Compile a native-list computation into one reading the distinguished
structural arena. The physical machine uses one additional address bit. -/
theorem runsTo_compile {v : Nat} {program : Program} {values output : List Nat}
    {time : Nat}
    (hcapacity : 32 ≤ 2 ^ (v + 1))
    (hlength : values.length < 2 ^ v)
    (hroot : 6 * values.length < 2 ^ (v + 1))
    (hruns : RunsTo v program (values.length :: values) output time) :
    ∃ physicalTime ≤ 18 * time + 26,
      RunsTo (v + 1) (compile program)
        ((Lax58.WordArena.encode
          (Lax58.StructuralCombinators.list Lax58.StructuralCombinators.nat)
          values).toInput) output physicalTime := by
  rcases hruns with ⟨sourceFinal, hsourceRun, hsourceHalt, houtput⟩
  rcases compile_start v program values hcapacity hlength hroot with
    ⟨physicalStart, hstart, hstartSimulates⟩
  rcases simulation_run hcapacity hlength hstartSimulates hsourceRun with
    ⟨runCost, physicalFinal, hrunCost, hrun, hfinalSimulates⟩
  rcases simulation_halt hcapacity hfinalSimulates hsourceHalt with
    ⟨haltCost, final, hhaltCost, hhaltRun, hphysicalHalt, hfinalOutput⟩
  refine ⟨10 + runCost + haltCost, by omega, final, ?_, hphysicalHalt, ?_⟩
  · rw [show 10 + runCost + haltCost = 10 + (runCost + haltCost) by omega,
      run_add, hstart, Option.bind_some, run_add, hrun, Option.bind_some, hhaltRun]
  · rw [hfinalOutput, houtput]

end Lax58Proofs.RamArenaToNativeSimulation
