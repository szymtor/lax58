import Lax560851Proofs.RamNativeToArenaCompiler
import Lax560851Proofs.RamListArena
import Mathlib.Data.List.TakeDrop

namespace Lax560851Proofs.RamNativeToArenaSimulation

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open Lax759944Proofs.Legacy.Ram
open RamVirtualMemory RamVirtualMacros
open RamNativeToArenaCompiler RamListArena

/-- The native payloads buffered by the prelude. The buffer lives above the
fixed compiler/adapter registers in the protected odd-addressed half. -/
def BufferStored (values : List Nat) (scratch : Nat → Nat) : Prop :=
  ∀ (index : Nat) (hindex : index < values.length),
    scratch (bufferBase + index) = values[index]'hindex

structure AdapterScratch (v : Nat) (values : List Nat)
    (consumed remaining mode : Nat) (scratch : Nat → Nat) : Prop where
  compiler : CompilerScratch v scratch
  length_eq : scratch 6 = values.length
  remaining_eq : scratch 7 = remaining
  mode_eq : scratch 8 = mode
  one_eq : scratch 9 = 1
  three_eq : scratch 10 = 3
  six_eq : scratch 11 = 6
  bufferAddress_eq : scratch 12 = 2 * (bufferBase + consumed) + 1
  root_eq : scratch 13 = 6 * values.length
  zero_eq : scratch 14 = 0
  buffer : BufferStored values scratch

theorem BufferStored.preserve {values : List Nat} {before after : Nat → Nat}
    (hbuffer : BufferStored values before)
    (hpreserved : ScratchPreservedFrom 6 before after) :
    BufferStored values after := by
  intro index hindex
  rw [hpreserved (bufferBase + index) (by simp [bufferBase]; omega)]
  exact hbuffer index hindex

theorem AdapterScratch.preserve {v consumed remaining mode : Nat}
    {values : List Nat} {before after : Nat → Nat}
    (hbefore : AdapterScratch v values consumed remaining mode before)
    (hcompiler : CompilerScratch v after)
    (hpreserved : ScratchPreservedFrom 6 before after) :
    AdapterScratch v values consumed remaining mode after := by
  refine ⟨hcompiler, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hbefore.buffer.preserve hpreserved⟩
  · exact (hpreserved 6 (by omega)).trans hbefore.length_eq
  · exact (hpreserved 7 (by omega)).trans hbefore.remaining_eq
  · exact (hpreserved 8 (by omega)).trans hbefore.mode_eq
  · exact (hpreserved 9 (by omega)).trans hbefore.one_eq
  · exact (hpreserved 10 (by omega)).trans hbefore.three_eq
  · exact (hpreserved 11 (by omega)).trans hbefore.six_eq
  · exact (hpreserved 12 (by omega)).trans hbefore.bufferAddress_eq
  · exact (hpreserved 13 (by omega)).trans hbefore.root_eq
  · exact (hpreserved 14 (by omega)).trans hbefore.zero_eq

/-- Logical arena-input phases mirrored by the read generator. The native
physical tape is empty after the prelude, while this relation exposes exactly
the unread suffix of the distinguished arena tape to the simulated source. -/
inductive InputRelation (v : Nat) (original : List Nat) :
    List Nat → (Nat → Nat) → Prop
  | root (scratch : Nat → Nat)
      (hscratch : AdapterScratch v original 0 original.length 0 scratch) :
      InputRelation v original
        (6 * original.length ::
          (naturalTriples original ++ [0, 0, 0] ++
            pairSuffix original.length original.length)) scratch
  | naturalTag (consumed : Nat) (values : List Nat) (scratch : Nat → Nat)
      (hconsumed : consumed ≤ original.length)
      (hdrop : original.drop consumed = values)
      (hscratch : AdapterScratch v original consumed values.length 1 scratch) :
      InputRelation v original
        (naturalTriples values ++ [0, 0, 0] ++
          pairSuffix original.length original.length) scratch
  | naturalValue (consumed value : Nat) (values : List Nat) (scratch : Nat → Nat)
      (hconsumed : consumed < original.length)
      (hdrop : original.drop consumed = value :: values)
      (hscratch : AdapterScratch v original consumed (value :: values).length 2 scratch) :
      InputRelation v original
        (value :: 0 :: naturalTriples values ++ [0, 0, 0] ++
          pairSuffix original.length original.length) scratch
  | naturalPadding (consumed value : Nat) (values : List Nat) (scratch : Nat → Nat)
      (hconsumed : consumed < original.length)
      (hdrop : original.drop consumed = value :: values)
      (hscratch : AdapterScratch v original (consumed + 1)
        (value :: values).length 3 scratch) :
      InputRelation v original
        (0 :: naturalTriples values ++ [0, 0, 0] ++
          pairSuffix original.length original.length) scratch
  | nilValue (scratch : Nat → Nat)
      (hscratch : AdapterScratch v original original.length 0 4 scratch) :
      InputRelation v original
        (0 :: 0 :: pairSuffix original.length original.length) scratch
  | nilPadding (scratch : Nat → Nat)
      (hscratch : AdapterScratch v original original.length 0 5 scratch) :
      InputRelation v original
        (0 :: pairSuffix original.length original.length) scratch
  | pairTag (remaining : Nat) (scratch : Nat → Nat)
      (hremaining : remaining ≤ original.length)
      (hscratch : AdapterScratch v original original.length remaining 6 scratch) :
      InputRelation v original (pairSuffix original.length remaining) scratch
  | pairLeft (remaining : Nat) (scratch : Nat → Nat)
      (hpositive : 0 < remaining) (hremaining : remaining ≤ original.length)
      (hscratch : AdapterScratch v original original.length remaining 7 scratch) :
      InputRelation v original
        (3 * (remaining - 1) ::
          (6 * original.length - 3 * (remaining - 1) - 3) ::
          pairSuffix original.length (remaining - 1)) scratch
  | pairRight (remaining : Nat) (scratch : Nat → Nat)
      (hpositive : 0 < remaining) (hremaining : remaining ≤ original.length)
      (hscratch : AdapterScratch v original original.length remaining 8 scratch) :
      InputRelation v original
        ((6 * original.length - 3 * (remaining - 1) - 3) ::
          pairSuffix original.length (remaining - 1)) scratch

theorem InputRelation.compiler {v : Nat} {original logical : List Nat}
    {scratch : Nat → Nat} (h : InputRelation v original logical scratch) :
    CompilerScratch v scratch := by
  cases h <;> rename_i hscratch <;> exact hscratch.compiler

theorem InputRelation.preserve {v : Nat} {original logical : List Nat}
    {before after : Nat → Nat}
    (hrelation : InputRelation v original logical before)
    (hcompiler : CompilerScratch v after)
    (hpreserved : ScratchPreservedFrom 6 before after) :
    InputRelation v original logical after := by
  cases hrelation with
  | root _ hscratch => exact .root after (hscratch.preserve hcompiler hpreserved)
  | naturalTag consumed values _ hconsumed hdrop hscratch =>
      exact .naturalTag consumed values after hconsumed hdrop
        (hscratch.preserve hcompiler hpreserved)
  | naturalValue consumed value values _ hconsumed hdrop hscratch =>
      exact .naturalValue consumed value values after hconsumed hdrop
        (hscratch.preserve hcompiler hpreserved)
  | naturalPadding consumed value values _ hconsumed hdrop hscratch =>
      exact .naturalPadding consumed value values after hconsumed hdrop
        (hscratch.preserve hcompiler hpreserved)
  | nilValue _ hscratch => exact .nilValue after (hscratch.preserve hcompiler hpreserved)
  | nilPadding _ hscratch => exact .nilPadding after (hscratch.preserve hcompiler hpreserved)
  | pairTag remaining _ hremaining hscratch =>
      exact .pairTag remaining after hremaining (hscratch.preserve hcompiler hpreserved)
  | pairLeft remaining _ hpositive hremaining hscratch =>
      exact .pairLeft remaining after hpositive hremaining
        (hscratch.preserve hcompiler hpreserved)
  | pairRight remaining _ hpositive hremaining hscratch =>
      exact .pairRight remaining after hpositive hremaining
        (hscratch.preserve hcompiler hpreserved)

def Simulates (v : Nat) (original : List Nat) (source physical : State) : Prop :=
  ∃ scratch logicalInput,
    Normalized v source.mem ∧ source.inp = logicalInput ∧
    InputRelation v original logicalInput scratch ∧
    physical = state (location source.pc) source.mem scratch [] source.out

def withInput (source : State) (input : List Nat) : State :=
  { source with inp := input }

theorem effect_withInput_of_notRead {v : Nat} {instruction : Instr}
    {source next : State} (physicalInput : List Nat)
    (hnotRead : NotRead instruction)
    (heffect : instruction.effect v source = some next) :
    instruction.effect v (withInput source physicalInput) =
      some (withInput next physicalInput) := by
  cases instruction <;> simp [NotRead] at hnotRead
  all_goals simp only [Instr.effect] at heffect ⊢
  all_goals try { cases heffect; rfl }
  all_goals simp at heffect

/-- The ordinary virtual body followed by enough no-ops to reach slot 64. -/
theorem paddedBody_effect_of_notRead {v physicalPc : Nat} (programLength sourcePc : Nat)
    {instruction : Instr}
    {source next : State} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hnotRead : NotRead instruction)
    (hscratch : CompilerScratch v scratch)
    (hnormal : Normalized v source.mem)
    (heffect : instruction.effect v source = some next) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      RamVirtualSimulation.BranchReady v instruction source nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      execute (v + 1) (paddedBody programLength sourcePc instruction)
        (state physicalPc source.mem scratch [] source.out) =
        some (state (physicalPc + blockBodyLength) next.mem nextScratch [] next.out) := by
  let sourceEmpty := withInput source []
  let nextEmpty := withInput next []
  have heffectEmpty : instruction.effect v sourceEmpty = some nextEmpty :=
    effect_withInput_of_notRead [] hnotRead heffect
  have hnormalEmpty : Normalized v sourceEmpty.mem := by
    simpa [sourceEmpty, withInput] using hnormal
  rcases RamVirtualSimulation.body_effect (physicalPc := physicalPc)
      (by omega : 16 ≤ 2 ^ (v + 1)) hscratch hnormalEmpty heffectEmpty with
    ⟨bodyScratch, hsBody, hready, hbodyHigh, hbody⟩
  have hbody' : execute (v + 1) (RamVirtualCompiler.body instruction)
      (state physicalPc source.mem scratch [] source.out) =
      some (state (physicalPc + (RamVirtualCompiler.body instruction).length)
        next.mem bodyScratch [] next.out) := by
    simpa [sourceEmpty, nextEmpty, withInput] using hbody
  rcases padding_execute v (blockBodyLength - (RamVirtualCompiler.body instruction).length)
      (physicalPc + (RamVirtualCompiler.body instruction).length)
      next.mem bodyScratch [] next.out (by omega) hsBody with
    ⟨nextScratch, hsNext, hfive, hpaddingHigh, hpadding⟩
  refine ⟨nextScratch, hsNext, ?_, hbodyHigh.trans hpaddingHigh, ?_⟩
  · cases instruction <;> simp only [RamVirtualSimulation.BranchReady] at hready ⊢
    all_goals try trivial
    rw [hfive]
    exact hready
  · rw [paddedBody,
      body_eq_of_notRead programLength sourcePc instruction hnotRead,
      execute_append, hbody']
    simp only [Option.bind_some]
    rw [hpadding]
    congr 2
    have := RamVirtualCompiler.body_length_le instruction
    simp only [blockBodyLength]
    omega

/-- The 64-word body is a genuine straight-line prefix of its compiled block
for every source instruction other than `read`. -/
theorem run_paddedBody_of_notRead {v : Nat} {program : Program}
    {instruction : Instr} {source next : State} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some instruction)
    (hnotRead : NotRead instruction)
    (hscratch : CompilerScratch v scratch)
    (hnormal : Normalized v source.mem)
    (heffect : instruction.effect v source = some next) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      RamVirtualSimulation.BranchReady v instruction source nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      run (v + 1) (compile program) blockBodyLength
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength) next.mem nextScratch
          [] next.out) := by
  have hlinear : ∀ i ∈ paddedBody program.length source.pc instruction,
      StraightLine i := by
    intro i hi
    simp only [paddedBody, List.mem_append, List.mem_replicate] at hi
    rcases hi with hi | ⟨_, rfl⟩
    · rw [body_eq_of_notRead program.length source.pc instruction hnotRead] at hi
      exact body_straightLine instruction i hi
    · trivial
  have hpaddedFetch : ∀ k,
      k < (paddedBody program.length source.pc instruction).length →
      (compile program)[location source.pc + k]? =
        (paddedBody program.length source.pc instruction)[k]? := by
    intro k hk
    exact compile_get_paddedBody program source.pc instruction hfetch k (by simpa using hk)
  rw [show blockBodyLength =
      (paddedBody program.length source.pc instruction).length by simp,
    run_eq_execute (v + 1) (compile program)
      (paddedBody program.length source.pc instruction)
      (state (location source.pc) source.mem scratch [] source.out)
      hlinear hpaddedFetch]
  simpa only [paddedBody_length] using
    (paddedBody_effect_of_notRead (physicalPc := location source.pc)
      program.length source.pc hcapacity hnotRead hscratch hnormal heffect)

theorem run_branch {v : Nat} {program : Program} {instruction : Instr}
    {source next : State} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some instruction)
    (hready : RamVirtualSimulation.BranchReady v instruction source scratch)
    (heffect : instruction.effect v source = some next) :
    ∃ cost, 1 ≤ cost ∧ cost ≤ 2 ∧
      run (v + 1) (compile program) cost
        (state (location source.pc + blockBodyLength) next.mem scratch [] next.out) =
        some (state (location next.pc) next.mem scratch [] next.out) := by
  have hfirst := compile_get_branch program source.pc instruction hfetch 0 (by omega)
  have hsecond := compile_get_branch program source.pc instruction hfetch 1 (by omega)
  simp only [blockBodyLength, Nat.add_zero] at hfirst hsecond ⊢
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

theorem run_read_root_prefix {v : Nat} {program : Program} {source : State}
    {target : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hscratch : AdapterScratch v original 0 original.length 0 scratch) :
    run (v + 1) (compile program) 4
      (state (location source.pc) source.mem scratch [] source.out) =
      some (state (location source.pc + 54) source.mem
        (put (put scratch 5 (6 * original.length)) 8 1) [] source.out) := by
  have h0 := compile_get_paddedBody program source.pc (.read target) hfetch 0
    (by simp [blockBodyLength])
  have h21 := compile_get_paddedBody program source.pc (.read target) hfetch 21
    (by simp [blockBodyLength])
  have h22 := compile_get_paddedBody program source.pc (.read target) hfetch 22
    (by simp [blockBodyLength])
  have h23 := compile_get_paddedBody program source.pc (.read target) hfetch 23
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h0 h21 h22 h23
  have h17 : modeRegister % 2 ^ (v + 1) = modeRegister :=
    Nat.mod_eq_of_lt (by simpa [modeRegister] using (show 17 < 2 ^ (v + 1) by omega))
  have h27 : rootRegister % 2 ^ (v + 1) = rootRegister :=
    Nat.mod_eq_of_lt (by simpa [rootRegister] using (show 27 < 2 ^ (v + 1) by omega))
  have h29 : zeroRegister % 2 ^ (v + 1) = zeroRegister :=
    Nat.mod_eq_of_lt (by simpa [zeroRegister] using (show 29 < 2 ^ (v + 1) by omega))
  have h11 : RamVirtualCompiler.resultRegister % 2 ^ (v + 1) =
      RamVirtualCompiler.resultRegister :=
    Nat.mod_eq_of_lt (by simpa [RamVirtualCompiler.resultRegister] using
      (show 11 < 2 ^ (v + 1) by omega))
  have hmode : merge source.mem scratch (modeRegister % 2 ^ (v + 1)) = 0 := by
    rw [h17]
    simpa [modeRegister] using (merge_odd source.mem scratch 8).trans hscratch.mode_eq
  have hrootValue : merge source.mem scratch (rootRegister % 2 ^ (v + 1)) =
      6 * original.length := by
    rw [h27]
    simpa [rootRegister] using (merge_odd source.mem scratch 13).trans hscratch.root_eq
  have hzero : merge source.mem scratch (zeroRegister % 2 ^ (v + 1)) = 0 := by
    rw [h29]
    simpa [zeroRegister] using (merge_odd source.mem scratch 14).trans hscratch.zero_eq
  have hmodeMod : merge source.mem scratch (17 % 2 ^ (v + 1)) = 0 := by
    simpa [modeRegister] using hmode
  have hrootMod : merge source.mem scratch (27 % 2 ^ (v + 1)) =
      6 * original.length := by
    simpa [rootRegister] using hrootValue
  have hzeroMod : merge source.mem scratch (29 % 2 ^ (v + 1)) = 0 := by
    simpa [zeroRegister] using hzero
  have hmode' : merge source.mem scratch 17 = 0 := by
    change merge source.mem scratch modeRegister = 0
    rw [← h17]
    exact hmode
  have hrootValue' : merge source.mem scratch 27 = 6 * original.length := by
    change merge source.mem scratch rootRegister = 6 * original.length
    rw [← h27]
    exact hrootValue
  have hzero' : merge source.mem scratch 29 = 0 := by
    change merge source.mem scratch zeroRegister = 0
    rw [← h29]
    exact hzero
  have hrootPhysical : 6 * original.length < 2 ^ (v + 1) :=
    Nat.lt_of_lt_of_le hroot (Nat.pow_le_pow_right (by decide) (by omega))
  have hsetResult := set_odd v source.mem scratch 11 (6 * original.length)
    (by decide) (by omega)
  have hsetMode := set_odd v source.mem (put scratch 5 (6 * original.length)) 17 1
    (by decide) (by omega)
  have hsetResult' : setCell (v + 1) (merge source.mem scratch) 11
      (6 * original.length) =
      merge source.mem (put scratch 5 (6 * original.length)) := by
    simpa [Nat.mod_eq_of_lt hrootPhysical] using hsetResult
  have hsetMode' : setCell (v + 1)
      (merge source.mem (put scratch 5 (6 * original.length))) 17 1 =
      merge source.mem (put (put scratch 5 (6 * original.length)) 8 1) := by
    simpa using hsetMode
  simp only [location] at h0 h21 h22 h23 ⊢
  have hstep0 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc) source.mem scratch [] source.out) =
      some (state (preludeLength + blockLength * source.pc + 21)
        source.mem scratch [] source.out) := by
    simp [step, h0, Instr.effect, state, modeRegister, hmodeMod]
  have hstep21 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 21)
        source.mem scratch [] source.out) =
      some (state (preludeLength + blockLength * source.pc + 22)
        source.mem (put scratch 5 (6 * original.length)) [] source.out) := by
    simp [step, h21, Instr.effect, state, RamVirtualCompiler.resultRegister,
      rootRegister, zeroRegister, hrootMod, hzeroMod, hsetResult']
  have hstep22 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 22)
        source.mem (put scratch 5 (6 * original.length)) [] source.out) =
      some (state (preludeLength + blockLength * source.pc + 23)
        source.mem (put (put scratch 5 (6 * original.length)) 8 1) [] source.out) := by
    simp [step, h22, Instr.effect, state, modeRegister, hsetMode']
  have hstep23 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 23)
        source.mem (put (put scratch 5 (6 * original.length)) 8 1) [] source.out) =
      some (state (preludeLength + blockLength * source.pc + 54)
        source.mem (put (put scratch 5 (6 * original.length)) 8 1) [] source.out) := by
    simp [step, h23, Instr.effect, state]
  simp [run, hstep0, hstep21, hstep22, hstep23]

/-- Common tail of every successful generator case: write the generated word
to the simulated target, then execute the five final padding instructions. -/
theorem run_read_write_tail {v : Nat} {program : Program} {source : State}
    {target value : Nat} {memory scratch : Nat → Nat} {output : List Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hscratch : CompilerScratch v scratch)
    (hvalue : scratch 5 = value) :
    ∃ nextScratch,
      CompilerScratch v nextScratch ∧
      ScratchPreservedFrom 6 scratch nextScratch ∧
      run (v + 1) (compile program) 10
        (state (location source.pc + 54) memory scratch [] output) =
        some (state (location source.pc + blockBodyLength)
          (setCell v memory target value) nextScratch [] output) := by
  let afterWrite := put (put scratch 2 (2 * (target % 2 ^ v))) 5 (value % 2 ^ v)
  have hwriteExecute := writeCell_execute v (location source.pc + 54) target
    memory scratch [] output (by omega) hscratch.1 hscratch.2
  rw [hvalue] at hwriteExecute
  change execute (v + 1) (RamVirtualCompiler.writeCell target)
      (state (location source.pc + 54) memory scratch [] output) =
    some (state (location source.pc + 54 + 5) (setCell v memory target value)
      afterWrite [] output) at hwriteExecute
  have hafterCompiler : CompilerScratch v afterWrite :=
    compilerScratch_put v _
      (compilerScratch_put v scratch hscratch 2 _ (by omega)) 5 _ (by omega)
  rcases padding_execute v 5 (location source.pc + 59)
      (setCell v memory target value) afterWrite [] output (by omega) hafterCompiler with
    ⟨nextScratch, hsNext, hfive, hpaddingHigh, hpaddingExecute⟩
  have hwriteLinear : ∀ instruction ∈ RamVirtualCompiler.writeCell target,
      StraightLine instruction := by
    intro instruction hinstruction
    simp [RamVirtualCompiler.writeCell] at hinstruction
    rcases hinstruction with rfl | rfl | rfl | rfl | rfl <;> trivial
  have hwriteFetch : ∀ k, k < (RamVirtualCompiler.writeCell target).length →
      (compile program)[location source.pc + 54 + k]? =
        (RamVirtualCompiler.writeCell target)[k]? := by
    intro k hk
    have hcompiled := compile_get_paddedBody program source.pc (.read target)
      hfetch (54 + k) (by
        simp [RamVirtualCompiler.writeCell] at hk
        simp only [blockBodyLength]
        omega)
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp [RamVirtualCompiler.writeCell] at hk
      omega
    rcases hkCases with rfl | rfl | rfl | rfl | rfl <;>
      simpa [paddedBody, body, readBody, RamVirtualCompiler.writeCell,
        List.getElem?_append] using hcompiled
  let padding := List.replicate 5 (Instr.set 5 0)
  have hpaddingLinear : ∀ instruction ∈ padding, StraightLine instruction := by
    intro instruction hinstruction
    simp only [padding, List.mem_replicate] at hinstruction
    rcases hinstruction with ⟨_, rfl⟩
    trivial
  have hpaddingFetch : ∀ k, k < padding.length →
      (compile program)[location source.pc + 59 + k]? = padding[k]? := by
    intro k hk
    have hcompiled := compile_get_paddedBody program source.pc (.read target)
      hfetch (59 + k) (by
        simp [padding] at hk
        simp only [blockBodyLength]
        omega)
    have hkCases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      simp [padding] at hk
      omega
    rcases hkCases with rfl | rfl | rfl | rfl | rfl <;>
      simpa [padding, paddedBody, body, readBody, RamVirtualCompiler.writeCell,
        List.getElem?_append] using hcompiled
  have hwriteRun : run (v + 1) (compile program) 5
      (state (location source.pc + 54) memory scratch [] output) =
      some (state (location source.pc + 59) (setCell v memory target value)
        afterWrite [] output) := by
    rw [show 5 = (RamVirtualCompiler.writeCell target).length by
        simp [RamVirtualCompiler.writeCell],
      run_eq_execute (v + 1) (compile program) (RamVirtualCompiler.writeCell target)
        (state (location source.pc + 54) memory scratch [] output)
        hwriteLinear hwriteFetch,
      hwriteExecute]
  have hpaddingRun : run (v + 1) (compile program) 5
      (state (location source.pc + 59) (setCell v memory target value)
        afterWrite [] output) =
      some (state (location source.pc + blockBodyLength)
        (setCell v memory target value) nextScratch [] output) := by
    rw [show 5 = padding.length by simp [padding],
      run_eq_execute (v + 1) (compile program) padding
        (state (location source.pc + 59) (setCell v memory target value)
          afterWrite [] output) hpaddingLinear hpaddingFetch,
      hpaddingExecute]
    congr 2
  refine ⟨nextScratch, hsNext, ?_, ?_⟩
  · intro index hindex
    rw [hpaddingHigh index hindex]
    have h2 : index ≠ 2 := by omega
    have h5 : index ≠ 5 := by omega
    simp [afterWrite, put, h2, h5]
  · rw [show 10 = 5 + 5 by omega, run_add, hwriteRun, Option.bind_some,
      hpaddingRun]

theorem run_read_root {v : Nat} {program : Program} {source : State}
    {target : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hscratch : AdapterScratch v original 0 original.length 0 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (naturalTriples original ++ [0, 0, 0] ++
          pairSuffix original.length original.length) nextScratch ∧
      run (v + 1) (compile program) 14
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target (6 * original.length)) nextScratch [] source.out) := by
  let phaseScratch := put (put scratch 5 (6 * original.length)) 8 1
  have hprefix := run_read_root_prefix hcapacity hroot hfetch hscratch
  have hphase : AdapterScratch v original 0 original.length 1 phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v scratch hscratch.compiler 5 _ (by omega)) 8 1 (by omega)
    · simp [phaseScratch, put, hscratch.length_eq]
    · simp [phaseScratch, put, hscratch.remaining_eq]
    · simp [phaseScratch]
    · simp [phaseScratch, put, hscratch.one_eq]
    · simp [phaseScratch, put, hscratch.three_eq]
    · simp [phaseScratch, put, hscratch.six_eq]
    · simp [phaseScratch, put, hscratch.bufferAddress_eq]
    · simp [phaseScratch, put, hscratch.root_eq]
    · simp [phaseScratch, put, hscratch.zero_eq]
    · intro index hindex
      have h16 : 16 ≤ bufferBase + index := by simp [bufferBase]
      have h5 : bufferBase + index ≠ 5 := by omega
      have h8 : bufferBase + index ≠ 8 := by omega
      simp [BufferStored, phaseScratch, put, h5, h8]
      exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 6 * original.length)
      (memory := source.mem) (scratch := phaseScratch) (output := source.out)
      hcapacity hfetch hphase.compiler (by simp [phaseScratch]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch, ?_, ?_⟩
  · exact InputRelation.naturalTag 0 original nextScratch (by omega) (by simp)
      (hphase.preserve hsNext hpreserved)
  · rw [show 14 = 4 + 10 by omega, run_add, hprefix, Option.bind_some, htail]

/-- Dispatch mode 1 to the natural-tag case, leaving the result temporary at
zero. -/
theorem run_read_mode_one_dispatch {v : Nat} {program : Program} {source : State}
    {target : Nat} {memory scratch : Nat → Nat} {output : List Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hone : scratch 9 = 1) (hzero : scratch 14 = 0)
    (hmode : scratch 8 = 1) :
    run (v + 1) (compile program) 4
      (state (location source.pc) memory scratch [] output) =
      some (state (location source.pc + 24) memory (put scratch 5 0) [] output) := by
  have h0 := compile_get_paddedBody program source.pc (.read target) hfetch 0
    (by simp [blockBodyLength])
  have h1 := compile_get_paddedBody program source.pc (.read target) hfetch 1
    (by simp [blockBodyLength])
  have h2 := compile_get_paddedBody program source.pc (.read target) hfetch 2
    (by simp [blockBodyLength])
  have h3 := compile_get_paddedBody program source.pc (.read target) hfetch 3
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h0 h1 h2 h3
  simp only [location] at h0 h1 h2 h3 ⊢
  let afterCopy := put scratch 5 1
  have hmodeValue : merge memory scratch (17 % 2 ^ (v + 1)) = 1 := by
    have h17 : 17 % 2 ^ (v + 1) = 17 := Nat.mod_eq_of_lt (by omega)
    rw [h17]
    simpa using (merge_odd memory scratch 8).trans hmode
  have hzeroValue : merge memory scratch (29 % 2 ^ (v + 1)) = 0 := by
    have h29 : 29 % 2 ^ (v + 1) = 29 := Nat.mod_eq_of_lt (by omega)
    rw [h29]
    simpa using (merge_odd memory scratch 14).trans hzero
  have honeValue : merge memory afterCopy (19 % 2 ^ (v + 1)) = 1 := by
    have h19 : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
    rw [h19]
    simpa [afterCopy, put] using (merge_odd memory afterCopy 9).trans (by
      simpa [afterCopy, put] using hone)
  have hresultValue : merge memory afterCopy (11 % 2 ^ (v + 1)) = 1 := by
    have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    rw [h11]
    simpa [afterCopy] using merge_odd memory afterCopy 5
  have hsetCopy := set_odd v memory scratch 11 1 (by decide) (by omega)
  have hsetCopy' : setCell (v + 1) (merge memory scratch) 11 1 =
      merge memory afterCopy := by simpa [afterCopy] using hsetCopy
  have hsetZero := set_odd v memory afterCopy 11 0 (by decide) (by omega)
  have hsetZero' : setCell (v + 1) (merge memory afterCopy) 11 0 =
      merge memory (put scratch 5 0) := by
    simpa [afterCopy, put] using hsetZero
  have hstep0 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc) memory scratch [] output) =
      some (state (preludeLength + blockLength * source.pc + 1)
        memory scratch [] output) := by
    simp [step, h0, Instr.effect, state, modeRegister, hmodeValue]
  have hstep1 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 1) memory scratch [] output) =
      some (state (preludeLength + blockLength * source.pc + 2)
        memory afterCopy [] output) := by
    simp [step, h1, Instr.effect, state, RamVirtualCompiler.resultRegister,
      modeRegister, zeroRegister, hmodeValue, hzeroValue, hsetCopy']
  have hstep2 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 2)
        memory afterCopy [] output) =
      some (state (preludeLength + blockLength * source.pc + 3)
        memory (put scratch 5 0) [] output) := by
    simp [step, h2, Instr.effect, state, RamVirtualCompiler.resultRegister,
      oneRegister, hresultValue, honeValue, hsetZero']
  have hstep3 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 3)
        memory (put scratch 5 0) [] output) =
      some (state (preludeLength + blockLength * source.pc + 24)
        memory (put scratch 5 0) [] output) := by
    have hresultZero : merge memory (put scratch 5 0) (11 % 2 ^ (v + 1)) = 0 := by
      have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
      rw [h11]
      simpa using merge_odd memory (put scratch 5 0) 5
    simp [step, h3, Instr.effect, state, RamVirtualCompiler.resultRegister,
      hresultZero]
  simp [run, hstep0, hstep1, hstep2, hstep3]

theorem run_read_natural_tag_nonempty {v : Nat} {program : Program}
    {source : State} {target consumed value : Nat} {values original : List Nat}
    {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hconsumed : consumed < original.length)
    (hdrop : original.drop consumed = value :: values)
    (hscratch : AdapterScratch v original consumed (value :: values).length 1 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (value :: 0 :: naturalTriples values ++ [0, 0, 0] ++
          pairSuffix original.length original.length) nextScratch ∧
      run (v + 1) (compile program) 18
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target 0) nextScratch [] source.out) := by
  let dispatched := put scratch 5 0
  let phaseScratch := put dispatched 8 2
  have hdispatch := run_read_mode_one_dispatch (memory := source.mem)
    (output := source.out) hcapacity hfetch hscratch.one_eq hscratch.zero_eq
      hscratch.mode_eq
  have h24 := compile_get_paddedBody program source.pc (.read target) hfetch 24
    (by simp [blockBodyLength])
  have h25 := compile_get_paddedBody program source.pc (.read target) hfetch 25
    (by simp [blockBodyLength])
  have h26 := compile_get_paddedBody program source.pc (.read target) hfetch 26
    (by simp [blockBodyLength])
  have h27 := compile_get_paddedBody program source.pc (.read target) hfetch 27
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h24 h25 h26 h27
  simp only [location] at h24 h25 h26 h27
  have hremaining : merge source.mem dispatched (15 % 2 ^ (v + 1)) =
      values.length + 1 := by
    have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [h15]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 7).trans (by
        simpa [dispatched, put] using hscratch.remaining_eq)
  have hsetMode := set_odd v source.mem dispatched 17 2 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem dispatched) 17 2 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 2 < 2 ^ (v + 1) by omega)] using hsetMode
  have hstep24 : step (v + 1) (compile program)
      (state (location source.pc + 24) source.mem dispatched [] source.out) =
      some (state (location source.pc + 25) source.mem dispatched [] source.out) := by
    simp [step, h24, Instr.effect, state, location, remainingRegister, hremaining]
  have hstep25 : step (v + 1) (compile program)
      (state (location source.pc + 25) source.mem dispatched [] source.out) =
      some (state (location source.pc + 26) source.mem dispatched [] source.out) := by
    have hsetZero := set_odd v source.mem dispatched 11 0 (by decide) (by omega)
    simp [step, h25, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      hsetZero, dispatched, put]
  have hstep26 : step (v + 1) (compile program)
      (state (location source.pc + 26) source.mem dispatched [] source.out) =
      some (state (location source.pc + 27) source.mem phaseScratch [] source.out) := by
    simp [step, h26, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep27 : step (v + 1) (compile program)
      (state (location source.pc + 27) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h27, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 4
      (state (location source.pc + 24) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep24, hstep25, hstep26, hstep27]
  have hphase : AdapterScratch v original consumed (value :: values).length 2
      phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega)) 8 2 (by omega)
    all_goals try simp [phaseScratch, dispatched, put, hscratch.length_eq,
      hscratch.remaining_eq, hscratch.one_eq, hscratch.three_eq, hscratch.six_eq,
      hscratch.bufferAddress_eq, hscratch.root_eq, hscratch.zero_eq]
    intro index hindex
    have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
    have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
    simp [BufferStored, phaseScratch, dispatched, put, h5, h8]
    exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 0) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, dispatched]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.naturalValue consumed value values nextScratch hconsumed hdrop
      (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 18 = 4 + 4 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

theorem run_read_natural_tag_empty {v : Nat} {program : Program}
    {source : State} {target consumed : Nat} {original : List Nat}
    {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hconsumed : consumed ≤ original.length)
    (hdrop : original.drop consumed = [])
    (hscratch : AdapterScratch v original consumed 0 1 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (0 :: 0 :: pairSuffix original.length original.length) nextScratch ∧
      run (v + 1) (compile program) 18
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target 0) nextScratch [] source.out) := by
  have hdropLength := congrArg List.length hdrop
  simp only [List.length_drop, List.length_nil] at hdropLength
  have hconsumedEq : consumed = original.length := by omega
  subst consumed
  let dispatched := put scratch 5 0
  let phaseScratch := put dispatched 8 4
  have hdispatch := run_read_mode_one_dispatch (memory := source.mem)
    (output := source.out) hcapacity hfetch hscratch.one_eq hscratch.zero_eq
      hscratch.mode_eq
  have h24 := compile_get_paddedBody program source.pc (.read target) hfetch 24
    (by simp [blockBodyLength])
  have h28 := compile_get_paddedBody program source.pc (.read target) hfetch 28
    (by simp [blockBodyLength])
  have h29 := compile_get_paddedBody program source.pc (.read target) hfetch 29
    (by simp [blockBodyLength])
  have h30 := compile_get_paddedBody program source.pc (.read target) hfetch 30
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h24 h28 h29 h30
  simp only [location] at h24 h28 h29 h30
  have hremaining : merge source.mem dispatched (15 % 2 ^ (v + 1)) = 0 := by
    have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [h15]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 7).trans (by
        simpa [dispatched, put] using hscratch.remaining_eq)
  have hsetMode := set_odd v source.mem dispatched 17 4 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem dispatched) 17 4 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 4 < 2 ^ (v + 1) by omega)] using hsetMode
  have hstep24 : step (v + 1) (compile program)
      (state (location source.pc + 24) source.mem dispatched [] source.out) =
      some (state (location source.pc + 28) source.mem dispatched [] source.out) := by
    simp [step, h24, Instr.effect, state, location, remainingRegister, hremaining]
  have hstep28 : step (v + 1) (compile program)
      (state (location source.pc + 28) source.mem dispatched [] source.out) =
      some (state (location source.pc + 29) source.mem dispatched [] source.out) := by
    have hsetZero := set_odd v source.mem dispatched 11 0 (by decide) (by omega)
    simp [step, h28, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      hsetZero, dispatched, put]
  have hstep29 : step (v + 1) (compile program)
      (state (location source.pc + 29) source.mem dispatched [] source.out) =
      some (state (location source.pc + 30) source.mem phaseScratch [] source.out) := by
    simp [step, h29, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep30 : step (v + 1) (compile program)
      (state (location source.pc + 30) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h30, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 4
      (state (location source.pc + 24) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep24, hstep28, hstep29, hstep30]
  have hphase : AdapterScratch v original original.length 0 4 phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega)) 8 4 (by omega)
    all_goals try simp [phaseScratch, dispatched, put, hscratch.length_eq,
      hscratch.remaining_eq, hscratch.one_eq, hscratch.three_eq, hscratch.six_eq,
      hscratch.bufferAddress_eq, hscratch.root_eq, hscratch.zero_eq]
    intro index hindex
    have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
    have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
    simp [BufferStored, phaseScratch, dispatched, put, h5, h8]
    exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 0) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, dispatched]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.nilValue nextScratch (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 18 = 4 + 4 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

theorem run_read_mode_two_dispatch {v : Nat} {program : Program} {source : State}
    {target : Nat} {memory scratch : Nat → Nat} {output : List Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hone : scratch 9 = 1) (hzero : scratch 14 = 0)
    (hmode : scratch 8 = 2) :
    run (v + 1) (compile program) 6
      (state (location source.pc) memory scratch [] output) =
      some (state (location source.pc + 31) memory (put scratch 5 0) [] output) := by
  have h0 := compile_get_paddedBody program source.pc (.read target) hfetch 0
    (by simp [blockBodyLength])
  have h1 := compile_get_paddedBody program source.pc (.read target) hfetch 1
    (by simp [blockBodyLength])
  have h2 := compile_get_paddedBody program source.pc (.read target) hfetch 2
    (by simp [blockBodyLength])
  have h3 := compile_get_paddedBody program source.pc (.read target) hfetch 3
    (by simp [blockBodyLength])
  have h4 := compile_get_paddedBody program source.pc (.read target) hfetch 4
    (by simp [blockBodyLength])
  have h5 := compile_get_paddedBody program source.pc (.read target) hfetch 5
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h0 h1 h2 h3 h4 h5
  simp only [location] at h0 h1 h2 h3 h4 h5 ⊢
  let copied := put scratch 5 2
  let once := put copied 5 1
  let twice := put once 5 0
  have hmodeValue : merge memory scratch (17 % 2 ^ (v + 1)) = 2 := by
    have h17 : 17 % 2 ^ (v + 1) = 17 := Nat.mod_eq_of_lt (by omega)
    rw [h17]
    simpa using (merge_odd memory scratch 8).trans hmode
  have hzeroValue (sc : Nat → Nat) (hsc : sc 14 = 0) :
      merge memory sc (29 % 2 ^ (v + 1)) = 0 := by
    have h29 : 29 % 2 ^ (v + 1) = 29 := Nat.mod_eq_of_lt (by omega)
    rw [h29]
    simpa using (merge_odd memory sc 14).trans hsc
  have honeValue (sc : Nat → Nat) (hsc : sc 9 = 1) :
      merge memory sc (19 % 2 ^ (v + 1)) = 1 := by
    have h19 : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
    rw [h19]
    simpa using (merge_odd memory sc 9).trans hsc
  have hresultValue (sc : Nat → Nat) (value : Nat) (hsc : sc 5 = value) :
      merge memory sc (11 % 2 ^ (v + 1)) = value := by
    have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    rw [h11]
    simpa using (merge_odd memory sc 5).trans hsc
  have hset (sc : Nat → Nat) (value : Nat) (hvalue : value < 2 ^ (v + 1)) :
      setCell (v + 1) (merge memory sc) 11 value = merge memory (put sc 5 value) := by
    simpa [Nat.mod_eq_of_lt hvalue] using
      set_odd v memory sc 11 value (by decide) (by omega)
  have hzScratch := hzeroValue scratch hzero
  have hset2 := hset scratch 2 (by omega)
  have hrCopied := hresultValue copied 2 (by simp [copied])
  have honeCopied := honeValue copied (by simp [copied, put, hone])
  have hset1 := hset copied 1 (by omega)
  have hrOnce := hresultValue once 1 (by simp [once])
  have honeOnce := honeValue once (by simp [once, copied, put, hone])
  have hset0 := hset once 0 (by omega)
  have hrTwice := hresultValue twice 0 (by simp [twice])
  have hstep0 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc) memory scratch [] output) =
      some (state (preludeLength + blockLength * source.pc + 1)
        memory scratch [] output) := by
    simp [step, h0, Instr.effect, state, modeRegister, hmodeValue]
  have hstep1 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 1) memory scratch [] output) =
      some (state (preludeLength + blockLength * source.pc + 2)
        memory copied [] output) := by
    simp [step, h1, Instr.effect, state, RamVirtualCompiler.resultRegister,
      modeRegister, zeroRegister, hmodeValue, hzScratch, copied, put, hset2]
  have hstep2 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 2) memory copied [] output) =
      some (state (preludeLength + blockLength * source.pc + 3)
        memory once [] output) := by
    simp [step, h2, Instr.effect, state, RamVirtualCompiler.resultRegister,
      oneRegister, hrCopied, honeCopied, copied, once, put, hset1]
  have hstep3 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 3) memory once [] output) =
      some (state (preludeLength + blockLength * source.pc + 4)
        memory once [] output) := by
    simp [step, h3, Instr.effect, state, RamVirtualCompiler.resultRegister,
      hrOnce, once]
  have hstep4 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 4) memory once [] output) =
      some (state (preludeLength + blockLength * source.pc + 5)
        memory twice [] output) := by
    simp [step, h4, Instr.effect, state, RamVirtualCompiler.resultRegister,
      oneRegister, hrOnce, honeOnce, once, twice, put, hset0]
  have hstep5 : step (v + 1) (compile program)
      (state (preludeLength + blockLength * source.pc + 5) memory twice [] output) =
      some (state (preludeLength + blockLength * source.pc + 31)
        memory twice [] output) := by
    simp [step, h5, Instr.effect, state, RamVirtualCompiler.resultRegister,
      hrTwice, twice]
  have htwice : twice = put scratch 5 0 := by
    funext index
    simp [twice, once, copied, put]
  rw [← htwice]
  simp only [run, hstep0, hstep1, hstep2, hstep3, hstep4, hstep5,
    Option.bind_some]

/-- Every odd physical address used by the native-input buffer fits in the
one-bit-wider target machine.  For short inputs this follows from the fixed
64-word compiler capacity; for longer inputs it follows from the arena root
bound `6 * n < 2^v`. -/
theorem bufferPhysicalAddress_lt {v n index : Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * n < 2 ^ v)
    (hindex : index ≤ n) :
    2 * (bufferBase + index) + 1 < 2 ^ (v + 1) := by
  rw [Nat.pow_succ]
  simp only [bufferBase]
  by_cases hshort : n < 16
  · omega
  · omega

theorem run_read_natural_value {v : Nat} {program : Program}
    {source : State} {target consumed value : Nat} {values original : List Nat}
    {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hvalue : value < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hconsumed : consumed < original.length)
    (hdrop : original.drop consumed = value :: values)
    (hscratch : AdapterScratch v original consumed (value :: values).length 2 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (0 :: naturalTriples values ++ [0, 0, 0] ++
          pairSuffix original.length original.length) nextScratch ∧
      run (v + 1) (compile program) 20
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target value) nextScratch [] source.out) := by
  let dispatched := put scratch 5 0
  let loaded := put dispatched 5 value
  let advanced := put loaded 12 (2 * (bufferBase + (consumed + 1)) + 1)
  let phaseScratch := put advanced 8 3
  have hdispatch := run_read_mode_two_dispatch (memory := source.mem)
    (output := source.out) hcapacity hfetch hscratch.one_eq hscratch.zero_eq
      hscratch.mode_eq
  have h31 := compile_get_paddedBody program source.pc (.read target) hfetch 31
    (by simp [blockBodyLength])
  have h32 := compile_get_paddedBody program source.pc (.read target) hfetch 32
    (by simp [blockBodyLength])
  have h33 := compile_get_paddedBody program source.pc (.read target) hfetch 33
    (by simp [blockBodyLength])
  have h34 := compile_get_paddedBody program source.pc (.read target) hfetch 34
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h31 h32 h33 h34
  simp only [location] at h31 h32 h33 h34
  have hhead : original[consumed]'hconsumed = value := by
    have hcons := List.cons_getElem_drop_succ (l := original) (n := consumed)
      (h := hconsumed)
    rw [hdrop] at hcons
    simp only [List.cons.injEq] at hcons
    exact hcons.1
  have hbuffer : scratch (bufferBase + consumed) = value := by
    rw [hscratch.buffer consumed hconsumed, hhead]
  have hpointer : 2 * (bufferBase + consumed) + 1 < 2 ^ (v + 1) :=
    bufferPhysicalAddress_lt hcapacity hroot (Nat.le_of_lt hconsumed)
  have hnextPointer : 2 * (bufferBase + (consumed + 1)) + 1 < 2 ^ (v + 1) :=
    bufferPhysicalAddress_lt hcapacity hroot hconsumed
  have haddressCell : merge source.mem dispatched (25 % 2 ^ (v + 1)) =
      2 * (bufferBase + consumed) + 1 := by
    have h25 : 25 % 2 ^ (v + 1) = 25 := Nat.mod_eq_of_lt (by omega)
    rw [h25]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 12).trans (by
        simpa [dispatched, put] using hscratch.bufferAddress_eq)
  have hloadedValue : merge source.mem dispatched
      ((merge source.mem dispatched (25 % 2 ^ (v + 1))) % 2 ^ (v + 1)) = value := by
    rw [haddressCell, Nat.mod_eq_of_lt hpointer]
    have h5 : bufferBase + consumed ≠ 5 := by simp [bufferBase]; omega
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched (bufferBase + consumed)).trans (by
        simpa [dispatched, put, h5] using hbuffer)
  have hloadedValue' : merge source.mem dispatched
      ((2 * (bufferBase + consumed) + 1) % 2 ^ (v + 1)) = value := by
    rw [Nat.mod_eq_of_lt hpointer]
    have h5 : bufferBase + consumed ≠ 5 := by simp [bufferBase]; omega
    simpa [dispatched, put, h5] using
      (merge_odd source.mem dispatched (bufferBase + consumed)).trans (by
        simpa [dispatched, put, h5] using hbuffer)
  have hvaluePhysical : value < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsetLoaded := set_odd v source.mem dispatched 11 value (by decide) (by omega)
  have hsetLoaded' : setCell (v + 1) (merge source.mem dispatched) 11 value =
      merge source.mem loaded := by
    simpa [loaded, Nat.mod_eq_of_lt hvaluePhysical]
      using hsetLoaded
  have hpointerValue : merge source.mem loaded (25 % 2 ^ (v + 1)) =
      2 * (bufferBase + consumed) + 1 := by
    have h25 : 25 % 2 ^ (v + 1) = 25 := Nat.mod_eq_of_lt (by omega)
    rw [h25]
    simpa [loaded, dispatched, put] using
      (merge_odd source.mem loaded 12).trans (by
        simpa [loaded, dispatched, put] using hscratch.bufferAddress_eq)
  have htwoValue : merge source.mem loaded (3 % 2 ^ (v + 1)) = 2 := by
    have h3 : 3 % 2 ^ (v + 1) = 3 := Nat.mod_eq_of_lt (by omega)
    rw [h3]
    simpa [loaded, dispatched, put] using
      (merge_odd source.mem loaded 1).trans hscratch.compiler.2
  have hsetAdvanced := set_odd v source.mem loaded 25
    (2 * (bufferBase + (consumed + 1)) + 1) (by decide) (by omega)
  have hsetAdvanced' : setCell (v + 1) (merge source.mem loaded) 25
      (2 * (bufferBase + consumed) + 1 + 2) = merge source.mem advanced := by
    have hpointerAdd : 2 * (bufferBase + consumed) + 1 + 2 =
        2 * (bufferBase + (consumed + 1)) + 1 := by omega
    rw [hpointerAdd]
    simpa [advanced, Nat.mod_eq_of_lt hnextPointer] using hsetAdvanced
  have hsetMode := set_odd v source.mem advanced 17 3 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem advanced) 17 3 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 3 < 2 ^ (v + 1) by omega)]
      using hsetMode
  have hstep31 : step (v + 1) (compile program)
      (state (location source.pc + 31) source.mem dispatched [] source.out) =
      some (state (location source.pc + 32) source.mem loaded [] source.out) := by
    simp [step, h31, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      bufferAddressRegister, haddressCell, hloadedValue, hloadedValue', hsetLoaded']
  have hstep32 : step (v + 1) (compile program)
      (state (location source.pc + 32) source.mem loaded [] source.out) =
      some (state (location source.pc + 33) source.mem advanced [] source.out) := by
    simp [step, h32, Instr.effect, state, location, bufferAddressRegister,
      RamVirtualCompiler.twoRegister, hpointerValue, htwoValue, hsetAdvanced']
  have hstep33 : step (v + 1) (compile program)
      (state (location source.pc + 33) source.mem advanced [] source.out) =
      some (state (location source.pc + 34) source.mem phaseScratch [] source.out) := by
    simp [step, h33, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep34 : step (v + 1) (compile program)
      (state (location source.pc + 34) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h34, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 4
      (state (location source.pc + 31) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep31, hstep32, hstep33, hstep34]
  have hphase : AdapterScratch v original (consumed + 1)
      (value :: values).length 3
      phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v _
            (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega))
            5 value (by omega))
          12 (2 * (bufferBase + (consumed + 1)) + 1) (by omega))
        8 3 (by omega)
    · simp [phaseScratch, advanced, loaded, dispatched, put, hscratch.length_eq]
    · simp [phaseScratch, advanced, loaded, dispatched, put, hscratch.remaining_eq]
    · simp [phaseScratch]
    · simp [phaseScratch, advanced, loaded, dispatched, put, hscratch.one_eq]
    · simp [phaseScratch, advanced, loaded, dispatched, put, hscratch.three_eq]
    · simp [phaseScratch, advanced, loaded, dispatched, put, hscratch.six_eq]
    · simp [phaseScratch, advanced]
    · simp [phaseScratch, advanced, loaded, dispatched, put, hscratch.root_eq]
    · simp [phaseScratch, advanced, loaded, dispatched, put, hscratch.zero_eq]
    · intro index hindex
      have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
      have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
      have h12 : bufferBase + index ≠ 12 := by simp [bufferBase]; omega
      simp [BufferStored, phaseScratch, advanced, loaded, dispatched, put,
        h5, h8, h12]
      exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := value) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, advanced, loaded]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.naturalPadding consumed value values nextScratch hconsumed hdrop
      (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 20 = 6 + 4 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

/-- Entry offset of the mode-specific portion of the read adapter. -/
def readModeOffset : Nat → Nat
  | 1 => 24
  | 2 => 31
  | 3 => 35
  | 4 => 39
  | 5 => 42
  | 6 => 46
  | 7 => 50
  | _ => 16

set_option maxHeartbeats 1000000 in
/-- The common positive-mode dispatcher repeatedly decrements a temporary.
This single lemma avoids reproving the same two-instruction prefix for every
logical input phase. -/
theorem run_read_positive_mode_dispatch {v : Nat} {program : Program}
    {source : State} {target mode : Nat} {memory scratch : Nat → Nat}
    {output : List Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hone : scratch 9 = 1) (hzero : scratch 14 = 0)
    (hmode : scratch 8 = mode)
    (hpositive : 1 ≤ mode) (hbounded : mode ≤ 8) :
    run (v + 1) (compile program) (if mode = 8 then 16 else 2 * mode + 2)
      (state (location source.pc) memory scratch [] output) =
      some (state (location source.pc + readModeOffset mode) memory
        (put scratch 5 (if mode = 8 then 1 else 0)) [] output) := by
  have h0 := compile_get_paddedBody program source.pc (.read target) hfetch 0
    (by simp [blockBodyLength])
  have h1 := compile_get_paddedBody program source.pc (.read target) hfetch 1
    (by simp [blockBodyLength])
  have h2 := compile_get_paddedBody program source.pc (.read target) hfetch 2
    (by simp [blockBodyLength])
  have h3 := compile_get_paddedBody program source.pc (.read target) hfetch 3
    (by simp [blockBodyLength])
  have h4 := compile_get_paddedBody program source.pc (.read target) hfetch 4
    (by simp [blockBodyLength])
  have h5 := compile_get_paddedBody program source.pc (.read target) hfetch 5
    (by simp [blockBodyLength])
  have h6 := compile_get_paddedBody program source.pc (.read target) hfetch 6
    (by simp [blockBodyLength])
  have h7 := compile_get_paddedBody program source.pc (.read target) hfetch 7
    (by simp [blockBodyLength])
  have h8 := compile_get_paddedBody program source.pc (.read target) hfetch 8
    (by simp [blockBodyLength])
  have h9 := compile_get_paddedBody program source.pc (.read target) hfetch 9
    (by simp [blockBodyLength])
  have h10 := compile_get_paddedBody program source.pc (.read target) hfetch 10
    (by simp [blockBodyLength])
  have h11 := compile_get_paddedBody program source.pc (.read target) hfetch 11
    (by simp [blockBodyLength])
  have h12 := compile_get_paddedBody program source.pc (.read target) hfetch 12
    (by simp [blockBodyLength])
  have h13 := compile_get_paddedBody program source.pc (.read target) hfetch 13
    (by simp [blockBodyLength])
  have h14 := compile_get_paddedBody program source.pc (.read target) hfetch 14
    (by simp [blockBodyLength])
  have h15 := compile_get_paddedBody program source.pc (.read target) hfetch 15
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  simp only [location] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 ⊢
  have hcap17 : 17 < 2 ^ (v + 1) := by omega
  have hcap11 : 11 < 2 ^ (v + 1) := by omega
  have hcap19 : 19 < 2 ^ (v + 1) := by omega
  have hcap29 : 29 < 2 ^ (v + 1) := by omega
  have hmodeValue : merge memory scratch (17 % 2 ^ (v + 1)) = mode := by
    rw [Nat.mod_eq_of_lt hcap17]
    simpa using (merge_odd memory scratch 8).trans hmode
  have hmodeRaw : merge memory scratch 17 = mode := by
    simpa using (merge_odd memory scratch 8).trans hmode
  have honeRaw (sc : Nat → Nat) (hsc : sc 9 = 1) : merge memory sc 19 = 1 := by
    simpa using (merge_odd memory sc 9).trans hsc
  have hzeroRaw (sc : Nat → Nat) (hsc : sc 14 = 0) : merge memory sc 29 = 0 := by
    simpa using (merge_odd memory sc 14).trans hsc
  have hresultPut (sc : Nat → Nat) (word : Nat) :
      merge memory (put sc 5 word) 11 = word := by
    simpa [put] using merge_odd memory (put sc 5 word) 5
  have hset0 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 0 =
      merge memory (put sc 5 0) := by
    simpa using set_odd v memory sc 11 0 (by decide) (by omega)
  have hset1 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 1 =
      merge memory (put sc 5 1) := by
    simpa using set_odd v memory sc 11 1 (by decide) (by omega)
  have hset2 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 2 =
      merge memory (put sc 5 2) := by
    simpa [Nat.mod_eq_of_lt (show 2 < 2 ^ (v + 1) by omega)] using
      set_odd v memory sc 11 2 (by decide) (by omega)
  have hset3 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 3 =
      merge memory (put sc 5 3) := by
    simpa [Nat.mod_eq_of_lt (show 3 < 2 ^ (v + 1) by omega)] using
      set_odd v memory sc 11 3 (by decide) (by omega)
  have hset4 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 4 =
      merge memory (put sc 5 4) := by
    simpa [Nat.mod_eq_of_lt (show 4 < 2 ^ (v + 1) by omega)] using
      set_odd v memory sc 11 4 (by decide) (by omega)
  have hset5 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 5 =
      merge memory (put sc 5 5) := by
    simpa [Nat.mod_eq_of_lt (show 5 < 2 ^ (v + 1) by omega)] using
      set_odd v memory sc 11 5 (by decide) (by omega)
  have hset6 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 6 =
      merge memory (put sc 5 6) := by
    simpa [Nat.mod_eq_of_lt (show 6 < 2 ^ (v + 1) by omega)] using
      set_odd v memory sc 11 6 (by decide) (by omega)
  have hset7 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 7 =
      merge memory (put sc 5 7) := by
    simpa [Nat.mod_eq_of_lt (show 7 < 2 ^ (v + 1) by omega)] using
      set_odd v memory sc 11 7 (by decide) (by omega)
  have hset8 (sc : Nat → Nat) : setCell (v + 1) (merge memory sc) 11 8 =
      merge memory (put sc 5 8) := by
    simpa [Nat.mod_eq_of_lt (show 8 < 2 ^ (v + 1) by omega)] using
      set_odd v memory sc 11 8 (by decide) (by omega)
  have hmodes : mode = 1 ∨ mode = 2 ∨ mode = 3 ∨ mode = 4 ∨
      mode = 5 ∨ mode = 6 ∨ mode = 7 ∨ mode = 8 := by omega
  rcases hmodes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, Instr.effect, state, readModeOffset,
      RamVirtualCompiler.resultRegister, modeRegister, oneRegister, zeroRegister,
      hmodeValue, hmodeRaw, honeRaw, hzeroRaw, hset0, hset1, hset2, hset3,
      hset4, hset5, hset6, hset7, hset8, Nat.mod_eq_of_lt hcap17,
      Nat.mod_eq_of_lt hcap11, Nat.mod_eq_of_lt hcap19,
      Nat.mod_eq_of_lt hcap29, hresultPut, merge_odd, put, hone, hzero]

theorem run_read_natural_padding {v : Nat} {program : Program}
    {source : State} {target consumed value : Nat} {values original : List Nat}
    {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hconsumed : consumed < original.length)
    (hdrop : original.drop consumed = value :: values)
    (hscratch : AdapterScratch v original (consumed + 1)
      (value :: values).length 3 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (naturalTriples values ++ [0, 0, 0] ++
          pairSuffix original.length original.length) nextScratch ∧
      run (v + 1) (compile program) 22
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target 0) nextScratch [] source.out) := by
  let dispatched := put scratch 5 0
  let afterRemaining := put dispatched 7 values.length
  let phaseScratch := put afterRemaining 8 1
  have hdispatch := run_read_positive_mode_dispatch (mode := 3)
    (memory := source.mem) (output := source.out) hcapacity hfetch
    hscratch.one_eq hscratch.zero_eq hscratch.mode_eq (by omega) (by omega)
  simp [readModeOffset] at hdispatch
  have h35 := compile_get_paddedBody program source.pc (.read target) hfetch 35
    (by simp [blockBodyLength])
  have h36 := compile_get_paddedBody program source.pc (.read target) hfetch 36
    (by simp [blockBodyLength])
  have h37 := compile_get_paddedBody program source.pc (.read target) hfetch 37
    (by simp [blockBodyLength])
  have h38 := compile_get_paddedBody program source.pc (.read target) hfetch 38
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h35 h36 h37 h38
  simp only [location] at h35 h36 h37 h38
  have hremaining : merge source.mem dispatched (15 % 2 ^ (v + 1)) =
      values.length + 1 := by
    have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [h15]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 7).trans (by
        simpa [dispatched, put] using hscratch.remaining_eq)
  have hone : merge source.mem dispatched (19 % 2 ^ (v + 1)) = 1 := by
    have h19 : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
    rw [h19]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 9).trans (by
        simpa [dispatched, put] using hscratch.one_eq)
  have hsetRemaining := set_odd v source.mem dispatched 15 values.length
    (by decide) (by omega)
  have hsetRemaining' : setCell (v + 1) (merge source.mem dispatched) 15
      (values.length + 1 - 1) = merge source.mem afterRemaining := by
    have hvaluesBound : values.length < 2 ^ (v + 1) := by
      have hdropLength := congrArg List.length hdrop
      simp only [List.length_drop, List.length_cons] at hdropLength
      rw [Nat.pow_succ]
      omega
    simpa [afterRemaining, Nat.mod_eq_of_lt hvaluesBound] using hsetRemaining
  have hsetRemainingExact : setCell (v + 1) (merge source.mem dispatched) 15
      values.length = merge source.mem afterRemaining := by
    simpa using hsetRemaining'
  have hsetMode := set_odd v source.mem afterRemaining 17 1 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem afterRemaining) 17 1 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 1 < 2 ^ (v + 1) by omega)]
      using hsetMode
  have hstep35 : step (v + 1) (compile program)
      (state (location source.pc + 35) source.mem dispatched [] source.out) =
      some (state (location source.pc + 36) source.mem dispatched [] source.out) := by
    have hsetZero := set_odd v source.mem dispatched 11 0 (by decide) (by omega)
    simp [step, h35, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      hsetZero, dispatched, put]
  have hstep36 : step (v + 1) (compile program)
      (state (location source.pc + 36) source.mem dispatched [] source.out) =
      some (state (location source.pc + 37) source.mem afterRemaining [] source.out) := by
    simp [step, h36, Instr.effect, state, location, remainingRegister, oneRegister,
      hremaining, hone, hsetRemainingExact]
  have hstep37 : step (v + 1) (compile program)
      (state (location source.pc + 37) source.mem afterRemaining [] source.out) =
      some (state (location source.pc + 38) source.mem phaseScratch [] source.out) := by
    simp [step, h37, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep38 : step (v + 1) (compile program)
      (state (location source.pc + 38) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h38, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 4
      (state (location source.pc + 35) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep35, hstep36, hstep37, hstep38]
  have hphase : AdapterScratch v original (consumed + 1) values.length 1
      phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega))
          7 values.length (by omega))
        8 1 (by omega)
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.length_eq]
    · simp [phaseScratch, afterRemaining]
    · simp [phaseScratch]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.one_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.three_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.six_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put,
        hscratch.bufferAddress_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.root_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.zero_eq]
    · intro index hindex
      have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
      have h7 : bufferBase + index ≠ 7 := by simp [bufferBase]; omega
      have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
      simp [phaseScratch, afterRemaining, dispatched, put, h5, h7, h8]
      exact hscratch.buffer index hindex
  have hdropNext : original.drop (consumed + 1) = values := by
    rw [← List.drop_drop]
    simp [hdrop]
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 0) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, afterRemaining, dispatched]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.naturalTag (consumed + 1) values nextScratch (by omega)
      hdropNext (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 22 = (2 * 3 + 2) + 4 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

theorem run_read_nil_value {v : Nat} {program : Program} {source : State}
    {target : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hscratch : AdapterScratch v original original.length 0 4 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (0 :: pairSuffix original.length original.length) nextScratch ∧
      run (v + 1) (compile program) 23
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target 0) nextScratch [] source.out) := by
  let dispatched := put scratch 5 0
  let phaseScratch := put dispatched 8 5
  have hdispatch := run_read_positive_mode_dispatch (mode := 4)
    (memory := source.mem) (output := source.out) hcapacity hfetch
    hscratch.one_eq hscratch.zero_eq hscratch.mode_eq (by omega) (by omega)
  simp [readModeOffset] at hdispatch
  have h39 := compile_get_paddedBody program source.pc (.read target) hfetch 39
    (by simp [blockBodyLength])
  have h40 := compile_get_paddedBody program source.pc (.read target) hfetch 40
    (by simp [blockBodyLength])
  have h41 := compile_get_paddedBody program source.pc (.read target) hfetch 41
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h39 h40 h41
  simp only [location] at h39 h40 h41
  have hsetMode := set_odd v source.mem dispatched 17 5 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem dispatched) 17 5 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 5 < 2 ^ (v + 1) by omega)]
      using hsetMode
  have hstep39 : step (v + 1) (compile program)
      (state (location source.pc + 39) source.mem dispatched [] source.out) =
      some (state (location source.pc + 40) source.mem dispatched [] source.out) := by
    have hsetZero := set_odd v source.mem dispatched 11 0 (by decide) (by omega)
    simp [step, h39, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      hsetZero, dispatched, put]
  have hstep40 : step (v + 1) (compile program)
      (state (location source.pc + 40) source.mem dispatched [] source.out) =
      some (state (location source.pc + 41) source.mem phaseScratch [] source.out) := by
    simp [step, h40, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep41 : step (v + 1) (compile program)
      (state (location source.pc + 41) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h41, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 3
      (state (location source.pc + 39) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep39, hstep40, hstep41]
  have hphase : AdapterScratch v original original.length 0 5 phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega))
        8 5 (by omega)
    all_goals try simp [phaseScratch, dispatched, put, hscratch.length_eq,
      hscratch.remaining_eq, hscratch.one_eq, hscratch.three_eq,
      hscratch.six_eq, hscratch.bufferAddress_eq, hscratch.root_eq,
      hscratch.zero_eq]
    intro index hindex
    have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
    have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
    simp [phaseScratch, dispatched, put, h5, h8]
    exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 0) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, dispatched]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.nilPadding nextScratch (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 23 = (2 * 4 + 2) + 3 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

theorem run_read_nil_padding {v : Nat} {program : Program} {source : State}
    {target : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hscratch : AdapterScratch v original original.length 0 5 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (pairSuffix original.length original.length) nextScratch ∧
      run (v + 1) (compile program) 26
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target 0) nextScratch [] source.out) := by
  let dispatched := put scratch 5 0
  let afterRemaining := put dispatched 7 original.length
  let phaseScratch := put afterRemaining 8 6
  have hdispatch := run_read_positive_mode_dispatch (mode := 5)
    (memory := source.mem) (output := source.out) hcapacity hfetch
    hscratch.one_eq hscratch.zero_eq hscratch.mode_eq (by omega) (by omega)
  simp [readModeOffset] at hdispatch
  have h42 := compile_get_paddedBody program source.pc (.read target) hfetch 42
    (by simp [blockBodyLength])
  have h43 := compile_get_paddedBody program source.pc (.read target) hfetch 43
    (by simp [blockBodyLength])
  have h44 := compile_get_paddedBody program source.pc (.read target) hfetch 44
    (by simp [blockBodyLength])
  have h45 := compile_get_paddedBody program source.pc (.read target) hfetch 45
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h42 h43 h44 h45
  simp only [location] at h42 h43 h44 h45
  have hlengthPhysical : original.length < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsetRemaining := set_odd v source.mem dispatched 15 original.length
    (by decide) (by omega)
  have hsetRemaining' : setCell (v + 1) (merge source.mem dispatched) 15
      original.length = merge source.mem afterRemaining := by
    simpa [afterRemaining, Nat.mod_eq_of_lt hlengthPhysical] using hsetRemaining
  have hlengthValue : merge source.mem dispatched (13 % 2 ^ (v + 1)) =
      original.length := by
    have h13 : 13 % 2 ^ (v + 1) = 13 := Nat.mod_eq_of_lt (by omega)
    rw [h13]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 6).trans (by
        simpa [dispatched, put] using hscratch.length_eq)
  have hzeroValue : merge source.mem dispatched (29 % 2 ^ (v + 1)) = 0 := by
    have h29 : 29 % 2 ^ (v + 1) = 29 := Nat.mod_eq_of_lt (by omega)
    rw [h29]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 14).trans (by
        simpa [dispatched, put] using hscratch.zero_eq)
  have hsetMode := set_odd v source.mem afterRemaining 17 6 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem afterRemaining) 17 6 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 6 < 2 ^ (v + 1) by omega)]
      using hsetMode
  have hstep42 : step (v + 1) (compile program)
      (state (location source.pc + 42) source.mem dispatched [] source.out) =
      some (state (location source.pc + 43) source.mem dispatched [] source.out) := by
    have hsetZero := set_odd v source.mem dispatched 11 0 (by decide) (by omega)
    simp [step, h42, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      hsetZero, dispatched, put]
  have hstep43 : step (v + 1) (compile program)
      (state (location source.pc + 43) source.mem dispatched [] source.out) =
      some (state (location source.pc + 44) source.mem afterRemaining [] source.out) := by
    simp [step, h43, Instr.effect, state, location, remainingRegister,
      nativeLengthRegister, zeroRegister, hlengthValue, hzeroValue, hsetRemaining']
  have hstep44 : step (v + 1) (compile program)
      (state (location source.pc + 44) source.mem afterRemaining [] source.out) =
      some (state (location source.pc + 45) source.mem phaseScratch [] source.out) := by
    simp [step, h44, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep45 : step (v + 1) (compile program)
      (state (location source.pc + 45) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h45, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 4
      (state (location source.pc + 42) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep42, hstep43, hstep44, hstep45]
  have hphase : AdapterScratch v original original.length original.length 6
      phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega))
          7 original.length (by omega))
        8 6 (by omega)
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.length_eq]
    · simp [phaseScratch, afterRemaining]
    · simp [phaseScratch]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.one_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.three_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.six_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put,
        hscratch.bufferAddress_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.root_eq]
    · simp [phaseScratch, afterRemaining, dispatched, put, hscratch.zero_eq]
    · intro index hindex
      have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
      have h7 : bufferBase + index ≠ 7 := by simp [bufferBase]; omega
      have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
      simp [phaseScratch, afterRemaining, dispatched, put, h5, h7, h8]
      exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 0) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, afterRemaining, dispatched]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.pairTag original.length nextScratch (by omega)
      (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 26 = (2 * 5 + 2) + 4 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

theorem run_read_pair_tag_positive {v : Nat} {program : Program} {source : State}
    {target remaining : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hfetch : program[source.pc]? = some (.read target))
    (hpositive : 0 < remaining)
    (hremaining : remaining ≤ original.length)
    (hscratch : AdapterScratch v original original.length remaining 6 scratch) :
    ∃ nextScratch,
      InputRelation v original
        (3 * (remaining - 1) ::
          (6 * original.length - 3 * (remaining - 1) - 3) ::
          pairSuffix original.length (remaining - 1)) nextScratch ∧
      run (v + 1) (compile program) 28
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target 1) nextScratch [] source.out) := by
  let dispatched := put scratch 5 0
  let withResult := put dispatched 5 1
  let phaseScratch := put withResult 8 7
  have hdispatch := run_read_positive_mode_dispatch (mode := 6)
    (memory := source.mem) (output := source.out) hcapacity hfetch
    hscratch.one_eq hscratch.zero_eq hscratch.mode_eq (by omega) (by omega)
  simp [readModeOffset] at hdispatch
  have h46 := compile_get_paddedBody program source.pc (.read target) hfetch 46
    (by simp [blockBodyLength])
  have h47 := compile_get_paddedBody program source.pc (.read target) hfetch 47
    (by simp [blockBodyLength])
  have h48 := compile_get_paddedBody program source.pc (.read target) hfetch 48
    (by simp [blockBodyLength])
  have h49 := compile_get_paddedBody program source.pc (.read target) hfetch 49
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h46 h47 h48 h49
  simp only [location] at h46 h47 h48 h49
  have hremainingValue : merge source.mem dispatched (15 % 2 ^ (v + 1)) =
      remaining := by
    have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [h15]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 7).trans (by
        simpa [dispatched, put] using hscratch.remaining_eq)
  have hsetResult := set_odd v source.mem dispatched 11 1 (by decide) (by omega)
  have hsetResult' : setCell (v + 1) (merge source.mem dispatched) 11 1 =
      merge source.mem withResult := by
    simpa [withResult, Nat.mod_eq_of_lt (show 1 < 2 ^ (v + 1) by omega)]
      using hsetResult
  have hsetMode := set_odd v source.mem withResult 17 7 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem withResult) 17 7 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 7 < 2 ^ (v + 1) by omega)]
      using hsetMode
  have hstep46 : step (v + 1) (compile program)
      (state (location source.pc + 46) source.mem dispatched [] source.out) =
      some (state (location source.pc + 47) source.mem dispatched [] source.out) := by
    simp [step, h46, Instr.effect, state, location, remainingRegister,
      hremainingValue, Nat.ne_of_gt hpositive]
  have hstep47 : step (v + 1) (compile program)
      (state (location source.pc + 47) source.mem dispatched [] source.out) =
      some (state (location source.pc + 48) source.mem withResult [] source.out) := by
    simp [step, h47, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      hsetResult']
  have hstep48 : step (v + 1) (compile program)
      (state (location source.pc + 48) source.mem withResult [] source.out) =
      some (state (location source.pc + 49) source.mem phaseScratch [] source.out) := by
    simp [step, h48, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep49 : step (v + 1) (compile program)
      (state (location source.pc + 49) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h49, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 4
      (state (location source.pc + 46) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep46, hstep47, hstep48, hstep49]
  have hphase : AdapterScratch v original original.length remaining 7
      phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega))
          5 1 (by omega))
        8 7 (by omega)
    all_goals try simp [phaseScratch, withResult, dispatched, put,
      hscratch.length_eq, hscratch.remaining_eq, hscratch.one_eq,
      hscratch.three_eq, hscratch.six_eq, hscratch.bufferAddress_eq,
      hscratch.root_eq, hscratch.zero_eq]
    intro index hindex
    have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
    have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
    simp [phaseScratch, withResult, dispatched, put, h5, h8]
    exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 1) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, withResult]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.pairLeft remaining nextScratch hpositive hremaining
      (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 28 = (2 * 6 + 2) + 4 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

theorem run_read_pair_left {v : Nat} {program : Program} {source : State}
    {target remaining : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hpositive : 0 < remaining)
    (hremaining : remaining ≤ original.length)
    (hscratch : AdapterScratch v original original.length remaining 7 scratch) :
    ∃ nextScratch,
      InputRelation v original
        ((6 * original.length - 3 * (remaining - 1) - 3) ::
          pairSuffix original.length (remaining - 1)) nextScratch ∧
      run (v + 1) (compile program) 30
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target (3 * (remaining - 1)))
          nextScratch [] source.out) := by
  let dispatched := put scratch 5 0
  let afterSub := put dispatched 5 (remaining - 1)
  let afterMul := put afterSub 5 (3 * (remaining - 1))
  let phaseScratch := put afterMul 8 8
  have hdispatch := run_read_positive_mode_dispatch (mode := 7)
    (memory := source.mem) (output := source.out) hcapacity hfetch
    hscratch.one_eq hscratch.zero_eq hscratch.mode_eq (by omega) (by omega)
  simp [readModeOffset] at hdispatch
  have h50 := compile_get_paddedBody program source.pc (.read target) hfetch 50
    (by simp [blockBodyLength])
  have h51 := compile_get_paddedBody program source.pc (.read target) hfetch 51
    (by simp [blockBodyLength])
  have h52 := compile_get_paddedBody program source.pc (.read target) hfetch 52
    (by simp [blockBodyLength])
  have h53 := compile_get_paddedBody program source.pc (.read target) hfetch 53
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h50 h51 h52 h53
  simp only [location] at h50 h51 h52 h53
  have hremainingValue : merge source.mem dispatched (15 % 2 ^ (v + 1)) =
      remaining := by
    have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [h15]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 7).trans (by
        simpa [dispatched, put] using hscratch.remaining_eq)
  have honeValue : merge source.mem dispatched (19 % 2 ^ (v + 1)) = 1 := by
    have h19 : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
    rw [h19]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 9).trans (by
        simpa [dispatched, put] using hscratch.one_eq)
  have hsubPhysical : remaining - 1 < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hleftVirtual : 3 * (remaining - 1) < 2 ^ v := by omega
  have hleftPhysical : 3 * (remaining - 1) < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hleftPhysical' : (remaining - 1) * 3 < 2 ^ (v + 1) := by omega
  have hsetSub := set_odd v source.mem dispatched 11 (remaining - 1)
    (by decide) (by omega)
  have hsetSub' : setCell (v + 1) (merge source.mem dispatched) 11
      (remaining - 1) = merge source.mem afterSub := by
    simpa [afterSub, Nat.mod_eq_of_lt hsubPhysical] using hsetSub
  have hsubValue : merge source.mem afterSub (11 % 2 ^ (v + 1)) =
      remaining - 1 := by
    have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    rw [h11]
    simpa [afterSub] using merge_odd source.mem afterSub 5
  have hthreeValue : merge source.mem afterSub (21 % 2 ^ (v + 1)) = 3 := by
    have h21 : 21 % 2 ^ (v + 1) = 21 := Nat.mod_eq_of_lt (by omega)
    rw [h21]
    simpa [afterSub, dispatched, put] using
      (merge_odd source.mem afterSub 10).trans (by
        simpa [afterSub, dispatched, put] using hscratch.three_eq)
  have hsetMul := set_odd v source.mem afterSub 11 (3 * (remaining - 1))
    (by decide) (by omega)
  have hsetMul' : setCell (v + 1) (merge source.mem afterSub) 11
      ((remaining - 1) * 3) = merge source.mem afterMul := by
    simpa [afterMul, Nat.mod_eq_of_lt hleftPhysical', Nat.mul_comm] using hsetMul
  have hsetMode := set_odd v source.mem afterMul 17 8 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem afterMul) 17 8 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 8 < 2 ^ (v + 1) by omega)]
      using hsetMode
  have hstep50 : step (v + 1) (compile program)
      (state (location source.pc + 50) source.mem dispatched [] source.out) =
      some (state (location source.pc + 51) source.mem afterSub [] source.out) := by
    simp [step, h50, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      remainingRegister, oneRegister, hremainingValue, honeValue, hsetSub']
  have hstep51 : step (v + 1) (compile program)
      (state (location source.pc + 51) source.mem afterSub [] source.out) =
      some (state (location source.pc + 52) source.mem afterMul [] source.out) := by
    simp [step, h51, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      threeRegister, hsubValue, hthreeValue, hsetMul']
  have hstep52 : step (v + 1) (compile program)
      (state (location source.pc + 52) source.mem afterMul [] source.out) =
      some (state (location source.pc + 53) source.mem phaseScratch [] source.out) := by
    simp [step, h52, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep53 : step (v + 1) (compile program)
      (state (location source.pc + 53) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h53, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 4
      (state (location source.pc + 50) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep50, hstep51, hstep52, hstep53]
  have hphase : AdapterScratch v original original.length remaining 8
      phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v _
            (compilerScratch_put v scratch hscratch.compiler 5 0 (by omega))
            5 (remaining - 1) (by omega))
          5 (3 * (remaining - 1)) (by omega))
        8 8 (by omega)
    all_goals try simp [phaseScratch, afterMul, afterSub, dispatched, put,
      hscratch.length_eq, hscratch.remaining_eq, hscratch.one_eq,
      hscratch.three_eq, hscratch.six_eq, hscratch.bufferAddress_eq,
      hscratch.root_eq, hscratch.zero_eq]
    intro index hindex
    have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
    have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
    simp [phaseScratch, afterMul, afterSub, dispatched, put, h5, h8]
    exact hscratch.buffer index hindex
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := 3 * (remaining - 1)) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, afterMul]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.pairRight remaining nextScratch hpositive hremaining
      (hphase.preserve hsNext hpreserved), ?_⟩
  rw [show 30 = (2 * 7 + 2) + 4 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

theorem run_read_pair_right {v : Nat} {program : Program} {source : State}
    {target remaining : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hpositive : 0 < remaining)
    (hremaining : remaining ≤ original.length)
    (hscratch : AdapterScratch v original original.length remaining 8 scratch) :
    ∃ nextScratch,
      InputRelation v original (pairSuffix original.length (remaining - 1))
        nextScratch ∧
      run (v + 1) (compile program) 31
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target
            (6 * original.length - 3 * (remaining - 1) - 3))
          nextScratch [] source.out) := by
  let dispatched := put scratch 5 1
  let afterMul := put dispatched 5 (3 * remaining)
  let rightAddress := 6 * original.length - 3 * remaining
  let afterSub := put afterMul 5 rightAddress
  let afterRemaining := put afterSub 7 (remaining - 1)
  let phaseScratch := put afterRemaining 8 6
  have hdispatch := run_read_positive_mode_dispatch (mode := 8)
    (memory := source.mem) (output := source.out) hcapacity hfetch
    hscratch.one_eq hscratch.zero_eq hscratch.mode_eq (by omega) (by omega)
  simp [readModeOffset] at hdispatch
  have h16 := compile_get_paddedBody program source.pc (.read target) hfetch 16
    (by simp [blockBodyLength])
  have h17 := compile_get_paddedBody program source.pc (.read target) hfetch 17
    (by simp [blockBodyLength])
  have h18 := compile_get_paddedBody program source.pc (.read target) hfetch 18
    (by simp [blockBodyLength])
  have h19 := compile_get_paddedBody program source.pc (.read target) hfetch 19
    (by simp [blockBodyLength])
  have h20 := compile_get_paddedBody program source.pc (.read target) hfetch 20
    (by simp [blockBodyLength])
  simp [paddedBody, body, readBody] at h16 h17 h18 h19 h20
  simp only [location] at h16 h17 h18 h19 h20
  have hremainingValue : merge source.mem dispatched (15 % 2 ^ (v + 1)) =
      remaining := by
    have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [h15]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 7).trans (by
        simpa [dispatched, put] using hscratch.remaining_eq)
  have hthreeValue : merge source.mem dispatched (21 % 2 ^ (v + 1)) = 3 := by
    have h21 : 21 % 2 ^ (v + 1) = 21 := Nat.mod_eq_of_lt (by omega)
    rw [h21]
    simpa [dispatched, put] using
      (merge_odd source.mem dispatched 10).trans (by
        simpa [dispatched, put] using hscratch.three_eq)
  have hproductVirtual : 3 * remaining < 2 ^ v := by omega
  have hproductPhysical : remaining * 3 < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsetMul := set_odd v source.mem dispatched 11 (3 * remaining)
    (by decide) (by omega)
  have hsetMul' : setCell (v + 1) (merge source.mem dispatched) 11
      (remaining * 3) = merge source.mem afterMul := by
    simpa [afterMul, Nat.mod_eq_of_lt hproductPhysical, Nat.mul_comm] using hsetMul
  have hproductValue : merge source.mem afterMul (11 % 2 ^ (v + 1)) =
      3 * remaining := by
    have h11 : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    rw [h11]
    simpa [afterMul] using merge_odd source.mem afterMul 5
  have hrootValue : merge source.mem afterMul (27 % 2 ^ (v + 1)) =
      6 * original.length := by
    have h27 : 27 % 2 ^ (v + 1) = 27 := Nat.mod_eq_of_lt (by omega)
    rw [h27]
    simpa [afterMul, dispatched, put] using
      (merge_odd source.mem afterMul 13).trans (by
        simpa [afterMul, dispatched, put] using hscratch.root_eq)
  have hrightVirtual : rightAddress < 2 ^ v := by
    dsimp [rightAddress]
    omega
  have hrightPhysical : rightAddress < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsetSub := set_odd v source.mem afterMul 11 rightAddress
    (by decide) (by omega)
  have hsetSub' : setCell (v + 1) (merge source.mem afterMul) 11
      (6 * original.length - 3 * remaining) = merge source.mem afterSub := by
    simpa [afterSub, rightAddress, Nat.mod_eq_of_lt hrightPhysical] using hsetSub
  have hremainingPhysical : remaining - 1 < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsetRemaining := set_odd v source.mem afterSub 15 (remaining - 1)
    (by decide) (by omega)
  have hsetRemaining' : setCell (v + 1) (merge source.mem afterSub) 15
      (remaining - 1) = merge source.mem afterRemaining := by
    simpa [afterRemaining, Nat.mod_eq_of_lt hremainingPhysical] using hsetRemaining
  have hremainingAfterSub : merge source.mem afterSub (15 % 2 ^ (v + 1)) =
      remaining := by
    have h15 : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [h15]
    simpa [afterSub, afterMul, dispatched, put] using
      (merge_odd source.mem afterSub 7).trans (by
        simpa [afterSub, afterMul, dispatched, put] using hscratch.remaining_eq)
  have honeValue : merge source.mem afterSub (19 % 2 ^ (v + 1)) = 1 := by
    have h19' : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
    rw [h19']
    simpa [afterSub, afterMul, dispatched, put] using
      (merge_odd source.mem afterSub 9).trans (by
        simpa [afterSub, afterMul, dispatched, put] using hscratch.one_eq)
  have hsetMode := set_odd v source.mem afterRemaining 17 6 (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge source.mem afterRemaining) 17 6 =
      merge source.mem phaseScratch := by
    simpa [phaseScratch, Nat.mod_eq_of_lt (show 6 < 2 ^ (v + 1) by omega)]
      using hsetMode
  have hstep16 : step (v + 1) (compile program)
      (state (location source.pc + 16) source.mem dispatched [] source.out) =
      some (state (location source.pc + 17) source.mem afterMul [] source.out) := by
    simp [step, h16, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      remainingRegister, threeRegister, hremainingValue, hthreeValue, hsetMul']
  have hstep17 : step (v + 1) (compile program)
      (state (location source.pc + 17) source.mem afterMul [] source.out) =
      some (state (location source.pc + 18) source.mem afterSub [] source.out) := by
    simp [step, h17, Instr.effect, state, location, RamVirtualCompiler.resultRegister,
      rootRegister, hrootValue, hproductValue, hsetSub']
  have hstep18 : step (v + 1) (compile program)
      (state (location source.pc + 18) source.mem afterSub [] source.out) =
      some (state (location source.pc + 19) source.mem afterRemaining [] source.out) := by
    simp [step, h18, Instr.effect, state, location, remainingRegister, oneRegister,
      hremainingAfterSub, honeValue, hsetRemaining']
  have hstep19 : step (v + 1) (compile program)
      (state (location source.pc + 19) source.mem afterRemaining [] source.out) =
      some (state (location source.pc + 20) source.mem phaseScratch [] source.out) := by
    simp [step, h19, Instr.effect, state, location, modeRegister, hsetMode']
  have hstep20 : step (v + 1) (compile program)
      (state (location source.pc + 20) source.mem phaseScratch [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [step, h20, Instr.effect, state, location]
  have hcase : run (v + 1) (compile program) 5
      (state (location source.pc + 16) source.mem dispatched [] source.out) =
      some (state (location source.pc + 54) source.mem phaseScratch [] source.out) := by
    simp [run, hstep16, hstep17, hstep18, hstep19, hstep20]
  have hphase : AdapterScratch v original original.length (remaining - 1) 6
      phaseScratch := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v _
            (compilerScratch_put v _
              (compilerScratch_put v scratch hscratch.compiler 5 1 (by omega))
              5 (3 * remaining) (by omega))
            5 rightAddress (by omega))
          7 (remaining - 1) (by omega))
        8 6 (by omega)
    · simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        hscratch.length_eq]
    · simp [phaseScratch, afterRemaining]
    · simp [phaseScratch]
    · simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        hscratch.one_eq]
    · simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        hscratch.three_eq]
    · simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        hscratch.six_eq]
    · simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        hscratch.bufferAddress_eq]
    · simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        hscratch.root_eq]
    · simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        hscratch.zero_eq]
    · intro index hindex
      have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
      have h7 : bufferBase + index ≠ 7 := by simp [bufferBase]; omega
      have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
      simp [phaseScratch, afterRemaining, afterSub, afterMul, dispatched, put,
        h5, h7, h8]
      exact hscratch.buffer index hindex
  have haddressEq : rightAddress =
      6 * original.length - 3 * (remaining - 1) - 3 := by
    dsimp [rightAddress]
    omega
  rcases run_read_write_tail (program := program) (source := source)
      (target := target) (value := rightAddress) (memory := source.mem)
      (scratch := phaseScratch) (output := source.out) hcapacity hfetch
      hphase.compiler (by simp [phaseScratch, afterRemaining, afterSub]) with
    ⟨nextScratch, hsNext, hpreserved, htail⟩
  refine ⟨nextScratch,
    InputRelation.pairTag (remaining - 1) nextScratch (by omega)
      (hphase.preserve hsNext hpreserved), ?_⟩
  rw [haddressEq] at htail
  rw [show 31 = 16 + 5 + 10 by omega, run_add, run_add, hdispatch,
    Option.bind_some, hcase, Option.bind_some, htail]

/-- Every successful logical read of the generated arena stream is simulated
in at most 31 physical instructions. -/
theorem run_read_success {v : Nat} {program : Program} {source : State}
    {target value : Nat} {rest original : List Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hpayloads : ∀ word ∈ original, word < 2 ^ v)
    (hfetch : program[source.pc]? = some (.read target))
    (hrelation : InputRelation v original (value :: rest) scratch) :
    ∃ cost nextScratch,
      cost ≤ 31 ∧
      InputRelation v original rest nextScratch ∧
      run (v + 1) (compile program) cost
        (state (location source.pc) source.mem scratch [] source.out) =
        some (state (location source.pc + blockBodyLength)
          (setCell v source.mem target value) nextScratch [] source.out) := by
  generalize hinput : value :: rest = input at hrelation
  cases hrelation with
  | root scratch hscratch =>
      simp only [List.cons.injEq] at hinput
      rcases hinput with ⟨rfl, rfl⟩
      rcases run_read_root hcapacity hroot hfetch hscratch with
        ⟨nextScratch, hnext, hrun⟩
      exact ⟨14, nextScratch, by omega, hnext, hrun⟩
  | naturalTag consumed values scratch hconsumed hdrop hscratch =>
      cases values with
      | nil =>
          simp [naturalTriples] at hinput
          rcases hinput with ⟨rfl, rfl⟩
          rcases run_read_natural_tag_empty hcapacity hfetch hconsumed hdrop hscratch with
            ⟨nextScratch, hnext, hrun⟩
          exact ⟨18, nextScratch, by omega, hnext, by
            simpa [naturalTriples] using hrun⟩
      | cons head tail =>
          simp [naturalTriples] at hinput
          rcases hinput with ⟨rfl, rfl⟩
          have hdropLength := congrArg List.length hdrop
          simp only [List.length_drop, List.length_cons] at hdropLength
          have hstrict : consumed < original.length := by omega
          rcases run_read_natural_tag_nonempty hcapacity hfetch hstrict hdrop
              hscratch with ⟨nextScratch, hnext, hrun⟩
          exact ⟨18, nextScratch, by omega, by
            simpa only [List.append_assoc] using! hnext, by
            simpa [naturalTriples, List.append_assoc] using hrun⟩
  | naturalValue consumed head tail scratch hconsumed hdrop hscratch =>
      injection hinput with hvalueEq hrestEq
      subst value
      subst rest
      have hhead : original[consumed]'hconsumed = head := by
        have hcons := List.cons_getElem_drop_succ (l := original) (n := consumed)
          (h := hconsumed)
        rw [hdrop] at hcons
        simp only [List.cons.injEq] at hcons
        exact hcons.1
      have hheadBound : head < 2 ^ v := by
        rw [← hhead]
        exact hpayloads _ (List.getElem_mem hconsumed)
      rcases run_read_natural_value hcapacity hroot hheadBound hfetch hconsumed hdrop
          hscratch with ⟨nextScratch, hnext, hrun⟩
      exact ⟨20, nextScratch, by omega, hnext, hrun⟩
  | naturalPadding consumed head tail scratch hconsumed hdrop hscratch =>
      injection hinput with hvalueEq hrestEq
      subst value
      subst rest
      rcases run_read_natural_padding hcapacity hroot hfetch hconsumed hdrop hscratch with
        ⟨nextScratch, hnext, hrun⟩
      exact ⟨22, nextScratch, by omega, hnext, hrun⟩
  | nilValue scratch hscratch =>
      injection hinput with hvalueEq hrestEq
      subst value
      subst rest
      rcases run_read_nil_value hcapacity hfetch hscratch with
        ⟨nextScratch, hnext, hrun⟩
      exact ⟨23, nextScratch, by omega, hnext, hrun⟩
  | nilPadding scratch hscratch =>
      injection hinput with hvalueEq hrestEq
      subst value
      subst rest
      rcases run_read_nil_padding hcapacity hroot hfetch hscratch with
        ⟨nextScratch, hnext, hrun⟩
      exact ⟨26, nextScratch, by omega, hnext, hrun⟩
  | pairTag remaining scratch hremaining hscratch =>
      cases remaining with
      | zero => simp [pairSuffix] at *
      | succ count =>
          simp [pairSuffix] at hinput
          rcases hinput with ⟨rfl, rfl⟩
          have hpositive : 0 < count + 1 := by omega
          rcases run_read_pair_tag_positive hcapacity hfetch hpositive hremaining
              hscratch with ⟨nextScratch, hnext, hrun⟩
          exact ⟨28, nextScratch, by omega, hnext, by
            simpa [pairSuffix] using hrun⟩
  | pairLeft remaining scratch hpositive hremaining hscratch =>
      injection hinput with hvalueEq hrestEq
      subst value
      subst rest
      rcases run_read_pair_left hcapacity hroot hfetch hpositive hremaining hscratch with
        ⟨nextScratch, hnext, hrun⟩
      exact ⟨30, nextScratch, by omega, hnext, hrun⟩
  | pairRight remaining scratch hpositive hremaining hscratch =>
      injection hinput with hvalueEq hrestEq
      subst value
      subst rest
      rcases run_read_pair_right hcapacity hroot hfetch hpositive hremaining hscratch with
        ⟨nextScratch, hnext, hrun⟩
      exact ⟨31, nextScratch, by omega, hnext, hrun⟩

/-- One source instruction on the structural-arena tape is simulated by the
native-input program with a uniform constant overhead. -/
theorem simulation_step {v : Nat} {program : Program} {original : List Nat}
    {source next physical : State}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hpayloads : ∀ word ∈ original, word < 2 ^ v)
    (hsimulates : Simulates v original source physical)
    (hstep : step v program source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 66 ∧
      run (v + 1) (compile program) cost physical = some nextPhysical ∧
      Simulates v original next nextPhysical := by
  rcases hsimulates with
    ⟨scratch, logicalInput, hnormal, hsourceInput, hrelation, rfl⟩
  simp only [step] at hstep
  cases hfetch : program[source.pc]? with
  | none => simp [hfetch] at hstep
  | some instruction =>
      rw [hfetch] at hstep
      simp only [Option.bind_some] at hstep
      by_cases hnotRead : NotRead instruction
      · rcases run_paddedBody_of_notRead hcapacity hfetch hnotRead
          hrelation.compiler hnormal hstep with
          ⟨bodyScratch, hsBody, hready, hbodyHigh, hbody⟩
        have hnextInput : next.inp = source.inp := by
          cases instruction <;> simp [NotRead] at hnotRead
          all_goals simp only [Instr.effect] at hstep
          all_goals try { cases hstep; rfl }
          all_goals simp at hstep
        rcases run_branch hcapacity hfetch hready hstep with
          ⟨branchCost, hcostPositive, hbranchCost, hbranch⟩
        let nextPhysical := state (location next.pc) next.mem bodyScratch [] next.out
        refine ⟨blockBodyLength + branchCost, nextPhysical,
          by simp only [blockBodyLength]; omega, ?_, ?_⟩
        · rw [run_add, hbody, Option.bind_some, hbranch]
        · refine ⟨bodyScratch, logicalInput,
            RamVirtualSimulation.normalized_effect hnormal hstep, ?_, ?_, rfl⟩
          · rw [hnextInput, hsourceInput]
          · exact hrelation.preserve hsBody hbodyHigh
      · cases instruction with
        | read target =>
            subst logicalInput
            cases hsourceInput : source.inp with
            | nil => simp [Instr.effect, hsourceInput] at hstep
            | cons value rest =>
                rw [hsourceInput] at hrelation
                simp only [Instr.effect, hsourceInput, List.head?_cons, Option.map_some,
                  List.tail_cons] at hstep
                injection hstep with hnext
                subst next
                rcases run_read_success hcapacity hroot hpayloads hfetch hrelation with
                  ⟨bodyCost, nextScratch, hbodyCost, hnextRelation, hbody⟩
                have heffect : (Instr.read target).effect v source =
                    some (State.mk (source.pc + 1)
                      (setCell v source.mem target value) rest source.out) := by
                  simp [Instr.effect, hsourceInput]
                rcases run_branch hcapacity hfetch (by trivial) heffect with
                  ⟨branchCost, hcostPositive, hbranchCost, hbranch⟩
                let nextPhysical := state (location (source.pc + 1))
                  (setCell v source.mem target value) nextScratch [] source.out
                refine ⟨bodyCost + branchCost, nextPhysical, by omega, ?_, ?_⟩
                · rw [run_add, hbody, Option.bind_some, hbranch]
                · exact ⟨nextScratch, rest,
                    RamVirtualSimulation.normalized_effect hnormal heffect,
                    rfl, hnextRelation, rfl⟩
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

theorem simulation_run {v : Nat} {program : Program} {original : List Nat}
    {time : Nat} {source next physical : State}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * original.length < 2 ^ v)
    (hpayloads : ∀ word ∈ original, word < 2 ^ v)
    (hsimulates : Simulates v original source physical)
    (hrun : run v program time source = some next) :
    ∃ cost nextPhysical,
      cost ≤ 66 * time ∧
      run (v + 1) (compile program) cost physical = some nextPhysical ∧
      Simulates v original next nextPhysical := by
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
          rcases simulation_step hcapacity hroot hpayloads hsimulates hsourceStep with
            ⟨firstCost, intermediatePhysical, hfirstCost, hfirstRun,
              hfirstSimulates⟩
          rcases ih hfirstSimulates hrun with
            ⟨restCost, nextPhysical, hrestCost, hrestRun, hnextSimulates⟩
          refine ⟨firstCost + restCost, nextPhysical, by omega, ?_, hnextSimulates⟩
          rw [run_add, hfirstRun, Option.bind_some, hrestRun]

def BufferPrefix (values : List Nat) (count : Nat) (scratch : Nat → Nat) : Prop :=
  ∀ index, index < count →
    ∀ hindex : index < values.length,
      scratch (bufferBase + index) = values[index]'hindex

structure BufferingScratch (v : Nat) (values remaining : List Nat)
    (consumed : Nat) (scratch : Nat → Nat) : Prop where
  compiler : CompilerScratch v scratch
  consumed_le : consumed ≤ values.length
  length_eq : scratch 6 = values.length
  remaining_eq : scratch 7 = remaining.length
  one_eq : scratch 9 = 1
  three_eq : scratch 10 = 3
  six_eq : scratch 11 = 6
  bufferAddress_eq : scratch 12 = bufferPhysicalBase
  root_eq : scratch 13 = 6 * values.length
  zero_eq : scratch 14 = 0
  writeAddress_eq : scratch 2 = 2 * (bufferBase + consumed) + 1
  buffered : BufferPrefix values consumed scratch

theorem BufferPrefix.finish {values : List Nat} {scratch : Nat → Nat}
    (hprefix : BufferPrefix values values.length scratch) :
    BufferStored values scratch := by
  intro index hindex
  exact hprefix index hindex hindex

theorem run_buffering_start (v : Nat) (program : Program) (values : List Nat)
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * values.length < 2 ^ v) :
    ∃ scratch,
      BufferingScratch v values values 0 scratch ∧
      run (v + 1) (compile program) 13
        (initState (values.length :: values)) =
        some (state 13 (fun _ => 0) scratch values []) := by
  let s0 := put (put (fun _ => 0) 1 2) 0 (2 ^ v - 1)
  let s1 := put s0 9 1
  let s2 := put s1 10 3
  let s3 := put s2 11 6
  let s4 := put s3 14 0
  let s5 := put s4 12 bufferPhysicalBase
  let s6 := put s5 2 bufferPhysicalBase
  let s7 := put s6 6 values.length
  let s8 := put s7 13 (6 * values.length)
  let finalScratch := put s8 7 values.length
  let adapterInit : Program :=
    [.set oneRegister 1, .set threeRegister 3, .set sixRegister 6,
     .set zeroRegister 0, .set bufferAddressRegister bufferPhysicalBase,
     .set RamVirtualCompiler.addressRegister bufferPhysicalBase,
     .read nativeLengthRegister,
     .mul rootRegister nativeLengthRegister sixRegister,
     .add remainingRegister nativeLengthRegister zeroRegister]
  have hlength : values.length < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hrootPhysical : 6 * values.length < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hrootPhysical' : values.length * 6 < 2 ^ (v + 1) := by omega
  have hbufferBaseWord : bufferPhysicalBase < 2 ^ (v + 1) := by
    simp only [bufferPhysicalBase, bufferBase]
    omega
  have hexecute : execute (v + 1)
      (RamVirtualCompiler.prelude ++ adapterInit)
      (state 0 (fun _ => 0) (fun _ => 0) (values.length :: values) []) =
      some (state 13 (fun _ => 0) finalScratch values []) := by
    rw [execute_append,
      RamVirtualMacros.prelude_execute v 0 (fun _ => 0) (fun _ => 0)
        (values.length :: values) [] (by omega)]
    simp only [Option.bind_some]
    change execute (v + 1) adapterInit
      (state 4 (fun _ => 0) s0 (values.length :: values) []) = _
    rw [show adapterInit =
        [.set 19 1] ++ ([.set 21 3] ++ ([.set 23 6] ++ ([.set 29 0] ++
          ([.set 25 bufferPhysicalBase] ++ ([.set 5 bufferPhysicalBase] ++
            ([.read 13] ++ ([.mul 27 13 23] ++ [.add 15 13 29]))))))) by rfl,
      execute_append,
      setRegister_execute v 4 9 1 (fun _ => 0) s0
        (values.length :: values) [] (by omega),
      Nat.mod_eq_of_lt (show 1 < 2 ^ (v + 1) by omega), Option.bind_some,
      execute_append,
      setRegister_execute v 5 10 3 (fun _ => 0) s1
        (values.length :: values) [] (by omega),
      Nat.mod_eq_of_lt (show 3 < 2 ^ (v + 1) by omega), Option.bind_some,
      execute_append,
      setRegister_execute v 6 11 6 (fun _ => 0) s2
        (values.length :: values) [] (by omega),
      Nat.mod_eq_of_lt (show 6 < 2 ^ (v + 1) by omega), Option.bind_some,
      execute_append,
      setRegister_execute v 7 14 0 (fun _ => 0) s3
        (values.length :: values) [] (by omega), Nat.zero_mod, Option.bind_some,
      execute_append,
      setRegister_execute v 8 12 bufferPhysicalBase (fun _ => 0) s4
        (values.length :: values) [] (by omega),
      Nat.mod_eq_of_lt hbufferBaseWord, Option.bind_some,
      execute_append,
      setRegister_execute v 9 2 bufferPhysicalBase (fun _ => 0) s5
        (values.length :: values) [] (by omega),
      Nat.mod_eq_of_lt hbufferBaseWord, Option.bind_some,
      execute_append,
      readRegister_execute v 10 6 values.length values (fun _ => 0) s6 []
        (by omega), Nat.mod_eq_of_lt hlength, Option.bind_some,
      execute_append]
    have hmul : execute (v + 1) [.mul 27 13 23]
        (state 11 (fun _ => 0) s7 values []) =
        some (state 12 (fun _ => 0) s8 values []) := by
      rw [show [.mul 27 13 23] =
          [BinaryKind.instruction .mul 27 13 23] by rfl,
        binaryRegister_execute .mul v 11 13 6 11 (fun _ => 0) s7 values []
          (by omega) (by omega) (by omega)]
      change some (state 12 (fun _ => 0)
        (put s7 13 ((s7 6 * s7 11) % 2 ^ (v + 1))) values []) = _
      simp [s8, s7, s6, s5, s4, s3, s2, s1, s0, put,
        Nat.mod_eq_of_lt hrootPhysical', Nat.mul_comm]
    rw [hmul, Option.bind_some]
    have hadd : execute (v + 1) [.add 15 13 29]
        (state 12 (fun _ => 0) s8 values []) =
        some (state 13 (fun _ => 0) finalScratch values []) := by
      rw [show [.add 15 13 29] =
          [BinaryKind.instruction .add 15 13 29] by rfl,
        binaryRegister_execute .add v 12 7 6 14 (fun _ => 0) s8 values []
          (by omega) (by omega) (by omega)]
      change some (state 13 (fun _ => 0)
        (put s8 7 ((s8 6 + s8 14) % 2 ^ (v + 1))) values []) = _
      simp [finalScratch, s8, s7, s6, s5, s4, s3, s2, s1, s0, put,
        Nat.mod_eq_of_lt hlength]
    exact hadd
  refine ⟨finalScratch, ?_, ?_⟩
  · refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor <;> simp [finalScratch, s8, s7, s6, s5, s4, s3, s2,
        s1, s0, put]
    all_goals try simp [finalScratch, s8, s7, s6, s5, s4, s3, s2, s1, s0,
      bufferPhysicalBase, bufferBase, BufferPrefix, put]
  · let code := RamVirtualCompiler.prelude ++ adapterInit
    have hlinear : ∀ instruction ∈ code, StraightLine instruction := by
      intro instruction hinstruction
      simp [code, adapterInit, RamVirtualCompiler.prelude, StraightLine] at hinstruction
      rcases hinstruction with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> trivial
    have hfetchCode : ∀ k, k < code.length →
        (compile program)[(initState (values.length :: values)).pc + k]? = code[k]? := by
      intro k hk
      have hprelude : prelude = code ++
          [.jzero remainingRegister 19, .read RamVirtualCompiler.resultRegister,
           .store RamVirtualCompiler.addressRegister RamVirtualCompiler.resultRegister,
           .add RamVirtualCompiler.addressRegister RamVirtualCompiler.addressRegister
             RamVirtualCompiler.twoRegister,
           .sub remainingRegister remainingRegister oneRegister, .jump 13,
           .add remainingRegister nativeLengthRegister zeroRegister,
           .set modeRegister 0, .jump (location 0)] := by
        rfl
      simp [compile, hprelude, initState, List.getElem?_append, hk]
    rw [show 13 = code.length by rfl,
      run_eq_execute (v + 1) (compile program) code
        (initState (values.length :: values)) hlinear hfetchCode]
    have hinitial : initState (values.length :: values) =
        state 0 (fun _ => 0) (fun _ => 0) (values.length :: values) [] := by
      simp [initState, state]
      congr 1
      funext address
      simp [merge]
    rw [hinitial]
    exact hexecute

theorem run_buffer_iteration {v : Nat} {program : Program}
    {values rest : List Nat} {value consumed : Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * values.length < 2 ^ v)
    (hpayloads : ∀ word ∈ values, word < 2 ^ v)
    (hdrop : values.drop consumed = value :: rest)
    (hscratch : BufferingScratch v values (value :: rest) consumed scratch) :
    ∃ nextScratch,
      BufferingScratch v values rest (consumed + 1) nextScratch ∧
      run (v + 1) (compile program) 6
        (state 13 (fun _ => 0) scratch (value :: rest) []) =
        some (state 13 (fun _ => 0) nextScratch rest []) := by
  let afterRead := put scratch 5 value
  let afterStore := put afterRead (bufferBase + consumed) value
  let afterAddress := put afterStore 2 (2 * (bufferBase + (consumed + 1)) + 1)
  let nextScratch := put afterAddress 7 rest.length
  have hdropLength := congrArg List.length hdrop
  simp only [List.length_drop, List.length_cons] at hdropLength
  have hconsumed : consumed < values.length := by omega
  have hhead : values[consumed]'hconsumed = value := by
    have hcons := List.cons_getElem_drop_succ (l := values) (n := consumed)
      (h := hconsumed)
    rw [hdrop] at hcons
    simp only [List.cons.injEq] at hcons
    exact hcons.1
  have hvalueVirtual : value < 2 ^ v := by
    rw [← hhead]
    exact hpayloads _ (List.getElem_mem hconsumed)
  have hvaluePhysical : value < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hpointer := bufferPhysicalAddress_lt hcapacity hroot
    (Nat.le_of_lt hconsumed)
  have hnextPointer := bufferPhysicalAddress_lt hcapacity hroot
    (Nat.succ_le_iff.mpr hconsumed)
  have hbufferNe (index : Nat) (hindex : index < 16) :
      index ≠ bufferBase + consumed := by
    simp only [bufferBase]
    omega
  have h13 : (compile program)[13]? = some (.jzero remainingRegister 19) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have h14 : (compile program)[14]? = some (.read RamVirtualCompiler.resultRegister) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have h15 : (compile program)[15]? = some
      (.store RamVirtualCompiler.addressRegister RamVirtualCompiler.resultRegister) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have h16 : (compile program)[16]? = some
      (.add RamVirtualCompiler.addressRegister RamVirtualCompiler.addressRegister
        RamVirtualCompiler.twoRegister) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have h17 : (compile program)[17]? = some
      (.sub remainingRegister remainingRegister oneRegister) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have h18 : (compile program)[18]? = some (.jump 13) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have hremainingValue : merge (fun _ => 0) scratch (15 % 2 ^ (v + 1)) =
      rest.length + 1 := by
    have hword : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa using (merge_odd (fun _ => 0) scratch 7).trans hscratch.remaining_eq
  have hsetRead := set_odd v (fun _ => 0) scratch 11 value (by decide) (by omega)
  have hsetRead' : setCell (v + 1) (merge (fun _ => 0) scratch) 11 value =
      merge (fun _ => 0) afterRead := by
    simpa [afterRead, Nat.mod_eq_of_lt hvaluePhysical] using hsetRead
  have hwriteAddress : merge (fun _ => 0) afterRead (5 % 2 ^ (v + 1)) =
      2 * (bufferBase + consumed) + 1 := by
    have hword : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa [afterRead, put] using
      (merge_odd (fun _ => 0) afterRead 2).trans (by
        simpa [afterRead, put] using hscratch.writeAddress_eq)
  have hwriteValue : merge (fun _ => 0) afterRead (11 % 2 ^ (v + 1)) = value := by
    have hword : 11 % 2 ^ (v + 1) = 11 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa [afterRead] using merge_odd (fun _ => 0) afterRead 5
  have hsetStore := set_odd v (fun _ => 0) afterRead
    (2 * (bufferBase + consumed) + 1) value (by omega) hpointer
  have hsetStore' : setCell (v + 1) (merge (fun _ => 0) afterRead)
      (2 * (bufferBase + consumed) + 1) value =
      merge (fun _ => 0) afterStore := by
    simpa [afterStore, Nat.mod_eq_of_lt hvaluePhysical, Nat.add_div,
      Nat.mul_div_right] using hsetStore
  have haddressValue : merge (fun _ => 0) afterStore (5 % 2 ^ (v + 1)) =
      2 * (bufferBase + consumed) + 1 := by
    have hword : 5 % 2 ^ (v + 1) = 5 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa [afterStore, afterRead, put, hbufferNe 2 (by omega)] using
      (merge_odd (fun _ => 0) afterStore 2).trans (by
        simpa [afterStore, afterRead, put, hbufferNe 2 (by omega)] using
          hscratch.writeAddress_eq)
  have htwoValue : merge (fun _ => 0) afterStore (3 % 2 ^ (v + 1)) = 2 := by
    have hword : 3 % 2 ^ (v + 1) = 3 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa [afterStore, afterRead, put, hbufferNe 1 (by omega)] using
      (merge_odd (fun _ => 0) afterStore 1).trans (by
        simpa [afterStore, afterRead, put, hbufferNe 1 (by omega)] using
          hscratch.compiler.2)
  have hsetAddress := set_odd v (fun _ => 0) afterStore 5
    (2 * (bufferBase + (consumed + 1)) + 1) (by decide) (by omega)
  have hsetAddress' : setCell (v + 1) (merge (fun _ => 0) afterStore) 5
      (2 * (bufferBase + consumed) + 1 + 2) =
      merge (fun _ => 0) afterAddress := by
    have heq : 2 * (bufferBase + consumed) + 1 + 2 =
        2 * (bufferBase + (consumed + 1)) + 1 := by omega
    rw [heq]
    simpa [afterAddress, Nat.mod_eq_of_lt hnextPointer] using hsetAddress
  have hremainingAfter : merge (fun _ => 0) afterAddress
      (15 % 2 ^ (v + 1)) = rest.length + 1 := by
    have hword : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa [afterAddress, afterStore, afterRead, put, hbufferNe 7 (by omega)] using
      (merge_odd (fun _ => 0) afterAddress 7).trans (by
        simpa [afterAddress, afterStore, afterRead, put,
          hbufferNe 7 (by omega)] using
          hscratch.remaining_eq)
  have honeValue : merge (fun _ => 0) afterAddress
      (19 % 2 ^ (v + 1)) = 1 := by
    have hword : 19 % 2 ^ (v + 1) = 19 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa [afterAddress, afterStore, afterRead, put, hbufferNe 9 (by omega)] using
      (merge_odd (fun _ => 0) afterAddress 9).trans (by
        simpa [afterAddress, afterStore, afterRead, put,
          hbufferNe 9 (by omega)] using hscratch.one_eq)
  have hrestPhysical : rest.length < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have hsetRemaining := set_odd v (fun _ => 0) afterAddress 15 rest.length
    (by decide) (by omega)
  have hsetRemaining' : setCell (v + 1) (merge (fun _ => 0) afterAddress) 15
      rest.length = merge (fun _ => 0) nextScratch := by
    simpa [nextScratch, Nat.mod_eq_of_lt hrestPhysical] using hsetRemaining
  have hstep13 : step (v + 1) (compile program)
      (state 13 (fun _ => 0) scratch (value :: rest) []) =
      some (state 14 (fun _ => 0) scratch (value :: rest) []) := by
    simp [step, h13, Instr.effect, state, remainingRegister, hremainingValue]
  have hstep14 : step (v + 1) (compile program)
      (state 14 (fun _ => 0) scratch (value :: rest) []) =
      some (state 15 (fun _ => 0) afterRead rest []) := by
    simp [step, h14, Instr.effect, state, RamVirtualCompiler.resultRegister,
      hsetRead']
  have hstep15 : step (v + 1) (compile program)
      (state 15 (fun _ => 0) afterRead rest []) =
      some (state 16 (fun _ => 0) afterStore rest []) := by
    simp [step, h15, Instr.effect, state, RamVirtualCompiler.addressRegister,
      RamVirtualCompiler.resultRegister, hwriteAddress, hwriteValue, hsetStore']
  have hstep16 : step (v + 1) (compile program)
      (state 16 (fun _ => 0) afterStore rest []) =
      some (state 17 (fun _ => 0) afterAddress rest []) := by
    simp [step, h16, Instr.effect, state, RamVirtualCompiler.addressRegister,
      RamVirtualCompiler.twoRegister, haddressValue, htwoValue, hsetAddress']
  have hstep17 : step (v + 1) (compile program)
      (state 17 (fun _ => 0) afterAddress rest []) =
      some (state 18 (fun _ => 0) nextScratch rest []) := by
    simp [step, h17, Instr.effect, state, remainingRegister, oneRegister,
      hremainingAfter, honeValue, hsetRemaining']
  have hstep18 : step (v + 1) (compile program)
      (state 18 (fun _ => 0) nextScratch rest []) =
      some (state 13 (fun _ => 0) nextScratch rest []) := by
    simp [step, h18, Instr.effect, state]
  refine ⟨nextScratch, ?_, ?_⟩
  · refine ⟨?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v _
          (compilerScratch_put v _
            (compilerScratch_put v scratch hscratch.compiler 5 value (by omega))
            (bufferBase + consumed) value (by simp [bufferBase]; omega))
          2 (2 * (bufferBase + (consumed + 1)) + 1) (by omega))
        7 rest.length (by omega)
    all_goals try simp [nextScratch, afterAddress, afterStore, afterRead, put,
      hscratch.length_eq, hscratch.remaining_eq, hscratch.one_eq,
      hscratch.three_eq, hscratch.six_eq, hscratch.bufferAddress_eq,
      hscratch.root_eq, hscratch.zero_eq, hscratch.writeAddress_eq,
      hbufferNe 0 (by omega), hbufferNe 1 (by omega), hbufferNe 2 (by omega),
      hbufferNe 5 (by omega), hbufferNe 6 (by omega), hbufferNe 7 (by omega),
      hbufferNe 9 (by omega), hbufferNe 10 (by omega), hbufferNe 11 (by omega),
      hbufferNe 12 (by omega), hbufferNe 13 (by omega), hbufferNe 14 (by omega)]
    intro index hindex hindexValues
    by_cases heq : index = consumed
    · subst index
      simp [nextScratch, afterAddress, afterStore, afterRead, put, bufferBase,
        hhead, show 16 + consumed ≠ 7 by omega,
        show 16 + consumed ≠ 2 by omega]
    · have hlt : index < consumed := by omega
      have hold := hscratch.buffered index hlt hindexValues
      have hbufferNe : bufferBase + index ≠ bufferBase + consumed := by omega
      have h2 : bufferBase + index ≠ 2 := by simp [bufferBase]; omega
      have h5 : bufferBase + index ≠ 5 := by simp [bufferBase]; omega
      have h7 : bufferBase + index ≠ 7 := by simp [bufferBase]; omega
      simpa [nextScratch, afterAddress, afterStore, afterRead, put,
        hbufferNe, h2, h5, h7, heq] using hold
  · simp [run, hstep13, hstep14, hstep15, hstep16, hstep17, hstep18]

theorem run_buffer_loop {v : Nat} {program : Program}
    {values remaining : List Nat} {consumed : Nat} {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * values.length < 2 ^ v)
    (hpayloads : ∀ word ∈ values, word < 2 ^ v)
    (hdrop : values.drop consumed = remaining)
    (hscratch : BufferingScratch v values remaining consumed scratch) :
    ∃ finalScratch,
      BufferingScratch v values [] values.length finalScratch ∧
      run (v + 1) (compile program) (6 * remaining.length + 1)
        (state 13 (fun _ => 0) scratch remaining []) =
        some (state 19 (fun _ => 0) finalScratch [] []) := by
  induction remaining generalizing consumed scratch with
  | nil =>
      have hdropLength := congrArg List.length hdrop
      simp only [List.length_drop, List.length_nil] at hdropLength
      have hconsumedLe := hscratch.consumed_le
      have hconsumed : consumed = values.length := by omega
      subst consumed
      have h13 : (compile program)[13]? = some (.jzero remainingRegister 19) := by
        simp [compile, prelude, RamVirtualCompiler.prelude]
      have hremainingValue : merge (fun _ => 0) scratch
          (15 % 2 ^ (v + 1)) = 0 := by
        have hword : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
        rw [hword]
        simpa using (merge_odd (fun _ => 0) scratch 7).trans hscratch.remaining_eq
      refine ⟨scratch, hscratch, ?_⟩
      simp [run, step, h13, Instr.effect, state, remainingRegister,
        hremainingValue]
  | cons value rest ih =>
      rcases run_buffer_iteration hcapacity hroot hpayloads hdrop hscratch with
        ⟨nextScratch, hnextScratch, hiteration⟩
      have hdropNext : values.drop (consumed + 1) = rest := by
        rw [← List.drop_drop]
        simp [hdrop]
      rcases ih hdropNext hnextScratch with
        ⟨finalScratch, hfinalScratch, hrestRun⟩
      refine ⟨finalScratch, hfinalScratch, ?_⟩
      rw [show 6 * (value :: rest).length + 1 =
          6 + (6 * rest.length + 1) by simp; omega,
        run_add, hiteration, Option.bind_some, hrestRun]

theorem run_buffering_finish {v : Nat} {program : Program} {values : List Nat}
    {scratch : Nat → Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * values.length < 2 ^ v)
    (hscratch : BufferingScratch v values [] values.length scratch) :
    ∃ finalScratch,
      AdapterScratch v values 0 values.length 0 finalScratch ∧
      run (v + 1) (compile program) 3
        (state 19 (fun _ => 0) scratch [] []) =
        some (state (location 0) (fun _ => 0) finalScratch [] []) := by
  let afterRemaining := put scratch 7 values.length
  let finalScratch := put afterRemaining 8 0
  have hlengthPhysical : values.length < 2 ^ (v + 1) := by
    rw [Nat.pow_succ]
    omega
  have h19 : (compile program)[19]? = some
      (.add remainingRegister nativeLengthRegister zeroRegister) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have h20 : (compile program)[20]? = some (.set modeRegister 0) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have h21 : (compile program)[21]? = some (.jump (location 0)) := by
    simp [compile, prelude, RamVirtualCompiler.prelude]
  have hlengthValue : merge (fun _ => 0) scratch (13 % 2 ^ (v + 1)) =
      values.length := by
    have hword : 13 % 2 ^ (v + 1) = 13 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa using (merge_odd (fun _ => 0) scratch 6).trans hscratch.length_eq
  have hzeroValue : merge (fun _ => 0) scratch (29 % 2 ^ (v + 1)) = 0 := by
    have hword : 29 % 2 ^ (v + 1) = 29 := Nat.mod_eq_of_lt (by omega)
    rw [hword]
    simpa using (merge_odd (fun _ => 0) scratch 14).trans hscratch.zero_eq
  have hsetRemaining := set_odd v (fun _ => 0) scratch 15 values.length
    (by decide) (by omega)
  have hsetRemaining' : setCell (v + 1) (merge (fun _ => 0) scratch) 15
      values.length = merge (fun _ => 0) afterRemaining := by
    simpa [afterRemaining, Nat.mod_eq_of_lt hlengthPhysical] using hsetRemaining
  have hsetMode := set_odd v (fun _ => 0) afterRemaining 17 0
    (by decide) (by omega)
  have hsetMode' : setCell (v + 1) (merge (fun _ => 0) afterRemaining) 17 0 =
      merge (fun _ => 0) finalScratch := by
    simpa [finalScratch] using hsetMode
  have hstep19 : step (v + 1) (compile program)
      (state 19 (fun _ => 0) scratch [] []) =
      some (state 20 (fun _ => 0) afterRemaining [] []) := by
    simp [step, h19, Instr.effect, state, remainingRegister, nativeLengthRegister,
      zeroRegister, hlengthValue, hzeroValue, hsetRemaining']
  have hstep20 : step (v + 1) (compile program)
      (state 20 (fun _ => 0) afterRemaining [] []) =
      some (state 21 (fun _ => 0) finalScratch [] []) := by
    simp [step, h20, Instr.effect, state, modeRegister, hsetMode']
  have hstep21 : step (v + 1) (compile program)
      (state 21 (fun _ => 0) finalScratch [] []) =
      some (state (location 0) (fun _ => 0) finalScratch [] []) := by
    simp [step, h21, Instr.effect, state]
  refine ⟨finalScratch, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact compilerScratch_put v _
        (compilerScratch_put v scratch hscratch.compiler 7 values.length (by omega))
        8 0 (by omega)
    · simp [finalScratch, afterRemaining, put, hscratch.length_eq]
    · simp [finalScratch, afterRemaining]
    · simp [finalScratch]
    · simp [finalScratch, afterRemaining, put, hscratch.one_eq]
    · simp [finalScratch, afterRemaining, put, hscratch.three_eq]
    · simp [finalScratch, afterRemaining, put, hscratch.six_eq]
    · simp [finalScratch, afterRemaining, put, hscratch.bufferAddress_eq,
        bufferPhysicalBase, bufferBase]
    · simp [finalScratch, afterRemaining, put, hscratch.root_eq]
    · simp [finalScratch, afterRemaining, put, hscratch.zero_eq]
    · intro index hindex
      have hold := hscratch.buffered index hindex hindex
      have h7 : bufferBase + index ≠ 7 := by simp [bufferBase]; omega
      have h8 : bufferBase + index ≠ 8 := by simp [bufferBase]; omega
      simpa [finalScratch, afterRemaining, put, h7, h8] using hold
  · simp [run, hstep19, hstep20, hstep21]

theorem compile_start (v : Nat) (program : Program) (values : List Nat)
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * values.length < 2 ^ v)
    (hpayloads : ∀ word ∈ values, word < 2 ^ v) :
    ∃ physical,
      run (v + 1) (compile program) (17 + 6 * values.length)
        (initState (values.length :: values)) = some physical ∧
      Simulates v values
        (initState ((Lax560851.WordArena.encode
          (Lax560851.StructuralCombinators.list Lax560851.StructuralCombinators.nat)
          values).toInput)) physical := by
  rcases run_buffering_start v program values hcapacity hroot with
    ⟨startScratch, hstartScratch, hstart⟩
  rcases run_buffer_loop (program := program) hcapacity hroot hpayloads (by simp)
      hstartScratch with
    ⟨bufferedScratch, hbufferedScratch, hbuffered⟩
  rcases run_buffering_finish (program := program) hcapacity hroot
      hbufferedScratch with
    ⟨finalScratch, hfinalScratch, hfinish⟩
  let physical := state (location 0) (fun _ => 0) finalScratch [] []
  refine ⟨physical, ?_, ?_⟩
  · rw [show 17 + 6 * values.length =
        13 + (6 * values.length + 1) + 3 by omega,
      run_add, run_add, hstart, Option.bind_some, hbuffered,
      Option.bind_some, hfinish]
  · refine ⟨finalScratch,
      6 * values.length ::
        (naturalTriples values ++ [0, 0, 0] ++
          pairSuffix values.length values.length),
      RamVirtualSimulation.normalized_init v _, ?_, ?_, rfl⟩
    · rw [encode_list_input_exact, listArenaWords_flat]
      simp [initState]
    · exact InputRelation.root finalScratch hfinalScratch

theorem InputRelation.empty {v : Nat} {original : List Nat} {scratch : Nat → Nat}
    (hrelation : InputRelation v original [] scratch) :
    AdapterScratch v original original.length 0 6 scratch := by
  generalize hinput : ([] : List Nat) = input at hrelation
  cases hrelation with
  | root scratch hscratch => simp at hinput
  | naturalTag consumed values scratch hconsumed hdrop hscratch =>
      cases values <;> simp [naturalTriples] at hinput
  | naturalValue => simp at hinput
  | naturalPadding => simp at hinput
  | nilValue => simp at hinput
  | nilPadding => simp at hinput
  | pairTag remaining scratch hremaining hscratch =>
      cases remaining with
      | zero => simpa using hscratch
      | succ count => simp [pairSuffix] at hinput
  | pairLeft => simp at hinput
  | pairRight => simp at hinput

theorem simulation_halt {v : Nat} {program : Program} {original : List Nat}
    {source physical : State}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hsimulates : Simulates v original source physical)
    (hhalt : step v program source = none) :
    ∃ cost final,
      cost ≤ 64 ∧
      run (v + 1) (compile program) cost physical = some final ∧
      step (v + 1) (compile program) final = none ∧
      final.out = source.out := by
  rcases hsimulates with
    ⟨scratch, logicalInput, hnormal, hsourceInput, hrelation, rfl⟩
  simp only [step] at hhalt
  cases hfetch : program[source.pc]? with
  | none =>
      have hcompiled : (compile program)[location source.pc]? = none := by
        have hcompiledAtZero := compile_get program source.pc 0 (by
          simp [blockLength])
        simpa [hfetch] using hcompiledAtZero
      refine ⟨0, state (location source.pc) source.mem scratch [] source.out,
        by omega, by simp [run], ?_, rfl⟩
      simp [step, state, hcompiled]
  | some instruction =>
      rw [hfetch] at hhalt
      simp only [Option.bind_some] at hhalt
      cases instruction with
      | halt =>
          let padding := List.replicate blockBodyLength (Instr.set 5 0)
          have hpaddingDef : paddedBody program.length source.pc Instr.halt =
              padding := by rfl
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
          rcases padding_execute v blockBodyLength (location source.pc)
              source.mem scratch [] source.out (by omega) hrelation.compiler with
            ⟨nextScratch, hsNext, hfive, hpaddingHigh, hpadding⟩
          let final := state (location source.pc + blockBodyLength) source.mem
            nextScratch [] source.out
          have hrun : run (v + 1) (compile program) blockBodyLength
              (state (location source.pc) source.mem scratch [] source.out) =
              some final := by
            rw [show blockBodyLength = padding.length by simp [padding],
              run_eq_execute (v + 1) (compile program) padding
                (state (location source.pc) source.mem scratch [] source.out)
                hlinear hprefix]
            exact hpadding
          have hbranch := compile_get_branch program source.pc Instr.halt hfetch 0
            (by omega)
          simp [branch] at hbranch
          have hfinalHalt : step (v + 1) (compile program) final = none := by
            simp [step, final, hbranch, branch, Instr.effect, state]
          exact ⟨blockBodyLength, final, by simp [blockBodyLength], hrun,
            hfinalHalt, rfl⟩
      | read target =>
          have hsourceNil : source.inp = [] := by
            cases hinput : source.inp with
            | nil => rfl
            | cons value rest => simp [Instr.effect, hinput] at hhalt
          have hlogicalNil : logicalInput = [] := by
            rw [← hsourceInput, hsourceNil]
          rw [hlogicalNil] at hrelation
          have hscratch := hrelation.empty
          have hdispatch := run_read_positive_mode_dispatch (mode := 6)
            (program := program) (source := source) (target := target)
            (memory := source.mem) (output := source.out) hcapacity hfetch
            hscratch.one_eq hscratch.zero_eq hscratch.mode_eq (by omega) (by omega)
          simp [readModeOffset] at hdispatch
          let dispatched := put scratch 5 0
          have h46 := compile_get_paddedBody program source.pc (.read target) hfetch 46
            (by simp [blockBodyLength])
          simp [paddedBody, body, readBody] at h46
          simp only [location] at h46
          have hremaining : merge source.mem dispatched
              (15 % 2 ^ (v + 1)) = 0 := by
            have hword : 15 % 2 ^ (v + 1) = 15 := Nat.mod_eq_of_lt (by omega)
            rw [hword]
            simpa [dispatched, put] using
              (merge_odd source.mem dispatched 7).trans (by
                simpa [dispatched, put] using hscratch.remaining_eq)
          let final := State.mk (location program.length)
            (merge source.mem dispatched) [] source.out
          have hlast : step (v + 1) (compile program)
              (state (location source.pc + 46) source.mem dispatched [] source.out) =
              some final := by
            simp [step, h46, Instr.effect, state, location, remainingRegister,
              hremaining, final]
          have hlast' : step (v + 1) (compile program)
              (state (location source.pc + 46) source.mem (put scratch 5 0) []
                source.out) = some final := by
            simpa [dispatched] using hlast
          have hrun : run (v + 1) (compile program) 15
              (state (location source.pc) source.mem scratch [] source.out) =
              some final := by
            rw [show 15 = 14 + 1 by omega, run_add, hdispatch,
              Option.bind_some]
            simp [run, hlast']
          have houtside : (compile program)[location program.length]? = none := by
            rw [show location program.length = (compile program).length by simp]
            exact List.getElem?_eq_none (by omega)
          have hfinalHalt : step (v + 1) (compile program) final = none := by
            simp [step, final, houtside]
          exact ⟨15, final, by omega, hrun, hfinalHalt, rfl⟩
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

/-- Compile a computation reading the exact structural list arena into one
reading the native length-prefixed list. The target uses one additional bit;
startup is linear in the native list length and each simulated instruction
has constant overhead. -/
theorem runsTo_compile {v : Nat} {program : Program} {values output : List Nat}
    {time : Nat}
    (hcapacity : 64 ≤ 2 ^ (v + 1))
    (hroot : 6 * values.length < 2 ^ v)
    (hpayloads : ∀ word ∈ values, word < 2 ^ v)
    (hruns : RunsTo v program
      ((Lax560851.WordArena.encode
        (Lax560851.StructuralCombinators.list Lax560851.StructuralCombinators.nat)
        values).toInput) output time) :
    ∃ physicalTime ≤ 66 * time + 6 * values.length + 81,
      RunsTo (v + 1) (compile program) (values.length :: values) output
        physicalTime := by
  rcases hruns with ⟨sourceFinal, hsourceRun, hsourceHalt, houtput⟩
  rcases compile_start v program values hcapacity hroot hpayloads with
    ⟨physicalStart, hstart, hstartSimulates⟩
  rcases simulation_run hcapacity hroot hpayloads hstartSimulates hsourceRun with
    ⟨runCost, physicalFinal, hrunCost, hrun, hfinalSimulates⟩
  rcases simulation_halt hcapacity hfinalSimulates hsourceHalt with
    ⟨haltCost, final, hhaltCost, hhaltRun, hphysicalHalt, hfinalOutput⟩
  refine ⟨17 + 6 * values.length + runCost + haltCost, by omega,
    final, ?_, hphysicalHalt, ?_⟩
  · rw [show 17 + 6 * values.length + runCost + haltCost =
        (17 + 6 * values.length) + (runCost + haltCost) by omega,
      run_add, hstart, Option.bind_some, run_add, hrun, Option.bind_some,
      hhaltRun]
  · rw [hfinalOutput, houtput]

end Lax560851Proofs.RamNativeToArenaSimulation
