import Lax560851Proofs.RamVirtualSimulation

namespace Lax560851Proofs.RamNativeToArenaCompiler

open Lax759944Proofs.Legacy.Ram
open RamVirtualMemory RamVirtualCompiler

def nativeLengthRegister : Nat := 13
def remainingRegister : Nat := 15
def modeRegister : Nat := 17
def oneRegister : Nat := 19
def threeRegister : Nat := 21
def sixRegister : Nat := 23
def bufferAddressRegister : Nat := 25
def rootRegister : Nat := 27
def zeroRegister : Nat := 29

def bufferBase : Nat := 16
def bufferPhysicalBase : Nat := 2 * bufferBase + 1

abbrev blockBodyLength : Nat := 64
abbrev blockLength : Nat := 66
abbrev preludeLength : Nat := 22

def location (pc : Nat) : Nat := preludeLength + blockLength * pc

/-- Initialize the virtual-memory convention, consume the native length and
payload words, and buffer the payloads in protected odd-addressed cells. -/
def prelude : Program := RamVirtualCompiler.prelude ++
  [.set oneRegister 1,
   .set threeRegister 3,
   .set sixRegister 6,
   .set zeroRegister 0,
   .set bufferAddressRegister bufferPhysicalBase,
   .set addressRegister bufferPhysicalBase,
   .read nativeLengthRegister,
   .mul rootRegister nativeLengthRegister sixRegister,
   .add remainingRegister nativeLengthRegister zeroRegister,
   .jzero remainingRegister 19,
   .read resultRegister,
   .store addressRegister resultRegister,
   .add addressRegister addressRegister twoRegister,
   .sub remainingRegister remainingRegister oneRegister,
   .jump 13,
   .add remainingRegister nativeLengthRegister zeroRegister,
   .set modeRegister 0,
   .jump (location 0)]

/-- Generate one word of the exact structural-arena tape. Modes 0--8 are,
respectively, root; natural tag/value/padding; nil value/padding; and pair
tag/left/right. Mode 6 with a zero remaining-pair count is exhausted input. -/
def readBody (programLength pc target : Nat) : Program :=
  let base := location pc
  let common := base + 54
  [.jzero modeRegister (base + 21),
   .add resultRegister modeRegister zeroRegister,
   .sub resultRegister resultRegister oneRegister,
   .jzero resultRegister (base + 24),
   .sub resultRegister resultRegister oneRegister,
   .jzero resultRegister (base + 31),
   .sub resultRegister resultRegister oneRegister,
   .jzero resultRegister (base + 35),
   .sub resultRegister resultRegister oneRegister,
   .jzero resultRegister (base + 39),
   .sub resultRegister resultRegister oneRegister,
   .jzero resultRegister (base + 42),
   .sub resultRegister resultRegister oneRegister,
   .jzero resultRegister (base + 46),
   .sub resultRegister resultRegister oneRegister,
   .jzero resultRegister (base + 50),
   -- mode 8: pair right address `6*n - 3*remaining`
   .mul resultRegister remainingRegister threeRegister,
   .sub resultRegister rootRegister resultRegister,
   .sub remainingRegister remainingRegister oneRegister,
   .set modeRegister 6,
   .jump common,
   -- mode 0: root
   .add resultRegister rootRegister zeroRegister,
   .set modeRegister 1,
   .jump common,
   -- mode 1: natural tag, or nil tag once payloads are exhausted
   .jzero remainingRegister (base + 28),
   .set resultRegister 0,
   .set modeRegister 2,
   .jump common,
   -- nil tag
   .set resultRegister 0,
   .set modeRegister 4,
   .jump common,
   -- mode 2: buffered payload
   .load resultRegister bufferAddressRegister,
   .add bufferAddressRegister bufferAddressRegister twoRegister,
   .set modeRegister 3,
   .jump common,
   -- mode 3: natural padding
   .set resultRegister 0,
   .sub remainingRegister remainingRegister oneRegister,
   .set modeRegister 1,
   .jump common,
   -- mode 4: nil payload
   .set resultRegister 0,
   .set modeRegister 5,
   .jump common,
   -- mode 5: nil padding and transition to pairs
   .set resultRegister 0,
   .add remainingRegister nativeLengthRegister zeroRegister,
   .set modeRegister 6,
   .jump common,
   -- mode 6: pair tag, or logical exhaustion
   .jzero remainingRegister (location programLength),
   .set resultRegister 1,
   .set modeRegister 7,
   .jump common,
   -- mode 7: pair left address `3*(remaining-1)`
   .sub resultRegister remainingRegister oneRegister,
   .mul resultRegister resultRegister threeRegister,
   .set modeRegister 8,
   .jump common] ++
    writeCell target ++ List.replicate 5 (.set 5 0)

def body (programLength pc : Nat) : Instr → Program
  | .read target => readBody programLength pc target
  | instruction => RamVirtualCompiler.body instruction

def NotRead : Instr → Prop
  | .read _ => False
  | _ => True

theorem body_eq_of_notRead (programLength pc : Nat) (instruction : Instr)
    (hnotRead : NotRead instruction) :
    body programLength pc instruction = RamVirtualCompiler.body instruction := by
  cases instruction <;> simp [NotRead, body] at hnotRead ⊢

theorem body_length_le (programLength pc : Nat) (instruction : Instr) :
    (body programLength pc instruction).length ≤ blockBodyLength := by
  cases instruction <;> simp [body, readBody, blockBodyLength,
    RamVirtualCompiler.body, RamVirtualCompiler.readCell,
    RamVirtualCompiler.writeCell]

def paddedBody (programLength pc : Nat) (instruction : Instr) : Program :=
  body programLength pc instruction ++
    List.replicate (blockBodyLength - (body programLength pc instruction).length)
      (.set 5 0)

@[simp] theorem paddedBody_length (programLength pc : Nat) (instruction : Instr) :
    (paddedBody programLength pc instruction).length = blockBodyLength := by
  simp only [paddedBody, List.length_append, List.length_replicate]
  have := body_length_le programLength pc instruction
  omega

def branch (pc : Nat) : Instr → Program
  | .halt => [.halt, .halt]
  | .jump target => [.jump (location target), .halt]
  | .jzero _ target => [.jzero resultRegister (location target),
      .jump (location (pc + 1))]
  | _ => [.jump (location (pc + 1)), .halt]

def block (programLength pc : Nat) (instruction : Instr) : Program :=
  paddedBody programLength pc instruction ++ branch pc instruction

def blocks (programLength pc : Nat) : Program → Program
  | [] => []
  | instruction :: rest =>
      block programLength pc instruction ++ blocks programLength (pc + 1) rest

def compile (program : Program) : Program :=
  prelude ++ blocks program.length 0 program

@[simp] theorem prelude_length : prelude.length = preludeLength := by rfl

@[simp] theorem branch_length (pc : Nat) (instruction : Instr) :
    (branch pc instruction).length = 2 := by cases instruction <;> rfl

@[simp] theorem block_length (programLength pc : Nat) (instruction : Instr) :
    (block programLength pc instruction).length = blockLength := by
  simp [block, blockLength, blockBodyLength]

@[simp] theorem blocks_length (programLength pc : Nat) (program : Program) :
    (blocks programLength pc program).length = blockLength * program.length := by
  induction program generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [blocks, List.length_append, block_length, ih, List.length_cons]
      simp only [blockLength]
      omega

@[simp] theorem compile_length (program : Program) :
    (compile program).length = location program.length := by
  simp [compile, location]

theorem blocks_get (program : Program) (programLength base pc offset : Nat)
    (hoffset : offset < blockLength) :
    (blocks programLength base program)[blockLength * pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block programLength (base + pc) instruction)[offset]?) := by
  induction program generalizing base pc with
  | nil => simp [blocks]
  | cons instruction rest ih =>
      cases pc with
      | zero => simp [blocks, List.getElem?_append, hoffset]
      | succ pc =>
          have hlarge : ¬blockLength * (pc + 1) + offset < blockLength := by
            simp only [blockLength]
            omega
          simp only [blocks, List.getElem?_append, block_length, hlarge,
            ↓reduceIte, List.getElem?_cons_succ]
          rw [show blockLength * (pc + 1) + offset - blockLength =
              blockLength * pc + offset by simp only [blockLength]; omega,
            ih]
          simp [Nat.add_comm, Nat.add_left_comm]

theorem compile_get (program : Program) (pc offset : Nat)
    (hoffset : offset < blockLength) :
    (compile program)[location pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block program.length pc instruction)[offset]?) := by
  have hlarge : ¬location pc + offset < prelude.length := by
    simp [location]
    omega
  simp only [compile, List.getElem?_append, hlarge, ↓reduceIte]
  have hsub : location pc + offset - prelude.length = blockLength * pc + offset := by
    simp [location]
    omega
  rw [hsub, blocks_get program program.length 0 pc offset hoffset, Nat.zero_add]

theorem compile_get_paddedBody (program : Program) (pc : Nat)
    (instruction : Instr) (hfetch : program[pc]? = some instruction)
    (offset : Nat) (hoffset : offset < blockBodyLength) :
    (compile program)[location pc + offset]? =
      (paddedBody program.length pc instruction)[offset]? := by
  rw [compile_get program pc offset (by
      simp only [blockBodyLength, blockLength] at hoffset ⊢
      omega), hfetch]
  simp [block, List.getElem?_append, hoffset]

theorem compile_get_branch (program : Program) (pc : Nat) (instruction : Instr)
    (hfetch : program[pc]? = some instruction) (offset : Nat)
    (hoffset : offset < 2) :
    (compile program)[location pc + blockBodyLength + offset]? =
      (branch pc instruction)[offset]? := by
  rw [show location pc + blockBodyLength + offset =
      location pc + (blockBodyLength + offset) by omega,
    compile_get program pc (blockBodyLength + offset) (by
      simp only [blockBodyLength, blockLength] at hoffset ⊢
      omega), hfetch]
  simp [block, List.getElem?_append, hoffset]

end Lax560851Proofs.RamNativeToArenaCompiler
