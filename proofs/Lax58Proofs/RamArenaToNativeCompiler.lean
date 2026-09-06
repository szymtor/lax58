import Lax58Proofs.RamVirtualSimulation

namespace Lax58Proofs.RamArenaToNativeCompiler

open Lax13.Ram
open RamVirtualCompiler

def nativeLengthRegister : Nat := 13
def remainingRegister : Nat := 15
def sixRegister : Nat := 17
def oneRegister : Nat := 19
def firstRegister : Nat := 21

/-- Initialize the virtual compiler and consume the arena root. For a list of
length `n`, the root is `6*n`; the adapter retains both `n` and `n+1`, the
number of words on the corresponding native logical tape. -/
def prelude : Program := RamVirtualCompiler.prelude ++
  [.set sixRegister 6, .read nativeLengthRegister,
   .div nativeLengthRegister nativeLengthRegister sixRegister,
   .set oneRegister 1, .add remainingRegister nativeLengthRegister oneRegister,
   .set firstRegister 1]

def location (pc : Nat) : Nat := 10 + 18 * pc

/-- Read one word of the logical tape `n :: xs` from the physical arena.
The first request returns the retained `n`; every later request skips the tag
and padding around one natural payload. A request past `xs` jumps outside the
compiled program and therefore halts. -/
def readBody (programLength pc target : Nat) : Program :=
  [.jzero remainingRegister (location programLength),
   .jzero firstRegister (location pc + 6),
   .set addressRegister nativeLengthRegister,
   .load resultRegister addressRegister,
   .set firstRegister 0,
   .jump (location pc + 9),
   .read addressRegister,
   .read resultRegister,
   .read addressRegister,
   .sub remainingRegister remainingRegister oneRegister] ++
    writeCell target

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
    (body programLength pc instruction).length ≤ 16 := by
  cases instruction <;> simp [body, readBody, RamVirtualCompiler.body,
    RamVirtualCompiler.readCell, RamVirtualCompiler.writeCell]

def paddedBody (programLength pc : Nat) (instruction : Instr) : Program :=
  body programLength pc instruction ++
    List.replicate (16 - (body programLength pc instruction).length) (.set 5 0)

theorem paddedBody_eq_of_notRead (programLength pc : Nat) (instruction : Instr)
    (hnotRead : NotRead instruction) :
    paddedBody programLength pc instruction = RamVirtualCompiler.paddedBody instruction := by
  simp [paddedBody, RamVirtualCompiler.paddedBody,
    body_eq_of_notRead programLength pc instruction hnotRead]

@[simp] theorem paddedBody_length (programLength pc : Nat) (instruction : Instr) :
    (paddedBody programLength pc instruction).length = 16 := by
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

@[simp] theorem prelude_length : prelude.length = 10 := by rfl

@[simp] theorem branch_length (pc : Nat) (instruction : Instr) :
    (branch pc instruction).length = 2 := by
  cases instruction <;> rfl

@[simp] theorem block_length (programLength pc : Nat) (instruction : Instr) :
    (block programLength pc instruction).length = 18 := by
  simp [block]

@[simp] theorem blocks_length (programLength pc : Nat) (program : Program) :
    (blocks programLength pc program).length = 18 * program.length := by
  induction program generalizing pc with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [blocks, List.length_append, block_length, ih, List.length_cons]
      omega

@[simp] theorem compile_length (program : Program) :
    (compile program).length = location program.length := by
  simp [compile, location]

theorem blocks_get (program : Program) (programLength base pc offset : Nat)
    (hoffset : offset < 18) :
    (blocks programLength base program)[18 * pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block programLength (base + pc) instruction)[offset]?) := by
  induction program generalizing base pc with
  | nil => simp [blocks]
  | cons instruction rest ih =>
      cases pc with
      | zero => simp [blocks, List.getElem?_append, hoffset]
      | succ pc =>
          have hlarge : ¬18 * (pc + 1) + offset < 18 := by omega
          simp only [blocks, List.getElem?_append, block_length, hlarge,
            ↓reduceIte, List.getElem?_cons_succ]
          rw [show 18 * (pc + 1) + offset - 18 = 18 * pc + offset by omega, ih]
          simp [Nat.add_comm, Nat.add_left_comm]

theorem compile_get (program : Program) (pc offset : Nat) (hoffset : offset < 18) :
    (compile program)[location pc + offset]? =
      program[pc]?.bind (fun instruction =>
        (block program.length pc instruction)[offset]?) := by
  have hlarge : ¬location pc + offset < prelude.length := by
    simp [location]
    omega
  simp only [compile, List.getElem?_append, hlarge, ↓reduceIte]
  have hsub : location pc + offset - prelude.length = 18 * pc + offset := by
    simp [location]
    omega
  rw [hsub, blocks_get program program.length 0 pc offset hoffset, Nat.zero_add]

theorem compile_get_paddedBody (program : Program) (pc : Nat) (instruction : Instr)
    (hfetch : program[pc]? = some instruction) (offset : Nat) (hoffset : offset < 16) :
    (compile program)[location pc + offset]? =
      (paddedBody program.length pc instruction)[offset]? := by
  rw [compile_get program pc offset (by omega), hfetch]
  simp [block, List.getElem?_append, hoffset]

theorem compile_get_branch (program : Program) (pc : Nat) (instruction : Instr)
    (hfetch : program[pc]? = some instruction) (offset : Nat) (hoffset : offset < 2) :
    (compile program)[location pc + 16 + offset]? = (branch pc instruction)[offset]? := by
  rw [show location pc + 16 + offset = location pc + (16 + offset) by omega,
    compile_get program pc (16 + offset) (by omega), hfetch]
  simp [block, List.getElem?_append, hoffset]

end Lax58Proofs.RamArenaToNativeCompiler
