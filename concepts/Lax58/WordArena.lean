import Lax58.StructuralPresentation

/-!
---
title: Distinguished immutable word arenas
type: definition and theorem
---

Every universal structural value has a distinguished dense postorder arena
using three natural-number words per node. Natural leaves store a tag, payload,
and padding word; pairs store a tag and two addresses of previously stored
children. The root address is supplied as one additional word.

The explicit encoder determines every stored word. Density separately says
that it adds no unreachable auxiliary blocks. The semantic representation
relation, exact footprint, and explicit payload and address-space hypotheses
form the public interface. No whole-memory
decoder, uniqueness of arbitrary physical layouts, mutation semantics, or
operation-cost model is imposed.
-/

namespace Lax58.WordArena

open Lax58.StructuralPresentation

universe u

/-- A finite array of unbounded natural-number words. -/
abbrev WordMemory := Array Nat

/-- A closed word array together with its distinguished root address. -/
structure WordImage where
  memory : WordMemory
  root : Nat
  deriving DecidableEq

namespace WordImage

/-- Number of words in the memory array. -/
def memoryWords (I : WordImage) : Nat := I.memory.size

/-- Total supplied words, including the separately supplied root. -/
def totalWords (I : WordImage) : Nat := I.memoryWords + 1

/-- The actual input word list, with the root followed by the arena array. -/
def words (I : WordImage) : List Nat := I.root :: I.memory.toList

/-- The memory array fits in the address space of `w`-bit words. -/
def AddressSpaceFits (I : WordImage) (w : Nat) : Prop :=
  I.memoryWords ≤ 2 ^ w

/-- Every supplied word, including the root, fits in `w` bits. -/
def ValuesFitInWord (I : WordImage) (w : Nat) : Prop :=
  ∀ x ∈ I.words, x < 2 ^ w

/-- Both the address space and all supplied word values fit at width `w`. -/
def FitsInWord (I : WordImage) (w : Nat) : Prop :=
  I.AddressSpaceFits w ∧ I.ValuesFitInWord w

/-- The word at an in-bounds arena address. -/
def wordAt? (I : WordImage) (address : Nat) : Option Nat :=
  I.memory[address]?

/-- Start of a complete aligned three-word arena block. -/
def ValidAddress (I : WordImage) (address : Nat) : Prop :=
  address % 3 = 0 ∧ address + 2 < I.memoryWords

/-- Tag of a natural-payload block. -/
def natTag : Nat := 0

/-- Tag of a binary-pair block. -/
def pairTag : Nat := 1

/-- A block rooted at an address semantically represents a structural value. -/
inductive Represents (I : WordImage) : Nat → Raw → Prop where
  | nat {address payload : Nat}
      (address_valid : I.ValidAddress address)
      (tag : I.wordAt? address = some natTag)
      (value : I.wordAt? (address + 1) = some payload)
      (padding : I.wordAt? (address + 2) = some 0) :
      I.Represents address (.nat payload)
  | pair {address leftAddress rightAddress : Nat} {left right : Raw}
      (address_valid : I.ValidAddress address)
      (tag : I.wordAt? address = some pairTag)
      (left_reference : I.wordAt? (address + 1) = some leftAddress)
      (right_reference : I.wordAt? (address + 2) = some rightAddress)
      (left_value : I.Represents leftAddress left)
      (right_value : I.Represents rightAddress right) :
      I.Represents address (.pair left right)

/-- A pair block directly refers to one valid child block. -/
inductive ChildAddress (I : WordImage) : Nat → Nat → Prop where
  | left {parent child : Nat}
      (parent_valid : I.ValidAddress parent)
      (child_valid : I.ValidAddress child)
      (tag : I.wordAt? parent = some pairTag)
      (reference : I.wordAt? (parent + 1) = some child) :
      I.ChildAddress parent child
  | right {parent child : Nat}
      (parent_valid : I.ValidAddress parent)
      (child_valid : I.ValidAddress child)
      (tag : I.wordAt? parent = some pairTag)
      (reference : I.wordAt? (parent + 2) = some child) :
      I.ChildAddress parent child

/-- Addresses reachable from a chosen root by following child references. -/
inductive ReachableFrom (I : WordImage) (root : Nat) : Nat → Prop where
  | root : I.ReachableFrom root root
  | child {parent child : Nat}
      (parent_reachable : I.ReachableFrom root parent)
      (child_address : I.ChildAddress parent child) :
      I.ReachableFrom root child

/-- Every aligned block is meaningful and all child references are valid. -/
def BlocksWellFormed (I : WordImage) : Prop :=
  I.memoryWords % 3 = 0 ∧
    ∀ address, I.ValidAddress address → ∃ raw, I.Represents address raw

/-- Every block is valid and the distinguished root represents a value. -/
def RootedWellFormed (I : WordImage) : Prop :=
  I.BlocksWellFormed ∧ ∃ raw, I.Represents I.root raw

/-- Every complete block is reachable from the distinguished root. -/
def Dense (I : WordImage) : Prop :=
  ∀ address, I.ValidAddress address → I.ReachableFrom I.root address

end WordImage

/-- Append the postorder arena of a raw value and return its root address. -/
def encodeInto : Raw → WordMemory → WordMemory × Nat
  | .nat payload, memory =>
      let address := memory.size
      (memory.push WordImage.natTag |>.push payload |>.push 0, address)
  | .pair left right, memory =>
      let (memory, leftAddress) := encodeInto left memory
      let (memory, rightAddress) := encodeInto right memory
      let address := memory.size
      (memory.push WordImage.pairTag |>.push leftAddress |>.push rightAddress, address)

/-- Distinguished closed postorder arena of a structural value. -/
def encodeRaw (raw : Raw) : WordImage :=
  let (memory, root) := encodeInto raw #[]
  { memory, root }

/-- Distinguished arena of a value through a named structural presentation. -/
def encode {α : Type u} (P : Presentation α) (x : α) : WordImage :=
  encodeRaw (P.toRaw x)

axiom encodeRaw_represents (raw : Raw) :
  (encodeRaw raw).Represents (encodeRaw raw).root raw

axiom encodeRaw_wellFormed (raw : Raw) :
  (encodeRaw raw).RootedWellFormed

axiom encodeRaw_dense (raw : Raw) :
  (encodeRaw raw).Dense

axiom encodeRaw_memoryWords (raw : Raw) :
  (encodeRaw raw).memoryWords = 3 * raw.nodes

axiom encodeRaw_totalWords (raw : Raw) :
  (encodeRaw raw).totalWords = 3 * raw.nodes + 1

axiom encodeRaw_fits (raw : Raw) (w : Nat) :
  raw.PayloadsFitInWord w →
  3 * raw.nodes ≤ 2 ^ w →
  (encodeRaw raw).FitsInWord w

axiom encode_represents {α : Type u} (P : Presentation α) (x : α) :
  (encode P x).Represents (encode P x).root (P.toRaw x)

axiom encode_memoryWords {α : Type u} (P : Presentation α) (x : α) :
  (encode P x).memoryWords = 3 * P.structuralSize x

axiom encode_totalWords {α : Type u} (P : Presentation α) (x : α) :
  (encode P x).totalWords = 3 * P.structuralSize x + 1

axiom encode_fits {α : Type u} (P : Presentation α) (x : α) (w : Nat) :
  P.PayloadsFitInWord x w →
  3 * P.structuralSize x ≤ 2 ^ w →
  (encode P x).FitsInWord w

end Lax58.WordArena
