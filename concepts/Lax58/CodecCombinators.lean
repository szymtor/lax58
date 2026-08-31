import Mathlib.Data.Vector.Basic
import Lax58.PrimitiveCodecs

/-!
---
title: Combinators for canonical codecs
type: definition
---

Canonical codecs compose along the usual finitary type constructors. Products
are encoded by concatenation. Sums and optional values use a one-bit constructor
tag. Lists use a one-bit nil/cons tag at each step. Fixed-length vectors and
functions on `Fin n` use the list encoding with the length checked by the
parser. Finite indices use the natural-number encoding with a range check.

These constructions preserve lawfulness, so their structural size functions
give exact encoding lengths. Under the standard `Primcodable` presentations,
they also preserve effectiveness.
-/

namespace Lax58.CodecCombinators

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.PrimitiveCodecs

universe u v

/-- Transport a codec across an equivalence. -/
def equivCodec {α : Type u} {β : Type v} (e : α ≃ β) (C : Codec β) : Codec α where
  encode x := C.encode (e x)
  parse input := (C.parse input).map fun result => (e.symm result.1, result.2)
  size x := C.size (e x)

/-- Concatenating product codec. -/
def prodCodec {α : Type u} {β : Type v} (A : Codec α) (B : Codec β) :
    Codec (α × β) where
  encode x := A.encode x.1 ++ B.encode x.2
  parse input :=
    match A.parse input with
    | none => none
    | some (x, rest) =>
        (B.parse rest).map fun result => ((x, result.1), result.2)
  size x := A.size x.1 + B.size x.2

/-- Tagged disjoint-sum codec. -/
def sumCodec {α : Type u} {β : Type v} (A : Codec α) (B : Codec β) :
    Codec (α ⊕ β) where
  encode
    | .inl x => false :: A.encode x
    | .inr y => true :: B.encode y
  parse
    | [] => none
    | false :: input => (A.parse input).map fun result => (.inl result.1, result.2)
    | true :: input => (B.parse input).map fun result => (.inr result.1, result.2)
  size
    | .inl x => A.size x + 1
    | .inr y => B.size y + 1

/-- Tagged optional-value codec. -/
def optionCodec {α : Type u} (C : Codec α) : Codec (Option α) where
  encode
    | none => [false]
    | some x => true :: C.encode x
  parse
    | [] => none
    | false :: suffix => some (none, suffix)
    | true :: input => (C.parse input).map fun result => (some result.1, result.2)
  size
    | none => 1
    | some x => C.size x + 1

/-- Encode a list using one nil/cons bit at each step. -/
def encodeList {α : Type u} (C : Codec α) : List α → BitString
  | [] => [false]
  | x :: xs => true :: C.encode x ++ encodeList C xs

/-- Structural size of the canonical list encoding. -/
def listSize {α : Type u} (C : Codec α) : List α → Nat
  | [] => 1
  | x :: xs => C.size x + listSize C xs + 1

/-- Fuel-bounded parser for the tagged list encoding. -/
def parseListAux {α : Type u} (C : Codec α) :
    Nat → BitString → Option (List α × BitString)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: suffix => some ([], suffix)
  | fuel + 1, true :: input => do
      let (x, rest) ← C.parse input
      let (xs, suffix) ← parseListAux C fuel rest
      pure (x :: xs, suffix)

/-- Parse one canonical list from the front of a string. -/
def parseList {α : Type u} (C : Codec α) (input : BitString) :
    Option (List α × BitString) :=
  parseListAux C (input.length + 1) input

/-- Canonical tagged-list codec. -/
def listCodec {α : Type u} (C : Codec α) : Codec (List α) where
  encode := encodeList C
  parse := parseList C
  size := listSize C

/-- A fixed-length vector is a list together with its length equation. -/
def vectorCodec {α : Type u} (C : Codec α) (n : Nat) : Codec (List.Vector α n) where
  encode xs := (listCodec C).encode xs.1
  parse input := do
    let (xs, suffix) ← (listCodec C).parse input
    if h : xs.length = n then
      pure (⟨xs, h⟩, suffix)
    else
      none
  size xs := (listCodec C).size xs.1

/-- Functions on a finite initial segment are encoded in increasing argument
order. -/
def finFunctionCodec {α : Type u} (C : Codec α) (n : Nat) : Codec (Fin n → α) :=
  equivCodec (Equiv.vectorEquivFin α n).symm (vectorCodec C n)

/-- A finite index is encoded as a natural number and checked against its
bound while parsing. -/
def finCodec (n : Nat) : Codec (Fin n) where
  encode i := natCodec.encode i.val
  parse input := do
    let (i, suffix) ← natCodec.parse input
    if h : i < n then
      pure (⟨i, h⟩, suffix)
    else
      none
  size i := natCodec.size i.val

axiom equivCodec_lawful {α : Type u} {β : Type v} (e : α ≃ β) (C : Codec β)
    (hC : C.Lawful) :
  (equivCodec e C).Lawful

axiom prodCodec_lawful {α : Type u} {β : Type v} (A : Codec α) (B : Codec β)
    (hA : A.Lawful) (hB : B.Lawful) :
  (prodCodec A B).Lawful

axiom sumCodec_lawful {α : Type u} {β : Type v} (A : Codec α) (B : Codec β)
    (hA : A.Lawful) (hB : B.Lawful) :
  (sumCodec A B).Lawful

axiom optionCodec_lawful {α : Type u} (C : Codec α) (hC : C.Lawful) :
  (optionCodec C).Lawful

axiom listCodec_lawful {α : Type u} (C : Codec α) (hC : C.Lawful) :
  (listCodec C).Lawful

axiom vectorCodec_lawful {α : Type u} (C : Codec α) (hC : C.Lawful) (n : Nat) :
  (vectorCodec C n).Lawful

axiom finFunctionCodec_lawful {α : Type u} (C : Codec α) (hC : C.Lawful)
    (n : Nat) :
  (finFunctionCodec C n).Lawful

axiom finCodec_lawful (n : Nat) : (finCodec n).Lawful

axiom equivCodec_effective {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (e : α ≃ β) (C : Codec β)
    (he : Computable e) (heSymm : Computable e.symm) (hC : C.Effective) :
  (equivCodec e C).Effective

axiom prodCodec_effective {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (A : Codec α) (B : Codec β)
    (hA : A.Effective) (hB : B.Effective) :
  (prodCodec A B).Effective

axiom sumCodec_effective {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (A : Codec α) (B : Codec β)
    (hA : A.Effective) (hB : B.Effective) :
  (sumCodec A B).Effective

axiom optionCodec_effective {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) :
  (optionCodec C).Effective

axiom listCodec_effective {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) :
  (listCodec C).Effective

axiom vectorCodec_effective {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) (n : Nat) :
  (vectorCodec C n).Effective

axiom finFunctionCodec_effective {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) (n : Nat) :
  (finFunctionCodec C n).Effective

axiom finCodec_effective (n : Nat) : (finCodec n).Effective

end Lax58.CodecCombinators
