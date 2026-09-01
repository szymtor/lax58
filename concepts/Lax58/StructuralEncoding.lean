import Mathlib.Data.Finset.Sort
import Mathlib.Data.Vector.Basic
import Lax58.PrimitiveCodecs

/-!
---
title: Structural presentations of finite data
type: definition
---

Finite data may be presented through one universal shape: binary trees with
natural-number leaves. The universal shape has a canonical prefix codec. A
presentation of a type consists of maps to and from this shape. It is lawful
when encoding followed by decoding is the identity, and canonical when the
decoder accepts only the distinguished representation of each value.

Presentations compose along the standard finitary type constructors. Lists
retain their order. Multisets and finite sets have a sorted distinguished
encoding but permissive decoders: permutations are accepted, and finite-set
decoding ignores repetitions.
-/

namespace Lax58.StructuralEncoding

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.PrimitiveCodecs

universe u v

/-- The universal shape of structurally finite data. -/
inductive Raw where
  | nat : Nat → Raw
  | pair : Raw → Raw → Raw
  deriving DecidableEq

namespace Raw

/-- Number of nodes in a universal structural representation. -/
def nodes : Raw → Nat
  | .nat _ => 1
  | .pair a b => nodes a + nodes b + 1

/-- Canonical bit length of a universal structural representation. -/
def bitSize : Raw → Nat
  | .nat n => natCodec.size n + 1
  | .pair a b => bitSize a + bitSize b + 1

/-- Prefix encoding: `false` introduces a natural leaf and `true` a pair. -/
def encode : Raw → BitString
  | .nat n => false :: natCodec.encode n
  | .pair a b => true :: encode a ++ encode b

/-- Fuel-bounded parser for one universal structural value. -/
def parseAux : Nat → BitString → Option (Raw × BitString)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: input => do
      let (n, suffix) ← natCodec.parse input
      pure (.nat n, suffix)
  | fuel + 1, true :: input => do
      let (a, input) ← parseAux fuel input
      let (b, suffix) ← parseAux fuel input
      pure (.pair a b, suffix)

/-- Parse one universal structural value from the front of a bit string. -/
def parse (input : BitString) : Option (Raw × BitString) :=
  parseAux (input.length + 1) input

/-- Canonical prefix codec for the universal structural representation. -/
def codec : Codec Raw where
  encode := encode
  parse := parse
  size := bitSize

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

namespace Presentation

/-- A presentation round-trips its distinguished representations. -/
def Lawful {α : Type u} (P : Presentation α) : Prop :=
  ∀ x : α, P.fromRaw (P.toRaw x) = some x

/-- A presentation is canonical if it accepts no alternative universal
representation of a value. -/
def Canonical {α : Type u} (P : Presentation α) : Prop :=
  P.Lawful ∧ ∀ {raw : Raw} {x : α}, P.fromRaw raw = some x → raw = P.toRaw x

/-- Binary codec induced by a structural presentation. -/
def codec {α : Type u} (P : Presentation α) : Codec α where
  encode x := Raw.codec.encode (P.toRaw x)
  parse input :=
    match Raw.codec.parse input with
    | none => none
    | some (raw, suffix) =>
        match P.fromRaw raw with
        | none => none
        | some x => some (x, suffix)
  size x := Raw.codec.size (P.toRaw x)

/-- Structural size before natural leaves are serialized into bits. -/
def structuralSize {α : Type u} (P : Presentation α) (x : α) : Nat :=
  (P.toRaw x).nodes

/-- Transport a presentation across an equivalence. -/
def equiv {α : Type u} {β : Type v} (e : α ≃ β) (P : Presentation β) :
    Presentation α where
  toRaw x := P.toRaw (e x)
  fromRaw raw := (P.fromRaw raw).map e.symm

/-- Presentation of the one-element type. -/
def unit : Presentation Unit where
  toRaw _ := .nat 0
  fromRaw
    | .nat 0 => some ()
    | _ => none

/-- Presentation of Booleans by the two natural leaves `0` and `1`. -/
def bool : Presentation Bool where
  toRaw
    | false => .nat 0
    | true => .nat 1
  fromRaw
    | .nat 0 => some false
    | .nat 1 => some true
    | _ => none

/-- Presentation of natural numbers as natural leaves. -/
def nat : Presentation Nat where
  toRaw := .nat
  fromRaw
    | .nat n => some n
    | _ => none

/-- Tagged presentation of integers. -/
def int : Presentation Int where
  toRaw
    | .ofNat n => .pair (.nat 0) (.nat n)
    | .negSucc n => .pair (.nat 1) (.nat n)
  fromRaw
    | .pair (.nat 0) (.nat n) => some (.ofNat n)
    | .pair (.nat 1) (.nat n) => some (.negSucc n)
    | _ => none

/-- Pairing presentation of products. -/
def prod {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    Presentation (α × β) where
  toRaw x := .pair (A.toRaw x.1) (B.toRaw x.2)
  fromRaw
    | .pair a b =>
        match A.fromRaw a with
        | none => none
        | some x =>
            match B.fromRaw b with
            | none => none
            | some y => some (x, y)
    | _ => none

/-- Tagged presentation of disjoint sums. -/
def sum {α : Type u} {β : Type v} (A : Presentation α) (B : Presentation β) :
    Presentation (α ⊕ β) where
  toRaw
    | .inl x => .pair (.nat 0) (A.toRaw x)
    | .inr y => .pair (.nat 1) (B.toRaw y)
  fromRaw
    | .pair (.nat 0) raw => (A.fromRaw raw).map Sum.inl
    | .pair (.nat 1) raw => (B.fromRaw raw).map Sum.inr
    | _ => none

/-- Tagged presentation of optional values. -/
def option {α : Type u} (P : Presentation α) : Presentation (Option α) where
  toRaw
    | none => .nat 0
    | some x => .pair (.nat 0) (P.toRaw x)
  fromRaw
    | .nat 0 => some none
    | .pair (.nat 0) raw => (P.fromRaw raw).map some
    | _ => none

/-- Universal representation of an ordered list. -/
def listToRaw {α : Type u} (P : Presentation α) : List α → Raw
  | [] => .nat 0
  | x :: xs => .pair (P.toRaw x) (listToRaw P xs)

/-- Partial inverse of `listToRaw`. -/
def listFromRaw {α : Type u} (P : Presentation α) : Raw → Option (List α)
  | .nat 0 => some []
  | .pair x xs => do
      let x ← P.fromRaw x
      let xs ← listFromRaw P xs
      pure (x :: xs)
  | _ => none

/-- Presentation of ordered lists. -/
def list {α : Type u} (P : Presentation α) : Presentation (List α) where
  toRaw := listToRaw P
  fromRaw := listFromRaw P

/-- Presentation of arrays through lists. -/
def array {α : Type u} (P : Presentation α) : Presentation (Array α) :=
  { toRaw := fun xs => listToRaw P xs.toList
    fromRaw := fun raw => (listFromRaw P raw).map List.toArray }

/-- A finite index is presented by its value, with the bound rechecked. -/
def fin (n : Nat) : Presentation (Fin n) where
  toRaw i := .nat i.val
  fromRaw
    | .nat i => if h : i < n then some ⟨i, h⟩ else none
    | _ => none

/-- A subtype is encoded as its underlying value, with its predicate
rechecked while decoding. -/
def subtype {α : Type u} (P : Presentation α) (p : α → Prop)
    [DecidablePred p] : Presentation {x // p x} where
  toRaw x := P.toRaw x.val
  fromRaw raw := do
    let x ← P.fromRaw raw
    if h : p x then pure ⟨x, h⟩ else none

/-- Fixed-length vectors are lists whose decoded length is checked. -/
def vector {α : Type u} (P : Presentation α) (n : Nat) :
    Presentation (List.Vector α n) where
  toRaw xs := listToRaw P xs.1
  fromRaw raw := do
    let xs ← listFromRaw P raw
    if h : xs.length = n then pure ⟨xs, h⟩ else none

/-- Functions on `Fin n` are presented in increasing argument order. -/
def finFunction {α : Type u} (P : Presentation α) (n : Nat) :
    Presentation (Fin n → α) :=
  equiv (Equiv.vectorEquivFin α n).symm (vector P n)

/-- A multiset is encoded by a sorted list, while decoding accepts every
permutation of that list. -/
def multiset {α : Type u} [LinearOrder α] (P : Presentation α) :
    Presentation (Multiset α) where
  toRaw s := listToRaw P (s.sort (· ≤ ·))
  fromRaw raw := (listFromRaw P raw).map (↑·)

/-- A finite set is encoded by a sorted list, while decoding accepts every
order and ignores repetitions. -/
def finset {α : Type u} [LinearOrder α] (P : Presentation α) :
    Presentation (Finset α) where
  toRaw s := listToRaw P (s.sort (· ≤ ·))
  fromRaw raw := (listFromRaw P raw).map List.toFinset

end Presentation

end Lax58.StructuralEncoding
