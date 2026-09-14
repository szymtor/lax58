/-!
---
title: Structural presentations of finite data
type: definition
---

Finite data may be presented through one universal shape: binary trees with
natural-number leaves. A presentation consists of a map into this shape and a
partial inverse. Its structural size counts shape nodes, independently of any
binary serialization or in-memory layout.

`Presentation` is deliberately low-level infrastructure. An arbitrary
presentation is not automatically a neutral complexity-theoretic input
representation: its forward map could compute and attach derived advice.
Advice-freedom is supplied downstream by complete, kernel-checked constructor
equations built from the fixed structural vocabulary.

Natural payload magnitude is recorded separately from structural size. This
separation is useful for word-machine applications: a large natural leaf still
occupies one structural node, but may require a wider machine word.
-/

namespace Lax560851.StructuralPresentation

universe u

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

/-- Largest natural-number payload occurring in a representation. -/
def maxNat : Raw → Nat
  | .nat n => n
  | .pair a b => max a.maxNat b.maxNat

/-- Every natural payload in a representation fits into a `w`-bit word. -/
def PayloadsFitInWord (raw : Raw) (w : Nat) : Prop :=
  raw.maxNat < 2 ^ w

end Raw

/-- An encoder into the universal shape and a partial inverse. -/
structure Presentation (α : Type u) where
  toRaw : α → Raw
  fromRaw : Raw → Option α

/-- Package an injective structural map as a low-level presentation by
choosing a preimage on its range. This construction certifies no complexity
or constructor-structurality property of the supplied map. -/
noncomputable def presentationOf {α : Type u} (f : α → Raw) : Presentation α := by
  classical
  exact {
    toRaw := f
    fromRaw := fun raw =>
      if h : ∃ x, f x = raw then some (Classical.choose h) else none
  }

namespace Presentation

/-- Distinguished representations round-trip. -/
def Lawful {α : Type u} (P : Presentation α) : Prop :=
  ∀ x : α, P.fromRaw (P.toRaw x) = some x

/-- Distinct values have distinct structural representations. -/
def Faithful {α : Type u} (P : Presentation α) : Prop :=
  Function.Injective P.toRaw

/-- Structural size before any serialization or memory layout is chosen. -/
def structuralSize {α : Type u} (P : Presentation α) (x : α) : Nat :=
  (P.toRaw x).nodes

/-- Largest natural payload in the distinguished representation. -/
def maxNat {α : Type u} (P : Presentation α) (x : α) : Nat :=
  (P.toRaw x).maxNat

/-- Every natural payload of a value fits into a `w`-bit word. -/
def PayloadsFitInWord {α : Type u}
    (P : Presentation α) (x : α) (w : Nat) : Prop :=
  (P.toRaw x).PayloadsFitInWord w

end Presentation

end Lax560851.StructuralPresentation
