/-!
---
title: Structural presentations of finite data
type: definition
---

Finite data may be presented through one universal shape: binary trees with
natural-number leaves. A presentation consists of a map into this shape and a
partial inverse. Its structural size counts shape nodes, independently of any
binary serialization or in-memory layout.

Natural payload magnitude is recorded separately from structural size. This
separation is useful for word-machine applications: a large natural leaf still
occupies one structural node, but may require a wider machine word.
-/

namespace Lax58.StructuralPresentation

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

namespace Presentation

/-- Distinguished representations round-trip. -/
def Lawful {α : Type u} (P : Presentation α) : Prop :=
  ∀ x : α, P.fromRaw (P.toRaw x) = some x

/-- Distinct values have distinct structural representations. -/
def Faithful {α : Type u} (P : Presentation α) : Prop :=
  Function.Injective P.toRaw

/-- A round-tripping presentation is faithful. -/
theorem faithful_of_lawful {α : Type u} {P : Presentation α}
    (hP : P.Lawful) : P.Faithful := by
  intro x y hxy
  have hx := hP x
  have hy := hP y
  rw [hxy, hy] at hx
  exact (Option.some.inj hx).symm

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

end Lax58.StructuralPresentation
