import Lax808846.RamComputes
import Lax560851.WordArena

/-!
---
title: Time and word-capacity bounds on the word-RAM
type: definition
---

One fixed program computes a mathematical function within explicit time and
word-capacity bounds. It works at every word width satisfying the input-fit
conditions and the supplied capacity threshold. The threshold is a number of
representable values, not a number of bits. Output production is included in
the instruction count, including a fetched final `halt` or exhausted `read`.
The arena is supplied on Lax808846's immutable input array and sequential
tape; writable memory starts at zero. No computability or growth restriction
on either bound is implicit: such restrictions belong in the theorem using this predicate.

`RamComputableWithinUsing` is relative to explicitly supplied encodings; it
does not certify them. The `RamComputableWithin` frontend selects approved
encodings from the input and output types. Inputs use structural arenas;
natural and Boolean outputs use one word, and structured outputs use arenas.
-/

namespace Lax560851.RamComplexity

open Lax808846.Ram Lax808846.RamComputes
open Lax560851.StructuralPresentation Lax560851.WordArena

universe u v

/-- Input size and payload magnitude for a specified presentation. -/
def inputMagnitudeUsing {α : Type u} (input : Presentation α) (x : α) : Nat :=
  (input.toRaw x).nodes + (input.toRaw x).maxNat + 1

/-- A natural-number result occupies one output word. -/
def natOutput (n : Nat) : List Nat := [n]

/-- A Boolean result occupies one output word: false is zero, true is one. -/
def boolOutput (b : Bool) : List Nat := [if b then 1 else 0]

/-- A structured result uses the same root-plus-arena convention as input. -/
def arenaOutput {α : Type u} (raw : α → Raw) (x : α) : List Nat :=
  (encodeRaw (raw x)).toInput

/-- One program for all inputs and all sufficient word widths, with explicit
encodings and exact instruction and word-capacity bounds. -/
def RamComputableWithinUsing {α : Type u} {β : Type v}
    (input : Presentation α) (output : β → List Nat)
    (f : α → β) (timeBound wordBound : α → Nat) : Prop :=
  ∃ program : Program,
    ∀ (x : α) (w : Nat),
      (input.toRaw x).PayloadsFitInWord w →
      3 * (input.toRaw x).nodes ≤ 2 ^ w →
      wordBound x ≤ 2 ^ w →
      ComputesInTime w program {(encode input x).toInput}
        (fun _ => output (f x)) (fun _ => timeBound x)

end Lax560851.RamComplexity
