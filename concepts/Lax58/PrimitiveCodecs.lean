import Mathlib.Data.Nat.Bits
import Lax58.CanonicalCodec

/-!
---
title: Canonical codecs for primitive finite data
type: definition
---

The unit value uses the empty string and a Boolean uses one bit. A natural
number `n` is represented by a self-delimiting binary string: first come
`k` zero bits and a one-bit delimiter, followed by the `k` canonical
least-significant-bit-first digits of `n`, where `k` is their number. Thus its
length is exactly `2k+1`, logarithmic in `n+1`.

The corresponding prefix parsers are canonical, and their encoders, parsers,
and size functions are computable.
-/

namespace Lax58.PrimitiveCodecs

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec

/-- Interpret a least-significant-bit-first binary digit string. -/
def bitsToNat : BitString → Nat
  | [] => 0
  | b :: bits => (if b then 1 else 0) + 2 * bitsToNat bits

/-- Split off and count the initial zero bits. -/
def splitZeros : BitString → Nat × BitString
  | false :: bits =>
      let result := splitZeros bits
      (result.1 + 1, result.2)
  | bits => (0, bits)

/-- Take exactly `n` bits, failing if the input is too short. -/
def takeExact : Nat → BitString → Option (BitString × BitString)
  | 0, bits => some ([], bits)
  | _ + 1, [] => none
  | n + 1, b :: bits => do
      let (taken, suffix) ← takeExact n bits
      pure (b :: taken, suffix)

/-- The canonical self-delimiting binary representation of a natural number. -/
def encodeNat (n : Nat) : BitString :=
  List.replicate n.bits.length false ++ true :: n.bits

/-- The exact bit length of the canonical natural-number encoding. -/
def natSize (n : Nat) : Nat := 2 * n.bits.length + 1

/-- Parse one canonical natural number from the front of a bit string. -/
def parseNat (input : BitString) : Option (Nat × BitString) := do
  let (width, rest) := splitZeros input
  let true :: rest := rest | none
  let (payload, suffix) ← takeExact width rest
  let n := bitsToNat payload
  if encodeNat n ++ suffix = input then
    pure (n, suffix)
  else
    none

/-- Canonical codec for the one-element type. -/
def unitCodec : Codec Unit where
  encode _ := []
  parse input := some ((), input)
  size _ := 0

/-- Canonical one-bit codec for Boolean values. -/
def boolCodec : Codec Bool where
  encode b := [b]
  parse
    | [] => none
    | b :: suffix => some (b, suffix)
  size _ := 1

/-- Canonical self-delimiting binary codec for natural numbers. -/
def natCodec : Codec Nat where
  encode := encodeNat
  parse := parseNat
  size := natSize

axiom unitCodec_lawful : unitCodec.Lawful
axiom boolCodec_lawful : boolCodec.Lawful
axiom natCodec_lawful : natCodec.Lawful

axiom unitCodec_effective : unitCodec.Effective
axiom boolCodec_effective : boolCodec.Effective
axiom natCodec_effective : natCodec.Effective

end Lax58.PrimitiveCodecs
