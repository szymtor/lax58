import Lax58.CanonicalDecoding

namespace Lax58Proofs.CanonicalDecoding

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CanonicalDecoding

universe u

private theorem decode_encode {α : Type u} (C : Codec α) (hC : C.Lawful)
    (x : α) : C.decode (C.encode x) = some x := by
  have hp := hC.parse_encode_append x []
  simp only [List.append_nil] at hp
  rw [Codec.decode, hp]

/--
---
conclusion: Lax58.CanonicalDecoding.laws
---
-/
theorem laws : DecodingLaws where
  decode_encode := decode_encode
  encode_injective := by
    intro α C hC x y hxy
    have h := congrArg C.decode hxy
    simpa [decode_encode C hC x, decode_encode C hC y] using h
  decode_eq_some_iff := by
    intro α C hC input x
    constructor
    · intro h
      unfold Codec.decode at h
      cases hp : C.parse input with
      | none => simp [hp] at h
      | some result =>
          obtain ⟨y, suffix⟩ := result
          cases suffix with
          | nil =>
              simp only [hp, Option.some.injEq] at h
              subst y
              simpa using hC.parse_canonical hp
          | cons b suffix => simp [hp] at h
    · intro h
      subst input
      exact decode_encode C hC.toLawful x

end Lax58Proofs.CanonicalDecoding
