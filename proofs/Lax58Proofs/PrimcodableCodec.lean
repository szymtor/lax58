import Lax58.PrimcodableCodec
import Lax58Proofs.PrimitiveCodecs

namespace Lax58Proofs.PrimcodableCodec

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.PrimcodableCodec

universe u

private theorem lawful (α : Type u) [Primcodable α] : (codec α).Lawful where
  parse_encode_append := by
    intro x suffix
    simp only [codec]
    rw [Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_lawful.parse_encode_append]
    simp [Encodable.decode₂_encode]
  encode_length := by
    intro x
    exact Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_lawful.encode_length
      (Encodable.encode x)

private theorem canonical (α : Type u) [Primcodable α] : (codec α).Canonical where
  toLawful := lawful α
  parse_canonical := by
    intro input x suffix h
    simp only [codec] at h ⊢
    cases hp : Lax58.PrimitiveCodecs.natCodec.parse input with
    | none => simp [hp] at h
    | some result =>
        obtain ⟨n, remaining⟩ := result
        cases hd : Encodable.decode₂ α n with
        | none => simp [hp, hd] at h
        | some y =>
            simp [hp, hd] at h
            obtain ⟨rfl, rfl⟩ := h
            have hn : Encodable.encode y = n := Encodable.decode₂_eq_some.mp hd
            rw [Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_canonical.parse_canonical hp,
              ← hn]

private def finish (α : Type u) [Primcodable α] (result : Nat × BitString) :
    Option (α × BitString) :=
  (Encodable.decode₂ α result.1).map fun x => (x, result.2)

private theorem finish_computable (α : Type u) [Primcodable α] :
    Computable (finish α) := by
  exact (Computable.option_map
    (Primrec.decode₂.to_comp.comp Computable.fst)
    (Computable.snd.pair (Computable.snd.comp Computable.fst)).to₂).of_eq
      (fun result => by simp [finish])

private theorem effective (α : Type u) [Primcodable α] : (codec α).Effective := by
  have hNat := Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_effective
  refine ⟨hNat.1.comp Primrec.encode.to_comp, ?_, hNat.2.2.comp Primrec.encode.to_comp⟩
  exact (Computable.option_bind hNat.2.1
    ((finish_computable α).comp Computable.snd).to₂).of_eq
      (fun input => by
        simp [codec, finish]
        cases Lax58.PrimitiveCodecs.natCodec.parse input with
        | none => rfl
        | some result =>
            obtain ⟨n, suffix⟩ := result
            cases hd : Encodable.decode₂ α n <;> simp [hd])

/--
---
conclusion: Lax58.PrimcodableCodec.valid
---
-/
theorem valid : Valid where
  lawful := lawful
  canonical := canonical
  effective := effective

end Lax58Proofs.PrimcodableCodec
