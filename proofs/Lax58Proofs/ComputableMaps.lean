import Lax58.ComputableMaps

namespace Lax58Proofs.ComputableMaps

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.ComputableMaps

universe u v

/--
---
conclusion: Lax58.ComputableMaps.computableMap_of_computable
---
-/
theorem computableMap_of_computable {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (C : Codec α) (D : Codec β)
    (hC : C.Lawful) (hCE : C.Effective) (hDE : D.Effective)
    {f : α → β} (hf : Computable f) : ComputableMap C D f := by
  let program : BitString → Option BitString := fun input =>
    (C.parse input).map fun result => D.encode (f result.1)
  refine ⟨program, ?_, ?_⟩
  · have hvalue : Computable (fun result : α × BitString =>
        D.encode (f result.1)) :=
      hDE.1.comp (hf.comp Computable.fst)
    exact Computable.option_map hCE.2.1
      ((hvalue.comp Computable.snd).to₂)
  · intro x
    have hp := hC.parse_encode_append x []
    simp only [List.append_nil] at hp
    simp [program, hp]

end Lax58Proofs.ComputableMaps
