import Lax58.FiniteCollections
import Lax58Proofs.LawfulCombinators

namespace Lax58Proofs.FiniteCollections

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CodecCombinators
open Lax58.FiniteCollections

universe u

/--
---
conclusion: Lax58.FiniteCollections.collectionCodecs_lawful
---
-/
theorem collectionCodecs_lawful : CollectionCodecsLawful where
  multiset := by
    intro α inst C hC
    letI := inst
    have hList := Lax58Proofs.LawfulCombinators.closure.{_, 0}.list C hC
    constructor
    · intro s suffix
      simp only [multisetCodec]
      rw [hList.parse_encode_append]
      simp
    · intro s
      exact hList.encode_length (s.sort (· ≤ ·))
  finset := by
    intro α inst C hC
    letI := inst
    have hList := Lax58Proofs.LawfulCombinators.closure.{_, 0}.list C hC
    constructor
    · intro s suffix
      simp only [finsetCodec]
      rw [hList.parse_encode_append]
      simp
    · intro s
      exact hList.encode_length (s.sort (· ≤ ·))

end Lax58Proofs.FiniteCollections
