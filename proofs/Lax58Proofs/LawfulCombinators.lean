import Lax58.LawfulCombinators

namespace Lax58Proofs.LawfulCombinators

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CodecCombinators
open Lax58.PrimitiveCodecs
open Lax58.LawfulCombinators

universe u v

private theorem lawful_equiv {α : Type u} {β : Type v} (e : α ≃ β)
    (C : Codec β) (hC : C.Lawful) : (equivCodec e C).Lawful where
  parse_encode_append := by
    intro x suffix
    simp [equivCodec, hC.parse_encode_append]
  encode_length := by
    intro x
    exact hC.encode_length (e x)

private theorem lawful_prod {α : Type u} {β : Type v} (A : Codec α)
    (B : Codec β) (hA : A.Lawful) (hB : B.Lawful) :
    (prodCodec A B).Lawful where
  parse_encode_append := by
    intro x suffix
    simp [prodCodec, List.append_assoc, hA.parse_encode_append,
      hB.parse_encode_append]
  encode_length := by
    intro x
    simp [prodCodec, hA.encode_length, hB.encode_length]

private theorem lawful_sum {α : Type u} {β : Type v} (A : Codec α)
    (B : Codec β) (hA : A.Lawful) (hB : B.Lawful) :
    (sumCodec A B).Lawful where
  parse_encode_append := by
    intro x suffix
    cases x <;> simp [sumCodec, hA.parse_encode_append, hB.parse_encode_append]
  encode_length := by
    intro x
    cases x <;> simp [sumCodec, hA.encode_length, hB.encode_length]

private theorem lawful_option {α : Type u} (C : Codec α) (hC : C.Lawful) :
    (optionCodec C).Lawful where
  parse_encode_append := by
    intro x suffix
    cases x <;> simp [optionCodec, hC.parse_encode_append]
  encode_length := by
    intro x
    cases x <;> simp [optionCodec, hC.encode_length]

private theorem parseListAux_encode_append {α : Type u} (C : Codec α)
    (hC : C.Lawful) (xs : List α) (suffix : BitString) (fuel : Nat)
    (hfuel : xs.length < fuel) :
    parseListAux C fuel (encodeList C xs ++ suffix) = some (xs, suffix) := by
  induction xs generalizing fuel with
  | nil =>
      cases fuel <;> simp_all [parseListAux, encodeList]
  | cons x xs ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [encodeList, List.cons_append, parseListAux]
          rw [List.append_assoc, hC.parse_encode_append]
          dsimp
          rw [ih fuel (by simpa using hfuel)]
          rfl

private theorem parseList_encode_append {α : Type u} (C : Codec α)
    (hC : C.Lawful) (xs : List α) (suffix : BitString) :
    parseList C (encodeList C xs ++ suffix) = some (xs, suffix) := by
  apply parseListAux_encode_append C hC
  simp
  induction xs with
  | nil => simp [encodeList]
  | cons x xs ih =>
      simp [encodeList] at *
      omega

private theorem lawful_list {α : Type u} (C : Codec α) (hC : C.Lawful) :
    (listCodec C).Lawful where
  parse_encode_append := parseList_encode_append C hC
  encode_length := by
    intro xs
    change (encodeList C xs).length = listSize C xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp [encodeList, listSize, hC.encode_length, ih]

private theorem lawful_vector {α : Type u} (C : Codec α) (n : Nat)
    (hC : C.Lawful) : (vectorCodec C n).Lawful := by
  have hList := lawful_list C hC
  constructor
  · intro xs suffix
    have hp := hList.parse_encode_append xs.1 suffix
    simp only [vectorCodec]
    rw [hp]
    simp [xs.2]
  · intro xs
    exact hList.encode_length xs.1

private theorem lawful_finFunction {α : Type u} (C : Codec α) (n : Nat)
    (hC : C.Lawful) : (finFunctionCodec C n).Lawful :=
  lawful_equiv _ _ (lawful_vector C n hC)

private theorem lawful_fin (n : Nat) : (finCodec n).Lawful := by
  have hNat := primitiveCodecs_valid.nat_lawful
  constructor
  · intro i suffix
    simp only [finCodec]
    rw [hNat.parse_encode_append]
    simp [i.isLt]
  · exact fun i => hNat.encode_length i.val

private theorem canonical_equiv {α : Type u} {β : Type v} (e : α ≃ β)
    (C : Codec β) (hC : C.Canonical) : (equivCodec e C).Canonical where
  toLawful := lawful_equiv e C hC.toLawful
  parse_canonical := by
    intro input x suffix h
    simp only [equivCodec] at h ⊢
    cases hp : C.parse input with
    | none => simp [hp] at h
    | some result =>
        obtain ⟨y, rest⟩ := result
        simp only [hp] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa using hC.parse_canonical hp

private theorem canonical_prod {α : Type u} {β : Type v} (A : Codec α)
    (B : Codec β) (hA : A.Canonical) (hB : B.Canonical) :
    (prodCodec A B).Canonical where
  toLawful := lawful_prod A B hA.toLawful hB.toLawful
  parse_canonical := by
    intro input x suffix h
    simp only [prodCodec] at h ⊢
    cases ha : A.parse input with
    | none => simp [ha] at h
    | some resultA =>
        obtain ⟨a, rest⟩ := resultA
        cases hb : B.parse rest with
        | none => simp [ha, hb] at h
        | some resultB =>
            obtain ⟨b, remaining⟩ := resultB
            simp only [ha, hb] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            rw [hA.parse_canonical ha, hB.parse_canonical hb,
              List.append_assoc]

private theorem canonical_sum {α : Type u} {β : Type v} (A : Codec α)
    (B : Codec β) (hA : A.Canonical) (hB : B.Canonical) :
    (sumCodec A B).Canonical where
  toLawful := lawful_sum A B hA.toLawful hB.toLawful
  parse_canonical := by
    intro input x suffix h
    cases input with
    | nil => simp [sumCodec] at h
    | cons tag rest =>
        cases tag <;> simp only [sumCodec] at h ⊢
        · cases hp : A.parse rest with
          | none => simp [hp] at h
          | some result =>
              obtain ⟨a, remaining⟩ := result
              simp only [hp] at h
              obtain ⟨rfl, rfl⟩ := h
              simpa [sumCodec] using congrArg (false :: ·) (hA.parse_canonical hp)
        · cases hp : B.parse rest with
          | none => simp [hp] at h
          | some result =>
              obtain ⟨b, remaining⟩ := result
              simp only [hp] at h
              obtain ⟨rfl, rfl⟩ := h
              simpa [sumCodec] using congrArg (true :: ·) (hB.parse_canonical hp)

private theorem canonical_option {α : Type u} (C : Codec α)
    (hC : C.Canonical) : (optionCodec C).Canonical where
  toLawful := lawful_option C hC.toLawful
  parse_canonical := by
    intro input x suffix h
    cases input with
    | nil => simp [optionCodec] at h
    | cons tag rest =>
        cases tag <;> simp only [optionCodec] at h ⊢
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rfl
        · cases hp : C.parse rest with
          | none => simp [hp] at h
          | some result =>
              obtain ⟨a, remaining⟩ := result
              simp only [hp] at h
              obtain ⟨rfl, rfl⟩ := h
              simpa [optionCodec] using congrArg (true :: ·) (hC.parse_canonical hp)

private theorem parseListAux_canonical {α : Type u} (C : Codec α)
    (hC : C.Canonical) : ∀ fuel input xs suffix,
    parseListAux C fuel input = some (xs, suffix) →
      input = encodeList C xs ++ suffix := by
  intro fuel
  induction fuel with
  | zero => intro input xs suffix h; simp [parseListAux] at h
  | succ fuel ih =>
      intro input xs suffix h
      cases input with
      | nil => simp [parseListAux] at h
      | cons tag input =>
          cases tag with
          | false =>
              simp only [parseListAux, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rfl
          | true =>
              simp only [parseListAux] at h
              cases hp : C.parse input with
              | none => simp [hp] at h
              | some result =>
                  obtain ⟨x, rest⟩ := result
                  cases hl : parseListAux C fuel rest with
                  | none => simp [hp, hl] at h
                  | some result =>
                      obtain ⟨tail, remaining⟩ := result
                      simp [hp, hl] at h
                      obtain ⟨rfl, rfl⟩ := h
                      rw [hC.parse_canonical hp, ih rest tail remaining hl]
                      simp [encodeList, List.append_assoc]

private theorem canonical_list {α : Type u} (C : Codec α)
    (hC : C.Canonical) : (listCodec C).Canonical where
  toLawful := lawful_list C hC.toLawful
  parse_canonical := by
    intro input xs suffix h
    exact parseListAux_canonical C hC (input.length + 1) input xs suffix h

private theorem canonical_vector {α : Type u} (C : Codec α) (n : Nat)
    (hC : C.Canonical) : (vectorCodec C n).Canonical := by
  have hList := canonical_list C hC
  constructor
  · exact lawful_vector C n hC.toLawful
  · intro input xs suffix h
    simp only [vectorCodec] at h ⊢
    cases hp : (listCodec C).parse input with
    | none => simp [hp] at h
    | some result =>
        obtain ⟨values, remaining⟩ := result
        rw [hp] at h
        dsimp at h
        split at h
        next hlen =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hList.parse_canonical hp
        next => simp at h

private theorem canonical_finFunction {α : Type u} (C : Codec α) (n : Nat)
    (hC : C.Canonical) : (finFunctionCodec C n).Canonical :=
  canonical_equiv _ _ (canonical_vector C n hC)

private theorem canonical_fin (n : Nat) : (finCodec n).Canonical := by
  have hNat := primitiveCodecs_valid.nat_canonical
  constructor
  · exact lawful_fin n
  · intro input i suffix h
    simp only [finCodec] at h ⊢
    cases hp : natCodec.parse input with
    | none => simp [hp] at h
    | some result =>
        obtain ⟨value, remaining⟩ := result
        rw [hp] at h
        dsimp at h
        split at h
        next hbound =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hNat.parse_canonical hp
        next => simp at h

/--
---
conclusion: Lax58.LawfulCombinators.closure
---
-/
theorem closure : Closure where
  equiv := lawful_equiv
  prod := lawful_prod
  sum := lawful_sum
  option := lawful_option
  list := lawful_list
  vector := lawful_vector
  finFunction := lawful_finFunction
  fin := lawful_fin
  canonical_equiv := canonical_equiv
  canonical_prod := canonical_prod
  canonical_sum := canonical_sum
  canonical_option := canonical_option
  canonical_list := canonical_list
  canonical_vector := canonical_vector
  canonical_finFunction := canonical_finFunction
  canonical_fin := canonical_fin

end Lax58Proofs.LawfulCombinators
