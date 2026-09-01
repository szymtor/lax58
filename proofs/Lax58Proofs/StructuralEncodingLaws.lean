import Lax58.StructuralEncodingLaws
import Lax58Proofs.PrimitiveCodecs

namespace Lax58Proofs.StructuralEncodingLaws

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.StructuralEncoding
open Lax58.StructuralEncoding.Presentation
open Lax58.StructuralEncodingLaws

universe u v

private theorem raw_nodes_le_bitSize (raw : Raw) : raw.nodes ≤ raw.bitSize := by
  induction raw with
  | nat n =>
      simp [Raw.nodes, Raw.bitSize]
  | pair a b ha hb =>
      simp only [Raw.nodes, Raw.bitSize]
      omega

private theorem raw_encode_length (raw : Raw) : raw.encode.length = raw.bitSize := by
  induction raw with
  | nat n =>
      simpa [Raw.encode, Raw.bitSize] using
        Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_lawful.encode_length n
  | pair a b ha hb =>
      simp only [Raw.encode, Raw.bitSize, List.length_cons, List.length_append]
      omega

private theorem raw_parseAux_encode_append (raw : Raw) (suffix : BitString)
    (fuel : Nat) (hfuel : raw.nodes < fuel) :
    Raw.parseAux fuel (raw.encode ++ suffix) = some (raw, suffix) := by
  induction raw generalizing fuel suffix with
  | nat n =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Raw.encode, List.cons_append, Raw.parseAux]
          rw [Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_lawful.parse_encode_append]
          rfl
  | pair a b ha hb =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [Raw.encode, List.cons_append, Raw.parseAux]
          have haFuel : a.nodes < fuel := by
            simp only [Raw.nodes] at hfuel
            omega
          have hbFuel : b.nodes < fuel := by
            simp only [Raw.nodes] at hfuel
            omega
          rw [List.append_assoc, ha (Raw.encode b ++ suffix) fuel haFuel]
          dsimp
          rw [hb suffix fuel hbFuel]
          rfl

private theorem raw_parse_encode_append (raw : Raw) (suffix : BitString) :
    Raw.parse (raw.encode ++ suffix) = some (raw, suffix) := by
  apply raw_parseAux_encode_append
  simp only [List.length_append]
  have hnodes := raw_nodes_le_bitSize raw
  rw [raw_encode_length]
  omega

private theorem raw_parseAux_canonical : ∀ fuel input raw suffix,
    Raw.parseAux fuel input = some (raw, suffix) → input = raw.encode ++ suffix := by
  intro fuel
  induction fuel with
  | zero =>
      intro input raw suffix h
      simp [Raw.parseAux] at h
  | succ fuel ih =>
      intro input raw suffix h
      cases input with
      | nil => simp [Raw.parseAux] at h
      | cons tag input =>
          cases tag with
          | false =>
              simp only [Raw.parseAux] at h
              cases hp : Lax58.PrimitiveCodecs.natCodec.parse input with
              | none => simp [hp] at h
              | some result =>
                  obtain ⟨n, remaining⟩ := result
                  simp [hp] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simpa [Raw.encode] using congrArg (false :: ·)
                    (Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_canonical.parse_canonical hp)
          | true =>
              simp only [Raw.parseAux] at h
              cases ha : Raw.parseAux fuel input with
              | none => simp [ha] at h
              | some resultA =>
                  obtain ⟨a, rest⟩ := resultA
                  cases hb : Raw.parseAux fuel rest with
                  | none => simp [ha, hb] at h
                  | some resultB =>
                      obtain ⟨b, remaining⟩ := resultB
                      simp [ha, hb] at h
                      obtain ⟨rfl, rfl⟩ := h
                      rw [ih input a rest ha, ih rest b remaining hb]
                      simp [Raw.encode, List.append_assoc]

private theorem raw_lawful : Raw.codec.Lawful where
  parse_encode_append := raw_parse_encode_append
  encode_length := by
    intro raw
    exact raw_encode_length raw

private theorem raw_canonical : Raw.codec.Canonical where
  toLawful := raw_lawful
  parse_canonical := by
    intro input raw suffix h
    exact raw_parseAux_canonical (input.length + 1) input raw suffix h

private theorem induced_lawful {α : Type u} (P : Presentation α)
    (hP : P.Lawful) : P.codec.Lawful where
  parse_encode_append := by
    intro x suffix
    simp only [Presentation.codec]
    rw [raw_lawful.parse_encode_append]
    dsimp
    rw [hP x]
  encode_length := by
    intro x
    exact raw_lawful.encode_length (P.toRaw x)

private theorem induced_canonical {α : Type u} (P : Presentation α)
    (hP : P.Canonical) : P.codec.Canonical where
  toLawful := induced_lawful P hP.1
  parse_canonical := by
    intro input x suffix h
    simp only [Presentation.codec] at h ⊢
    cases hp : Raw.codec.parse input with
    | none => simp [hp] at h
    | some result =>
        obtain ⟨raw, remaining⟩ := result
        cases hd : P.fromRaw raw with
        | none => simp [hp, hd] at h
        | some y =>
            simp [hp, hd] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [raw_canonical.parse_canonical hp, hP.2 hd]

private theorem lawful_equiv {α : Type u} {β : Type v} (e : α ≃ β)
    (P : Presentation β) (hP : P.Lawful) : (Presentation.equiv e P).Lawful := by
  intro x
  simp only [Presentation.equiv]
  rw [hP (e x)]
  simp

private theorem lawful_unit : Presentation.unit.Lawful := by
  intro x
  cases x
  rfl

private theorem lawful_bool : Presentation.bool.Lawful := by
  intro x
  cases x <;> rfl

private theorem lawful_nat : Presentation.nat.Lawful := by
  intro x
  rfl

private theorem lawful_int : Presentation.int.Lawful := by
  intro x
  cases x <;> rfl

private theorem lawful_prod {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Lawful) (hB : B.Lawful) :
    (Presentation.prod A B).Lawful := by
  intro x
  simp only [Presentation.prod]
  rw [hA x.1, hB x.2]

private theorem lawful_sum {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Lawful) (hB : B.Lawful) :
    (Presentation.sum A B).Lawful := by
  intro x
  cases x with
  | inl x => simp [Presentation.sum, hA x]
  | inr x => simp [Presentation.sum, hB x]

private theorem lawful_option {α : Type u} (P : Presentation α) (hP : P.Lawful) :
    (Presentation.option P).Lawful := by
  intro x
  cases x with
  | none => rfl
  | some x => simp [Presentation.option, hP x]

private theorem list_roundtrip {α : Type u} (P : Presentation α) (hP : P.Lawful)
    (xs : List α) : listFromRaw P (listToRaw P xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listToRaw, listFromRaw, hP x, ih]

private theorem lawful_list {α : Type u} (P : Presentation α) (hP : P.Lawful) :
    (Presentation.list P).Lawful := list_roundtrip P hP

private theorem lawful_array {α : Type u} (P : Presentation α) (hP : P.Lawful) :
    (Presentation.array P).Lawful := by
  intro xs
  simp [Presentation.array, list_roundtrip P hP]

private theorem lawful_fin (n : Nat) : (Presentation.fin n).Lawful := by
  intro i
  simp [Presentation.fin, i.isLt]

private theorem lawful_subtype {α : Type u} (P : Presentation α) (p : α → Prop)
    [DecidablePred p] (hP : P.Lawful) : (Presentation.subtype P p).Lawful := by
  intro x
  simp [Presentation.subtype, hP x.val, x.property]

private theorem lawful_vector {α : Type u} (P : Presentation α) (n : Nat)
    (hP : P.Lawful) : (Presentation.vector P n).Lawful := by
  intro xs
  simp [Presentation.vector, list_roundtrip P hP, xs.2]

private theorem lawful_finFunction {α : Type u} (P : Presentation α) (n : Nat)
    (hP : P.Lawful) : (Presentation.finFunction P n).Lawful :=
  lawful_equiv _ _ (lawful_vector P n hP)

private theorem lawful_multiset {α : Type u} [LinearOrder α] (P : Presentation α)
    (hP : P.Lawful) : (Presentation.multiset P).Lawful := by
  intro s
  simp [Presentation.multiset, list_roundtrip P hP]

private theorem lawful_finset {α : Type u} [LinearOrder α] (P : Presentation α)
    (hP : P.Lawful) : (Presentation.finset P).Lawful := by
  intro s
  simp [Presentation.finset, list_roundtrip P hP]

private theorem canonical_unit : Presentation.unit.Canonical := by
  refine ⟨lawful_unit, ?_⟩
  intro raw x h
  cases x
  cases raw with
  | pair a b => simp [Presentation.unit] at h
  | nat n =>
      cases n with
      | zero => rfl
      | succ n => simp [Presentation.unit] at h

private theorem canonical_bool : Presentation.bool.Canonical := by
  refine ⟨lawful_bool, ?_⟩
  intro raw x h
  cases raw with
  | pair a b => simp [Presentation.bool] at h
  | nat n =>
      cases x with
      | false =>
          cases n with
          | zero => rfl
          | succ n =>
              cases n <;> simp [Presentation.bool] at h
      | true =>
          cases n with
          | zero => simp [Presentation.bool] at h
          | succ n =>
              cases n with
              | zero => rfl
              | succ n => simp [Presentation.bool] at h

private theorem canonical_nat : Presentation.nat.Canonical := by
  refine ⟨lawful_nat, ?_⟩
  intro raw x h
  cases raw with
  | pair a b => simp [Presentation.nat] at h
  | nat n =>
      simp [Presentation.nat] at h
      subst x
      rfl

private theorem canonical_int : Presentation.int.Canonical := by
  refine ⟨lawful_int, ?_⟩
  intro raw x h
  cases raw with
  | nat n => simp [Presentation.int] at h
  | pair a b =>
      cases a with
      | pair a₁ a₂ => simp [Presentation.int] at h
      | nat tag =>
          cases b with
          | pair b₁ b₂ => simp [Presentation.int] at h
          | nat payload =>
              cases x with
              | ofNat x =>
                  cases tag with
                  | zero =>
                      simp [Presentation.int] at h
                      have hx : payload = x := Int.ofNat_injective h
                      subst x
                      rfl
                  | succ tag =>
                      cases tag <;> simp [Presentation.int] at h
              | negSucc x =>
                  cases tag with
                  | zero => simp [Presentation.int] at h
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp [Presentation.int] at h
                          subst x
                          rfl
                      | succ tag => simp [Presentation.int] at h

private theorem canonical_prod {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Canonical) (hB : B.Canonical) :
    (Presentation.prod A B).Canonical := by
  refine ⟨lawful_prod A B hA.1 hB.1, ?_⟩
  intro raw x h
  cases raw with
  | nat n => simp [Presentation.prod] at h
  | pair a b =>
      simp only [Presentation.prod] at h ⊢
      cases ha : A.fromRaw a with
      | none => simp [ha] at h
      | some x' =>
          cases hb : B.fromRaw b with
          | none => simp [ha, hb] at h
          | some y' =>
              simp [ha, hb] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [hA.2 ha, hB.2 hb]

private theorem canonical_sum {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Canonical) (hB : B.Canonical) :
    (Presentation.sum A B).Canonical := by
  refine ⟨lawful_sum A B hA.1 hB.1, ?_⟩
  intro raw x h
  cases raw with
  | nat n => simp [Presentation.sum] at h
  | pair tag raw =>
      cases tag with
      | pair a b => simp [Presentation.sum] at h
      | nat n =>
          cases n with
          | zero =>
              cases hp : A.fromRaw raw <;> cases x <;>
                simp [Presentation.sum, hp] at h ⊢
              subst_vars
              rw [hA.2 hp]
          | succ n =>
              cases n with
              | zero =>
                  cases hp : B.fromRaw raw <;> cases x <;>
                    simp [Presentation.sum, hp] at h ⊢
                  subst_vars
                  rw [hB.2 hp]
              | succ n => simp [Presentation.sum] at h

private theorem canonical_option {α : Type u} (P : Presentation α)
    (hP : P.Canonical) : (Presentation.option P).Canonical := by
  refine ⟨lawful_option P hP.1, ?_⟩
  intro raw x h
  cases raw with
  | nat n =>
      cases n <;> cases x <;> simp [Presentation.option] at h ⊢
  | pair tag raw =>
      cases tag with
      | pair a b => simp [Presentation.option] at h
      | nat n =>
          cases n with
          | zero =>
              cases hp : P.fromRaw raw <;> cases x <;>
                simp [Presentation.option, hp] at h ⊢
              subst_vars
              rw [hP.2 hp]
          | succ n => simp [Presentation.option] at h

private theorem list_canonical_aux {α : Type u} (P : Presentation α)
    (hP : P.Canonical) {raw : Raw} {xs : List α}
    (h : listFromRaw P raw = some xs) : raw = listToRaw P xs := by
  induction raw generalizing xs with
  | nat n =>
      cases n with
      | zero =>
          simp [listFromRaw] at h
          subst xs
          rfl
      | succ n => simp [listFromRaw] at h
  | pair a b ha hb =>
      simp only [listFromRaw] at h
      cases hx : P.fromRaw a with
      | none => simp [hx] at h
      | some x =>
          cases hxs : listFromRaw P b with
          | none => simp [hx, hxs] at h
          | some tail =>
              simp [hx, hxs] at h
              subst xs
              simp [listToRaw, hP.2 hx, hb hxs]

private theorem canonical_list {α : Type u} (P : Presentation α)
    (hP : P.Canonical) : (Presentation.list P).Canonical := by
  refine ⟨lawful_list P hP.1, ?_⟩
  intro raw xs h
  exact list_canonical_aux P hP h

/--
---
conclusion: Lax58.StructuralEncodingLaws.laws
---
-/
theorem laws : Laws where
  raw_lawful := raw_lawful
  raw_canonical := raw_canonical
  induced_lawful := induced_lawful
  induced_canonical := induced_canonical
  equiv := lawful_equiv
  unit := lawful_unit
  bool := lawful_bool
  nat := lawful_nat
  int := lawful_int
  prod := lawful_prod
  sum := lawful_sum
  option := lawful_option
  list := lawful_list
  array := lawful_array
  fin := lawful_fin
  subtype := lawful_subtype
  vector := lawful_vector
  finFunction := lawful_finFunction
  multiset := lawful_multiset
  finset := lawful_finset
  canonical_unit := canonical_unit
  canonical_bool := canonical_bool
  canonical_nat := canonical_nat
  canonical_int := canonical_int
  canonical_prod := canonical_prod
  canonical_sum := canonical_sum
  canonical_option := canonical_option
  canonical_list := canonical_list

end Lax58Proofs.StructuralEncodingLaws
