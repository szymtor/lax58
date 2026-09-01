import Lax58.StructuralEncodingLaws
import Lax58Proofs.PrimitiveCodecs

namespace Lax58Proofs.StructuralEncodingLaws

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.StructuralEncoding
open Lax58.StructuralEncoding.Presentation
open Lax58.StructuralEncodingLaws

universe u v

/-! The following definitions are the hidden witness. None of their tag,
parser, or collection choices occur in the public concept package. -/

private def rawEncode : Raw → BitString
  | .nat n => false :: Lax58.PrimitiveCodecs.natCodec.encode n
  | .pair a b => true :: rawEncode a ++ rawEncode b

private def rawParseAux : Nat → BitString → Option (Raw × BitString)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: input => do
      let (n, suffix) ← Lax58.PrimitiveCodecs.natCodec.parse input
      pure (.nat n, suffix)
  | fuel + 1, true :: input => do
      let (a, input) ← rawParseAux fuel input
      let (b, suffix) ← rawParseAux fuel input
      pure (.pair a b, suffix)

private def rawParse (input : BitString) : Option (Raw × BitString) :=
  rawParseAux (input.length + 1) input

private def rawCodec : Codec Raw where
  encode := rawEncode
  parse := rawParse
  size := Raw.bitSize

private def inducedCodec {α : Type u} (P : Presentation α) : Codec α where
  encode x := rawCodec.encode (P.toRaw x)
  parse input :=
    match rawCodec.parse input with
    | none => none
    | some (raw, suffix) =>
        match P.fromRaw raw with
        | none => none
        | some x => some (x, suffix)
  size x := rawCodec.size (P.toRaw x)

private def equivPresentation {α : Type u} {β : Type v} (e : α ≃ β) (P : Presentation β) :
    Presentation α where
  toRaw x := P.toRaw (e x)
  fromRaw raw := (P.fromRaw raw).map e.symm

private def unitPresentation : Presentation Unit where
  toRaw _ := .nat 0
  fromRaw
    | .nat 0 => some ()
    | _ => none

private def boolPresentation : Presentation Bool where
  toRaw
    | false => .nat 0
    | true => .nat 1
  fromRaw
    | .nat 0 => some false
    | .nat 1 => some true
    | _ => none

private def natPresentation : Presentation Nat where
  toRaw := .nat
  fromRaw
    | .nat n => some n
    | _ => none

private def intPresentation : Presentation Int where
  toRaw
    | .ofNat n => .pair (.nat 0) (.nat n)
    | .negSucc n => .pair (.nat 1) (.nat n)
  fromRaw
    | .pair (.nat 0) (.nat n) => some (.ofNat n)
    | .pair (.nat 1) (.nat n) => some (.negSucc n)
    | _ => none

private def prodPresentation {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) :
    Presentation (α × β) where
  toRaw x := .pair (A.toRaw x.1) (B.toRaw x.2)
  fromRaw
    | .pair a b =>
        match A.fromRaw a with
        | none => none
        | some x =>
            match B.fromRaw b with
            | none => none
            | some y => some (x, y)
    | _ => none

private def sumPresentation {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) :
    Presentation (α ⊕ β) where
  toRaw
    | .inl x => .pair (.nat 0) (A.toRaw x)
    | .inr y => .pair (.nat 1) (B.toRaw y)
  fromRaw
    | .pair (.nat 0) raw => (A.fromRaw raw).map Sum.inl
    | .pair (.nat 1) raw => (B.fromRaw raw).map Sum.inr
    | _ => none

private def optionPresentation {α : Type u} (P : Presentation α) :
    Presentation (Option α) where
  toRaw
    | none => .nat 0
    | some x => .pair (.nat 0) (P.toRaw x)
  fromRaw
    | .nat 0 => some none
    | .pair (.nat 0) raw => (P.fromRaw raw).map some
    | _ => none

private def listToRaw {α : Type u} (P : Presentation α) : List α → Raw
  | [] => .nat 0
  | x :: xs => .pair (P.toRaw x) (listToRaw P xs)

private def listFromRaw {α : Type u} (P : Presentation α) : Raw → Option (List α)
  | .nat 0 => some []
  | .pair x xs => do
      let x ← P.fromRaw x
      let xs ← listFromRaw P xs
      pure (x :: xs)
  | _ => none

private def listPresentation {α : Type u} (P : Presentation α) : Presentation (List α) where
  toRaw := listToRaw P
  fromRaw := listFromRaw P

private def arrayPresentation {α : Type u} (P : Presentation α) : Presentation (Array α) where
  toRaw xs := listToRaw P xs.toList
  fromRaw raw := (listFromRaw P raw).map List.toArray

private def finPresentation (n : Nat) : Presentation (Fin n) where
  toRaw i := .nat i.val
  fromRaw
    | .nat i => if h : i < n then some ⟨i, h⟩ else none
    | _ => none

private def subtypePresentation {α : Type u} (P : Presentation α) (p : α → Prop)
    [DecidablePred p] : Presentation {x // p x} where
  toRaw x := P.toRaw x.val
  fromRaw raw := do
    let x ← P.fromRaw raw
    if h : p x then pure ⟨x, h⟩ else none

private def vectorPresentation {α : Type u} (P : Presentation α) (n : Nat) :
    Presentation (List.Vector α n) where
  toRaw xs := listToRaw P xs.1
  fromRaw raw := do
    let xs ← listFromRaw P raw
    if h : xs.length = n then pure ⟨xs, h⟩ else none

private def finFunctionPresentation {α : Type u} (P : Presentation α) (n : Nat) :
    Presentation (Fin n → α) :=
  equivPresentation (Equiv.vectorEquivFin α n).symm (vectorPresentation P n)

private def multisetPresentation {α : Type u} [LinearOrder α] (P : Presentation α) :
    Presentation (Multiset α) where
  toRaw s := listToRaw P (s.sort (· ≤ ·))
  fromRaw raw := (listFromRaw P raw).map (↑·)

private def finsetPresentation {α : Type u} [LinearOrder α] (P : Presentation α) :
    Presentation (Finset α) where
  toRaw s := listToRaw P (s.sort (· ≤ ·))
  fromRaw raw := (listFromRaw P raw).map List.toFinset

private theorem raw_nodes_le_bitSize (raw : Raw) : raw.nodes ≤ raw.bitSize := by
  induction raw with
  | nat n =>
      simp [Raw.nodes, Raw.bitSize]
  | pair a b ha hb =>
      simp only [Raw.nodes, Raw.bitSize]
      omega

private theorem raw_encode_length (raw : Raw) : (rawEncode raw).length = raw.bitSize := by
  induction raw with
  | nat n =>
      simpa [rawEncode, Raw.bitSize] using
        Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_lawful.encode_length n
  | pair a b ha hb =>
      simp only [rawEncode, Raw.bitSize, List.length_cons, List.length_append]
      omega

private theorem raw_parseAux_encode_append (raw : Raw) (suffix : BitString)
    (fuel : Nat) (hfuel : raw.nodes < fuel) :
    rawParseAux fuel (rawEncode raw ++ suffix) = some (raw, suffix) := by
  induction raw generalizing fuel suffix with
  | nat n =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [rawEncode, List.cons_append, rawParseAux]
          rw [Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_lawful.parse_encode_append]
          rfl
  | pair a b ha hb =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [rawEncode, List.cons_append, rawParseAux]
          have haFuel : a.nodes < fuel := by
            simp only [Raw.nodes] at hfuel
            omega
          have hbFuel : b.nodes < fuel := by
            simp only [Raw.nodes] at hfuel
            omega
          rw [List.append_assoc, ha (rawEncode b ++ suffix) fuel haFuel]
          dsimp
          rw [hb suffix fuel hbFuel]
          rfl

private theorem raw_parse_encode_append (raw : Raw) (suffix : BitString) :
    rawParse (rawEncode raw ++ suffix) = some (raw, suffix) := by
  apply raw_parseAux_encode_append
  simp only [List.length_append]
  have hnodes := raw_nodes_le_bitSize raw
  rw [raw_encode_length]
  omega

private theorem raw_parseAux_canonical : ∀ fuel input raw suffix,
    rawParseAux fuel input = some (raw, suffix) → input = rawEncode raw ++ suffix := by
  intro fuel
  induction fuel with
  | zero =>
      intro input raw suffix h
      simp [rawParseAux] at h
  | succ fuel ih =>
      intro input raw suffix h
      cases input with
      | nil => simp [rawParseAux] at h
      | cons tag input =>
          cases tag with
          | false =>
              simp only [rawParseAux] at h
              cases hp : Lax58.PrimitiveCodecs.natCodec.parse input with
              | none => simp [hp] at h
              | some result =>
                  obtain ⟨n, remaining⟩ := result
                  simp [hp] at h
                  obtain ⟨rfl, rfl⟩ := h
                  simpa [rawEncode] using congrArg (false :: ·)
                    (Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_canonical.parse_canonical hp)
          | true =>
              simp only [rawParseAux] at h
              cases ha : rawParseAux fuel input with
              | none => simp [ha] at h
              | some resultA =>
                  obtain ⟨a, rest⟩ := resultA
                  cases hb : rawParseAux fuel rest with
                  | none => simp [ha, hb] at h
                  | some resultB =>
                      obtain ⟨b, remaining⟩ := resultB
                      simp [ha, hb] at h
                      obtain ⟨rfl, rfl⟩ := h
                      rw [ih input a rest ha, ih rest b remaining hb]
                      simp [rawEncode, List.append_assoc]

private theorem raw_lawful : rawCodec.Lawful where
  parse_encode_append := raw_parse_encode_append
  encode_length := by
    intro raw
    exact raw_encode_length raw

private theorem raw_canonical : rawCodec.Canonical where
  toLawful := raw_lawful
  parse_canonical := by
    intro input raw suffix h
    exact raw_parseAux_canonical (input.length + 1) input raw suffix h

private theorem induced_lawful {α : Type u} (P : Presentation α)
    (hP : P.Lawful) : (inducedCodec P).Lawful where
  parse_encode_append := by
    intro x suffix
    simp only [inducedCodec]
    rw [raw_lawful.parse_encode_append]
    dsimp
    rw [hP x]
  encode_length := by
    intro x
    exact raw_lawful.encode_length (P.toRaw x)

private theorem induced_canonical {α : Type u} (P : Presentation α)
    (hP : P.Canonical) : (inducedCodec P).Canonical where
  toLawful := induced_lawful P hP.1
  parse_canonical := by
    intro input x suffix h
    simp only [inducedCodec] at h ⊢
    cases hp : rawCodec.parse input with
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
    (P : Presentation β) (hP : P.Lawful) : (equivPresentation e P).Lawful := by
  intro x
  simp only [equivPresentation]
  rw [hP (e x)]
  simp

private theorem lawful_unit : unitPresentation.Lawful := by
  intro x
  cases x
  rfl

private theorem lawful_bool : boolPresentation.Lawful := by
  intro x
  cases x <;> rfl

private theorem lawful_nat : natPresentation.Lawful := by
  intro x
  rfl

private theorem lawful_int : intPresentation.Lawful := by
  intro x
  cases x <;> rfl

private theorem lawful_prod {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Lawful) (hB : B.Lawful) :
    (prodPresentation A B).Lawful := by
  intro x
  simp only [prodPresentation]
  rw [hA x.1, hB x.2]

private theorem lawful_sum {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Lawful) (hB : B.Lawful) :
    (sumPresentation A B).Lawful := by
  intro x
  cases x with
  | inl x => simp [sumPresentation, hA x]
  | inr x => simp [sumPresentation, hB x]

private theorem lawful_option {α : Type u} (P : Presentation α) (hP : P.Lawful) :
    (optionPresentation P).Lawful := by
  intro x
  cases x with
  | none => rfl
  | some x => simp [optionPresentation, hP x]

private theorem list_roundtrip {α : Type u} (P : Presentation α) (hP : P.Lawful)
    (xs : List α) : listFromRaw P (listToRaw P xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listToRaw, listFromRaw, hP x, ih]

private theorem lawful_list {α : Type u} (P : Presentation α) (hP : P.Lawful) :
    (listPresentation P).Lawful := list_roundtrip P hP

private theorem lawful_array {α : Type u} (P : Presentation α) (hP : P.Lawful) :
    (arrayPresentation P).Lawful := by
  intro xs
  simp [arrayPresentation, list_roundtrip P hP]

private theorem lawful_fin (n : Nat) : (finPresentation n).Lawful := by
  intro i
  simp [finPresentation, i.isLt]

private theorem lawful_subtype {α : Type u} (P : Presentation α) (p : α → Prop)
    [DecidablePred p] (hP : P.Lawful) : (subtypePresentation P p).Lawful := by
  intro x
  simp [subtypePresentation, hP x.val, x.property]

private theorem lawful_vector {α : Type u} (P : Presentation α) (n : Nat)
    (hP : P.Lawful) : (vectorPresentation P n).Lawful := by
  intro xs
  simp [vectorPresentation, list_roundtrip P hP, xs.2]

private theorem lawful_finFunction {α : Type u} (P : Presentation α) (n : Nat)
    (hP : P.Lawful) : (finFunctionPresentation P n).Lawful :=
  lawful_equiv _ _ (lawful_vector P n hP)

private theorem lawful_multiset {α : Type u} [LinearOrder α] (P : Presentation α)
    (hP : P.Lawful) : (multisetPresentation P).Lawful := by
  intro s
  simp [multisetPresentation, list_roundtrip P hP]

private theorem lawful_finset {α : Type u} [LinearOrder α] (P : Presentation α)
    (hP : P.Lawful) : (finsetPresentation P).Lawful := by
  intro s
  simp [finsetPresentation, list_roundtrip P hP]

private theorem canonical_unit : unitPresentation.Canonical := by
  refine ⟨lawful_unit, ?_⟩
  intro raw x h
  cases x
  cases raw with
  | pair a b => simp [unitPresentation] at h
  | nat n =>
      cases n with
      | zero => rfl
      | succ n => simp [unitPresentation] at h

private theorem canonical_bool : boolPresentation.Canonical := by
  refine ⟨lawful_bool, ?_⟩
  intro raw x h
  cases raw with
  | pair a b => simp [boolPresentation] at h
  | nat n =>
      cases x with
      | false =>
          cases n with
          | zero => rfl
          | succ n =>
              cases n <;> simp [boolPresentation] at h
      | true =>
          cases n with
          | zero => simp [boolPresentation] at h
          | succ n =>
              cases n with
              | zero => rfl
              | succ n => simp [boolPresentation] at h

private theorem canonical_nat : natPresentation.Canonical := by
  refine ⟨lawful_nat, ?_⟩
  intro raw x h
  cases raw with
  | pair a b => simp [natPresentation] at h
  | nat n =>
      simp [natPresentation] at h
      subst x
      rfl

private theorem canonical_int : intPresentation.Canonical := by
  refine ⟨lawful_int, ?_⟩
  intro raw x h
  cases raw with
  | nat n => simp [intPresentation] at h
  | pair a b =>
      cases a with
      | pair a₁ a₂ => simp [intPresentation] at h
      | nat tag =>
          cases b with
          | pair b₁ b₂ => simp [intPresentation] at h
          | nat payload =>
              cases x with
              | ofNat x =>
                  cases tag with
                  | zero =>
                      simp [intPresentation] at h
                      have hx : payload = x := Int.ofNat_injective h
                      subst x
                      rfl
                  | succ tag =>
                      cases tag <;> simp [intPresentation] at h
              | negSucc x =>
                  cases tag with
                  | zero => simp [intPresentation] at h
                  | succ tag =>
                      cases tag with
                      | zero =>
                          simp [intPresentation] at h
                          subst x
                          rfl
                      | succ tag => simp [intPresentation] at h

private theorem canonical_prod {α : Type u} {β : Type v} (A : Presentation α)
    (B : Presentation β) (hA : A.Canonical) (hB : B.Canonical) :
    (prodPresentation A B).Canonical := by
  refine ⟨lawful_prod A B hA.1 hB.1, ?_⟩
  intro raw x h
  cases raw with
  | nat n => simp [prodPresentation] at h
  | pair a b =>
      simp only [prodPresentation] at h ⊢
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
    (sumPresentation A B).Canonical := by
  refine ⟨lawful_sum A B hA.1 hB.1, ?_⟩
  intro raw x h
  cases raw with
  | nat n => simp [sumPresentation] at h
  | pair tag raw =>
      cases tag with
      | pair a b => simp [sumPresentation] at h
      | nat n =>
          cases n with
          | zero =>
              cases hp : A.fromRaw raw <;> cases x <;>
                simp [sumPresentation, hp] at h ⊢
              subst_vars
              rw [hA.2 hp]
          | succ n =>
              cases n with
              | zero =>
                  cases hp : B.fromRaw raw <;> cases x <;>
                    simp [sumPresentation, hp] at h ⊢
                  subst_vars
                  rw [hB.2 hp]
              | succ n => simp [sumPresentation] at h

private theorem canonical_option {α : Type u} (P : Presentation α)
    (hP : P.Canonical) : (optionPresentation P).Canonical := by
  refine ⟨lawful_option P hP.1, ?_⟩
  intro raw x h
  cases raw with
  | nat n =>
      cases n <;> cases x <;> simp [optionPresentation] at h ⊢
  | pair tag raw =>
      cases tag with
      | pair a b => simp [optionPresentation] at h
      | nat n =>
          cases n with
          | zero =>
              cases hp : P.fromRaw raw <;> cases x <;>
                simp [optionPresentation, hp] at h ⊢
              subst_vars
              rw [hP.2 hp]
          | succ n => simp [optionPresentation] at h

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
    (hP : P.Canonical) : (listPresentation P).Canonical := by
  refine ⟨lawful_list P hP.1, ?_⟩
  intro raw xs h
  exact list_canonical_aux P hP h

private theorem listToRaw_bitSize {α : Type u} (P : Presentation α)
    (xs : List α) :
    (listToRaw P xs).bitSize =
      2 + xs.length + (xs.map P.bitSize).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [listToRaw, Raw.bitSize, List.length_cons, List.map_cons,
        List.sum_cons, Presentation.bitSize]
      rw [ih]
      omega

private def standard : Standard.{u} where
  rawCodec := rawCodec
  induced := inducedCodec
  equiv := equivPresentation
  unit := unitPresentation
  bool := boolPresentation
  nat := natPresentation
  int := intPresentation
  prod := prodPresentation
  sum := sumPresentation
  option := optionPresentation
  list := listPresentation
  array := arrayPresentation
  fin := finPresentation
  subtype := subtypePresentation
  vector := vectorPresentation
  finFunction := finFunctionPresentation
  multiset := multisetPresentation
  finset := finsetPresentation

private theorem standard_valid : standard.Valid where
  raw_lawful := raw_lawful
  raw_canonical := raw_canonical
  raw_size := by intro raw; rfl
  induced_encode := by intro α P x; rfl
  induced_size := by intro α P x; rfl
  induced_lawful := induced_lawful
  induced_canonical := induced_canonical
  equiv_size := by intro α β e P x; rfl
  unit_size := by intro x; cases x; rfl
  bool_size := by intro b; cases b <;> rfl
  nat_size := by intro n; rfl
  int_ofNat_size := by
    intro n
    simp [standard, intPresentation, Presentation.bitSize, Raw.bitSize,
      Lax58.PrimitiveCodecs.natCodec, Lax58.PrimitiveCodecs.natSize,
      Lax58.PrimitiveCodecs.binaryBits]
    omega
  int_negSucc_size := by
    intro n
    simp [standard, intPresentation, Presentation.bitSize, Raw.bitSize,
      Lax58.PrimitiveCodecs.natCodec, Lax58.PrimitiveCodecs.natSize,
      Lax58.PrimitiveCodecs.binaryBits, Lax58.PrimitiveCodecs.incrementBits]
    omega
  prod_size := by intro α β A B x y; rfl
  sum_inl_size := by
    intro α β A B x
    simp [standard, sumPresentation, Presentation.bitSize, Raw.bitSize,
      Lax58.PrimitiveCodecs.natCodec, Lax58.PrimitiveCodecs.natSize,
      Lax58.PrimitiveCodecs.binaryBits]
    omega
  sum_inr_size := by
    intro α β A B y
    simp [standard, sumPresentation, Presentation.bitSize, Raw.bitSize,
      Lax58.PrimitiveCodecs.natCodec, Lax58.PrimitiveCodecs.natSize,
      Lax58.PrimitiveCodecs.binaryBits, Lax58.PrimitiveCodecs.incrementBits]
    omega
  option_none_size := by intro α P; rfl
  option_some_size := by
    intro α P x
    simp [standard, optionPresentation, Presentation.bitSize, Raw.bitSize,
      Lax58.PrimitiveCodecs.natCodec, Lax58.PrimitiveCodecs.natSize,
      Lax58.PrimitiveCodecs.binaryBits]
    omega
  list_size := by intro α P xs; exact listToRaw_bitSize P xs
  array_size := by
    intro α P xs
    simpa [arrayPresentation, Presentation.bitSize] using
      listToRaw_bitSize P xs.toList
  fin_size := by intro n i; rfl
  subtype_size := by intro α P p inst x; rfl
  vector_size := by
    intro α P n xs
    simpa [vectorPresentation, Presentation.bitSize, xs.2] using
      listToRaw_bitSize P xs.toList
  finFunction_size := by
    intro α P n f
    change (listToRaw P (List.Vector.ofFn f).toList).bitSize =
      2 + n + (List.ofFn fun i => P.bitSize (f i)).sum
    rw [List.Vector.toList_ofFn, listToRaw_bitSize, List.map_ofFn]
    simp [Function.comp_def]
  multiset_size := by
    intro α inst P s
    rw [show (standard.multiset P).bitSize s =
        (listToRaw P (s.sort (· ≤ ·))).bitSize by rfl]
    rw [listToRaw_bitSize]
    simp only [Multiset.length_sort]
    congr 1
    have hsort : (↑(s.sort (· ≤ ·)) : Multiset α) = s :=
      Multiset.sort_eq _ _
    have hsum := congrArg (fun t : Multiset α => (t.map P.bitSize).sum) hsort
    rw [← Multiset.sum_coe]
    simpa only [Multiset.map_coe] using hsum
  finset_size := by
    intro α inst P s
    rw [show (standard.finset P).bitSize s =
        (listToRaw P (s.sort (· ≤ ·))).bitSize by rfl]
    rw [listToRaw_bitSize]
    simp only [Finset.length_sort]
    congr 1
    change (List.map P.bitSize (s.sort (· ≤ ·))).sum =
      (s.1.map P.bitSize).sum
    have hsort : (↑(s.sort (· ≤ ·)) : Multiset α) = s.1 :=
      Finset.sort_eq _ _
    have hsum := congrArg (fun t : Multiset α => (t.map P.bitSize).sum) hsort
    rw [← Multiset.sum_coe]
    simpa only [Multiset.map_coe] using hsum
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

/--
---
conclusion: Lax58.StructuralEncodingLaws.exists_standard
---
-/
theorem exists_standard : ∃ S : Standard.{u}, S.Valid :=
  ⟨standard, standard_valid⟩

end Lax58Proofs.StructuralEncodingLaws
