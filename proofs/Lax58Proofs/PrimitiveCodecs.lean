import Lax58.PrimitiveCodecs

namespace Lax58Proofs.PrimitiveCodecs

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.PrimitiveCodecs

private theorem bitsToNat_incrementBits (bits : BitString) :
    bitsToNat (incrementBits bits) = bitsToNat bits + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      cases b <;> simp [incrementBits, bitsToNat, ih] <;> omega

private theorem bitsToNat_binaryBits (n : Nat) :
    bitsToNat (binaryBits n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binaryBits, bitsToNat_incrementBits, ih]

private theorem splitZeros_replicate (width : Nat) (rest : BitString) :
    splitZeros (List.replicate width false ++ true :: rest) =
      (width, true :: rest) := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ, splitZeros, ih]

private theorem takeExact_append (payload suffix : BitString) :
    takeExact payload.length (payload ++ suffix) = some (payload, suffix) := by
  simp [takeExact]

private theorem parseNat_encode_append (n : Nat) (suffix : BitString) :
    parseNat (encodeNat n ++ suffix) = some (n, suffix) := by
  unfold parseNat
  simp only [encodeNat, List.append_assoc, List.cons_append]
  rw [splitZeros_replicate]
  simp only
  rw [takeExact_append]
  simp [bitsToNat_binaryBits]

private theorem parseNat_canonical {input : BitString} {n : Nat}
    {suffix : BitString} (h : parseNat input = some (n, suffix)) :
    input = encodeNat n ++ suffix := by
  unfold parseNat at h
  generalize hz : splitZeros input = z at h
  obtain ⟨width, rest⟩ := z
  cases rest with
  | nil => simp at h
  | cons delimiter rest =>
      cases delimiter with
      | false => simp at h
      | true =>
          cases ht : takeExact width rest with
          | none => simp [ht] at h
          | some result =>
              obtain ⟨payload, remaining⟩ := result
              simp [ht] at h
              obtain ⟨heq, hn, hsuffix⟩ := h
              subst n
              subst suffix
              exact heq.symm

private theorem unit_lawful : unitCodec.Lawful where
  parse_encode_append := by intro x suffix; cases x; rfl
  encode_length := by intro x; cases x; rfl

private theorem unit_canonical : unitCodec.Canonical where
  toLawful := unit_lawful
  parse_canonical := by
    intro input x suffix h
    cases x
    simp only [unitCodec] at h ⊢
    simpa using h

private theorem bool_lawful : boolCodec.Lawful where
  parse_encode_append := by intro b suffix; cases b <;> rfl
  encode_length := by intro b; cases b <;> rfl

private theorem bool_canonical : boolCodec.Canonical where
  toLawful := bool_lawful
  parse_canonical := by
    intro input b suffix h
    cases input with
    | nil => simp [boolCodec] at h
    | cons head tail =>
        simp only [boolCodec, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl

private theorem nat_lawful : natCodec.Lawful where
  parse_encode_append := parseNat_encode_append
  encode_length := by
    intro n
    simp [natCodec, encodeNat, natSize]
    omega

private theorem nat_canonical : natCodec.Canonical where
  toLawful := nat_lawful
  parse_canonical := parseNat_canonical

private def incrementStep (p : Bool × BitString × BitString) : BitString :=
  cond p.1 (false :: p.2.2) (true :: p.2.1)

private theorem incrementStep_prim : Primrec incrementStep := by
  exact (Primrec.cond Primrec.fst
    (Primrec.list_cons.comp (Primrec.const false) (Primrec.snd.comp Primrec.snd))
    (Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp Primrec.snd))).of_eq
      (fun p => by
        obtain ⟨b, tail, result⟩ := p
        cases b <;> rfl)

private theorem incrementBits_prim : Primrec incrementBits := by
  exact (Primrec.list_rec Primrec.id (Primrec.const [true])
    ((incrementStep_prim.comp Primrec.snd).to₂)).of_eq (fun bits => by
      change List.rec [true] (fun b tail result => incrementStep (b, tail, result)) bits =
        incrementBits bits
      induction bits with
      | nil => rfl
      | cons b bits ih =>
          change incrementStep (b, bits,
            List.rec [true] (fun b tail result => incrementStep (b, tail, result)) bits) =
              incrementBits (b :: bits)
          rw [ih]
          cases b <;> rfl)

private theorem binaryBits_prim : Primrec binaryBits := by
  exact (Primrec.nat_rec₁ ([] : BitString)
    ((incrementBits_prim.comp Primrec.snd).to₂)).of_eq (fun n => by
      induction n <;> simp [binaryBits, *])

private def bitsValueStep (p : Bool × BitString × Nat) : Nat :=
  p.1.toNat + 2 * p.2.2

private theorem bitsValueStep_prim : Primrec bitsValueStep := by
  have hbool : Primrec Bool.toNat :=
    Primrec.encode.of_eq (fun b => by cases b <;> rfl)
  exact (Primrec.nat_add.comp (hbool.comp Primrec.fst)
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).of_eq
      (fun _ => rfl)

private theorem bitsToNat_prim : Primrec bitsToNat := by
  exact (Primrec.list_rec Primrec.id (Primrec.const 0)
    ((bitsValueStep_prim.comp Primrec.snd).to₂)).of_eq (fun bits => by
      change List.rec 0 (fun b tail result => bitsValueStep (b, tail, result)) bits =
        bitsToNat bits
      induction bits with
      | nil => rfl
      | cons b bits ih =>
          change bitsValueStep (b, bits,
            List.rec 0 (fun b tail result => bitsValueStep (b, tail, result)) bits) =
              bitsToNat (b :: bits)
          rw [ih]
          cases b <;> rfl)

private def splitStep (p : Bool × BitString × (Nat × BitString)) : Nat × BitString :=
  cond p.1 (0, true :: p.2.1) (p.2.2.1 + 1, p.2.2.2)

private theorem splitStep_prim : Primrec splitStep := by
  have htrue : Primrec (fun p : Bool × BitString × (Nat × BitString) =>
      (0, true :: p.2.1)) :=
    (Primrec.const 0).pair
      (Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp Primrec.snd))
  have hfalse : Primrec (fun p : Bool × BitString × (Nat × BitString) =>
      (p.2.2.1 + 1, p.2.2.2)) :=
    (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.cond Primrec.fst htrue hfalse).of_eq
    (fun p => by
      obtain ⟨b, tail, result⟩ := p
      cases b <;> rfl)

private theorem splitZeros_prim : Primrec splitZeros := by
  exact (Primrec.list_rec Primrec.id (Primrec.const (0, []))
    ((splitStep_prim.comp Primrec.snd).to₂)).of_eq (fun bits => by
      change List.rec (0, []) (fun b tail result => splitStep (b, tail, result)) bits =
        splitZeros bits
      induction bits with
      | nil => rfl
      | cons b bits ih =>
          change splitStep (b, bits,
            List.rec (0, []) (fun b tail result => splitStep (b, tail, result)) bits) =
              splitZeros (b :: bits)
          rw [ih]
          cases b <;> rfl)

private theorem takeExact_prim : Primrec₂ takeExact := by
  have hpair : Primrec (fun p : Nat × BitString =>
      (p.2.take p.1, p.2.drop p.1)) :=
    (Primrec.list_take.comp Primrec.fst Primrec.snd).pair
      (Primrec.list_drop.comp Primrec.fst Primrec.snd)
  exact (Primrec.ite
    (Primrec.nat_le.comp Primrec.fst (Primrec.list_length.comp Primrec.snd))
    (Primrec.option_some.comp hpair) (Primrec.const none)).to₂.of_eq
      (fun n bits => by simp [takeExact])

private def falseBits (n : Nat) : BitString := List.replicate n false

private theorem falseBits_prim : Primrec falseBits := by
  exact (Primrec.nat_rec₁ ([] : BitString)
    ((Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)).of_eq
      (fun n => by induction n <;> simp [falseBits, List.replicate_succ, *])

private theorem encodeNat_prim : Primrec encodeNat := by
  have hbits := binaryBits_prim
  have hzeros : Primrec (fun n => falseBits (binaryBits n).length) :=
    falseBits_prim.comp (Primrec.list_length.comp hbits)
  have hpayload : Primrec (fun n => true :: binaryBits n) :=
    Primrec.list_cons.comp (Primrec.const true) hbits
  exact (Primrec.list_append.comp hzeros hpayload).of_eq
    (fun n => by simp [encodeNat, falseBits])

private theorem natSize_prim : Primrec natSize := by
  exact (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.list_length.comp binaryBits_prim))
    (Primrec.const 1)).of_eq (fun n => by simp [natSize])

private def finishPayload (input : BitString) (result : BitString × BitString) :
    Option (Nat × BitString) :=
  let n := bitsToNat result.1
  if encodeNat n ++ result.2 = input then some (n, result.2) else none

private theorem finishPayload_prim : Primrec₂ finishPayload := by
  have hn : Primrec (fun p : BitString × (BitString × BitString) =>
      bitsToNat p.2.1) :=
    bitsToNat_prim.comp (Primrec.fst.comp Primrec.snd)
  have hsuffix : Primrec (fun p : BitString × (BitString × BitString) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hcandidate : Primrec (fun p : BitString × (BitString × BitString) =>
      encodeNat (bitsToNat p.2.1) ++ p.2.2) :=
    Primrec.list_append.comp (encodeNat_prim.comp hn) hsuffix
  have hresult : Primrec (fun p : BitString × (BitString × BitString) =>
      (bitsToNat p.2.1, p.2.2)) := hn.pair hsuffix
  exact (Primrec.ite (Primrec.eq.comp hcandidate Primrec.fst)
    (Primrec.option_some.comp hresult) (Primrec.const none)).to₂.of_eq
      (fun input result => by simp [finishPayload])

private def parseAfterTake (input : BitString) (width : Nat) (rest : BitString) :
    Option (Nat × BitString) :=
  (takeExact width rest).bind (finishPayload input)

private theorem parseAfterTake_prim :
    Primrec (fun p : BitString × Nat × BitString =>
      parseAfterTake p.1 p.2.1 p.2.2) := by
  have htake : Primrec (fun p : BitString × Nat × BitString =>
      takeExact p.2.1 p.2.2) :=
    takeExact_prim.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.option_bind htake
    ((finishPayload_prim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)).of_eq
      (fun p => by simp [parseAfterTake])

private def parseSplitStep
    (p : (BitString × (Nat × BitString)) × (Bool × BitString)) :
    Option (Nat × BitString) :=
  cond p.2.1 (parseAfterTake p.1.1 p.1.2.1 p.2.2) none

private theorem parseSplitStep_prim : Primrec parseSplitStep := by
  have hsuccess : Primrec (fun p :
      (BitString × (Nat × BitString)) × (Bool × BitString) =>
      parseAfterTake p.1.1 p.1.2.1 p.2.2) :=
    parseAfterTake_prim.comp <|
      (Primrec.fst.comp Primrec.fst).pair <|
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair <|
          Primrec.snd.comp Primrec.snd
  exact (Primrec.cond (Primrec.fst.comp Primrec.snd)
    hsuccess (Primrec.const none)).of_eq
      (fun p => by
        obtain ⟨main, delimiter, rest⟩ := p
        cases delimiter <;> rfl)

private def parseAfterSplit (p : BitString × (Nat × BitString)) :
    Option (Nat × BitString) :=
  match p.2.2 with
  | [] => none
  | delimiter :: rest => parseSplitStep (p, delimiter, rest)

private theorem parseAfterSplit_prim : Primrec parseAfterSplit := by
  exact (Primrec.list_casesOn (Primrec.snd.comp (Primrec.snd.comp Primrec.id))
    (Primrec.const none)
    parseSplitStep_prim.to₂).of_eq
        (fun p => by
          obtain ⟨input, width, rest⟩ := p
          cases rest <;> rfl)

private theorem parseNat_prim : Primrec parseNat := by
  exact (parseAfterSplit_prim.comp (Primrec.id.pair splitZeros_prim)).of_eq
    (fun input => by
      change parseAfterSplit (input, splitZeros input) = parseNat input
      unfold parseAfterSplit parseNat
      cases hs : splitZeros input with
      | mk width rest =>
          cases rest with
          | nil => rfl
          | cons delimiter rest =>
              cases delimiter <;>
                simp [parseSplitStep, parseAfterTake, finishPayload])

private theorem unit_effective : unitCodec.Effective := by
  refine ⟨Computable.const [], ?_, Computable.const 0⟩
  exact Computable.option_some_iff.2
    ((Computable.const ()).pair Computable.id)

private theorem bool_effective : boolCodec.Effective := by
  constructor
  · exact Computable.list_cons.comp Computable.id (Computable.const ([] : BitString))
  constructor
  · exact (Primrec.list_casesOn Primrec.id
      (Primrec.const (none : Option (Bool × BitString)))
      ((Primrec.option_some.comp
        (Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).to₂)).of_eq
            (fun input => by cases input <;> rfl) |>.to_comp
  · exact Computable.const 1

/--
---
conclusion: Lax58.PrimitiveCodecs.primitiveCodecs_valid
---
-/
theorem primitiveCodecs_valid : PrimitiveCodecsValid where
  unit_lawful := unit_lawful
  bool_lawful := bool_lawful
  nat_lawful := nat_lawful
  unit_canonical := unit_canonical
  bool_canonical := bool_canonical
  nat_canonical := nat_canonical
  unit_effective := unit_effective
  bool_effective := bool_effective
  nat_effective := by
    exact ⟨encodeNat_prim.to_comp, parseNat_prim.to_comp, natSize_prim.to_comp⟩

end Lax58Proofs.PrimitiveCodecs
