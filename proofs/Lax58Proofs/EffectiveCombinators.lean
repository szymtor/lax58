import Lax58.EffectiveCombinators
import Lax58Proofs.PrimitiveCodecs

namespace Lax58Proofs.EffectiveCombinators

open Lax58.CanonicalCodec
open Lax58.CanonicalCodec.Codec
open Lax58.CodecCombinators
open Lax58.EffectiveCombinators

universe u v

private def foldStep {α : Type u} {β : Type v} (f : β → α → β) :
    List α × β → β ⊕ (List α × β)
  | ([], acc) => .inl acc
  | (x :: xs, acc) => .inr (xs, f acc x)

private theorem foldStep_computable {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (f : β → α → β) (hf : Computable₂ f) :
    Computable (foldStep f) := by
  let head : List α × β → Option α := fun state => state.1.head?
  let tail : List α × β → List α := fun state => state.1.tail
  have hHead : Computable head := Primrec.list_head?.to_comp.comp Computable.fst
  have hTail : Computable tail := Primrec.list_tail.to_comp.comp Computable.fst
  refine (Computable.option_casesOn hHead
    (Computable.sumInl.comp Computable.snd)
    ((Computable.sumInr.comp
      ((hTail.comp Computable.fst).pair
        (hf.comp (Computable.snd.comp Computable.fst) Computable.snd))).to₂)).of_eq ?_
  intro state
  obtain ⟨xs, acc⟩ := state
  cases xs <;> rfl

private theorem foldStep_terminates {α : Type u} {β : Type v}
    (f : β → α → β) (state : List α × β) :
    state.1.foldl f state.2 ∈
      PFun.fix (fun state => Part.some (foldStep f state)) state := by
  obtain ⟨xs, acc⟩ := state
  induction xs generalizing acc with
  | nil =>
      apply PFun.mem_fix_iff.2
      exact Or.inl (by simp [foldStep])
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply PFun.mem_fix_iff.2
      exact Or.inr ⟨(xs, f acc x), by simp [foldStep], ih (f acc x)⟩

private theorem list_foldl_computable {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (f : β → α → β) (hf : Computable₂ f)
    (init : β) : Computable fun xs : List α => xs.foldl f init := by
  have hfix : Partrec (PFun.fix (fun state : List α × β =>
      Part.some (foldStep f state))) :=
    Partrec.fix (foldStep_computable f hf).partrec
  have hall : Computable fun state : List α × β => state.1.foldl f state.2 :=
    hfix.of_eq_tot (foldStep_terminates f)
  exact hall.comp (Computable.id.pair (Computable.const init))

private theorem equiv_effective {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (e : α ≃ β) (C : Codec β)
    (he : Computable e) (hesymm : Computable e.symm) (hC : C.Effective) :
    (equivCodec e C).Effective := by
  refine ⟨hC.1.comp he, ?_, hC.2.2.comp he⟩
  exact (Computable.option_map hC.2.1
    (((hesymm.comp Computable.fst).pair Computable.snd).comp Computable.snd).to₂).of_eq
      (fun input => by simp [equivCodec])

private theorem prod_effective {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (A : Codec α) (B : Codec β)
    (hA : A.Effective) (hB : B.Effective) : (prodCodec A B).Effective := by
  refine ⟨?_, ?_, ?_⟩
  · exact Computable.list_append.comp
      (hA.1.comp Computable.fst) (hB.1.comp Computable.snd)
  · let finish : α × BitString → Option ((α × β) × BitString) := fun first =>
      (B.parse first.2).map fun second => ((first.1, second.1), second.2)
    have hfinish : Computable finish := by
      exact (Computable.option_map (hB.2.1.comp Computable.snd)
        (((Computable.fst.comp Computable.fst).pair
          (Computable.fst.comp Computable.snd)).pair
          (Computable.snd.comp Computable.snd)).to₂).of_eq
            (fun first => by simp [finish])
    exact (Computable.option_bind hA.2.1
      (hfinish.comp Computable.snd).to₂).of_eq
        (fun input => by
          simp [prodCodec, finish]
          cases A.parse input <;> rfl)
  · exact Primrec.nat_add.to_comp.comp
      (hA.2.2.comp Computable.fst) (hB.2.2.comp Computable.snd)

private theorem sum_effective {α : Type u} {β : Type v}
    [Primcodable α] [Primcodable β] (A : Codec α) (B : Codec β)
    (hA : A.Effective) (hB : B.Effective) : (sumCodec A B).Effective := by
  let encodeLeft : α → BitString := fun x => false :: A.encode x
  let encodeRight : β → BitString := fun y => true :: B.encode y
  have hEncodeLeft : Computable encodeLeft :=
    (Computable.list_cons.comp (Computable.const false) hA.1).of_eq
      (fun _ => rfl)
  have hEncodeRight : Computable encodeRight :=
    (Computable.list_cons.comp (Computable.const true) hB.1).of_eq
      (fun _ => rfl)
  let parseLeft : BitString → Option ((α ⊕ β) × BitString) := fun input =>
    (A.parse input).map fun result => (.inl result.1, result.2)
  let parseRight : BitString → Option ((α ⊕ β) × BitString) := fun input =>
    (B.parse input).map fun result => (.inr result.1, result.2)
  have hParseLeft : Computable parseLeft := by
    exact (Computable.option_map hA.2.1
      (((Computable.sumInl.comp Computable.fst).pair Computable.snd).comp
        Computable.snd).to₂).of_eq (fun input => by simp [parseLeft])
  have hParseRight : Computable parseRight := by
    exact (Computable.option_map hB.2.1
      (((Computable.sumInr.comp Computable.fst).pair Computable.snd).comp
        Computable.snd).to₂).of_eq (fun input => by simp [parseRight])
  refine ⟨?_, ?_, ?_⟩
  · exact (Computable.sumCasesOn Computable.id
      (hEncodeLeft.comp Computable.snd).to₂
      (hEncodeRight.comp Computable.snd).to₂).of_eq
        (fun value => by cases value <;> rfl)
  · let head : BitString → Option Bool := List.head?
    let tail : BitString → BitString := List.tail
    have hHead : Computable head := Primrec.list_head?.to_comp
    have hTail : Computable tail := Primrec.list_tail.to_comp
    have hBranch : Computable₂ fun input tag =>
        cond tag (parseRight (tail input)) (parseLeft (tail input)) := by
      exact (Computable.cond Computable.snd
        (hParseRight.comp (hTail.comp Computable.fst))
        (hParseLeft.comp (hTail.comp Computable.fst))).to₂
    exact (Computable.option_casesOn hHead (Computable.const none) hBranch).of_eq
      (fun input => by
        cases input with
        | nil => rfl
        | cons tag tail => cases tag <;> rfl)
  · let sizeLeft : α → Nat := fun x => A.size x + 1
    let sizeRight : β → Nat := fun y => B.size y + 1
    have hSizeLeft : Computable sizeLeft :=
      (Primrec.nat_add.to_comp.comp hA.2.2 (Computable.const 1)).of_eq (fun _ => rfl)
    have hSizeRight : Computable sizeRight :=
      (Primrec.nat_add.to_comp.comp hB.2.2 (Computable.const 1)).of_eq (fun _ => rfl)
    exact (Computable.sumCasesOn Computable.id
      (hSizeLeft.comp Computable.snd).to₂
      (hSizeRight.comp Computable.snd).to₂).of_eq
        (fun value => by cases value <;> rfl)

private theorem option_effective {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) : (optionCodec C).Effective := by
  let encodeSome : α → BitString := fun x => true :: C.encode x
  have hEncodeSome : Computable encodeSome :=
    (Computable.list_cons.comp (Computable.const true) hC.1).of_eq (fun _ => rfl)
  let parseSome : BitString → Option (Option α × BitString) := fun input =>
    (C.parse input).map fun result => (some result.1, result.2)
  have hParseSome : Computable parseSome := by
    exact (Computable.option_map hC.2.1
      (((Computable.option_some.comp Computable.fst).pair Computable.snd).comp
        Computable.snd).to₂).of_eq (fun input => by simp [parseSome])
  refine ⟨?_, ?_, ?_⟩
  · exact (Computable.option_casesOn Computable.id (Computable.const [false])
      (hEncodeSome.comp Computable.snd).to₂).of_eq
        (fun value => by cases value <;> rfl)
  · let head : BitString → Option Bool := List.head?
    let tail : BitString → BitString := List.tail
    have hHead : Computable head := Primrec.list_head?.to_comp
    have hTail : Computable tail := Primrec.list_tail.to_comp
    have hBranch : Computable₂ fun input tag =>
        cond tag (parseSome (tail input)) (some (none, tail input)) := by
      exact (Computable.cond Computable.snd
        (hParseSome.comp (hTail.comp Computable.fst))
        (Computable.option_some.comp
          ((Computable.const none).pair (hTail.comp Computable.fst)))).to₂
    exact (Computable.option_casesOn hHead (Computable.const none) hBranch).of_eq
      (fun input => by
        cases input with
        | nil => rfl
        | cons tag tail => cases tag <;> rfl)
  · let sizeSome : α → Nat := fun x => C.size x + 1
    have hSizeSome : Computable sizeSome :=
      (Primrec.nat_add.to_comp.comp hC.2.2 (Computable.const 1)).of_eq (fun _ => rfl)
    exact (Computable.option_casesOn Computable.id (Computable.const 1)
      (hSizeSome.comp Computable.snd).to₂).of_eq
        (fun value => by cases value <;> rfl)

private theorem encodeList_computable {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) : Computable (encodeList C) := by
  let step : BitString → α → BitString := fun acc x => true :: C.encode x ++ acc
  have hStep : Computable₂ step := by
    exact (Computable.list_append.comp
      (Computable.list_cons.comp (Computable.const true) (hC.1.comp Computable.snd))
      Computable.fst).to₂
  have hFold : Computable fun xs : List α => xs.reverse.foldl step [false] :=
    (list_foldl_computable step hStep [false]).comp Primrec.list_reverse.to_comp
  have fold_eq : ∀ xs : List α,
      xs.foldr (fun x acc => true :: C.encode x ++ acc) [false] = encodeList C xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldr_cons, encodeList]
        rw [ih]
  exact hFold.of_eq fun xs => by
    rw [List.foldl_reverse]
    simpa only [step] using fold_eq xs

private theorem listSize_computable {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) : Computable (listSize C) := by
  let step : Nat → α → Nat := fun acc x => C.size x + acc + 1
  have hStep : Computable₂ step := by
    have first : Computable fun input : Nat × α => C.size input.2 + input.1 :=
      Primrec.nat_add.to_comp.comp (hC.2.2.comp Computable.snd) Computable.fst
    exact (Primrec.nat_add.to_comp.comp first (Computable.const 1)).to₂
  have hFold : Computable fun xs : List α => xs.reverse.foldl step 1 :=
    (list_foldl_computable step hStep 1).comp Primrec.list_reverse.to_comp
  have fold_eq : ∀ xs : List α,
      xs.foldr (fun x acc => C.size x + acc + 1) 1 = listSize C xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.foldr_cons, listSize]
        rw [ih]
  exact hFold.of_eq fun xs => by
    rw [List.foldl_reverse]
    simpa only [step] using fold_eq xs

private abbrev ParseState (α : Type u) := Nat × (BitString × List α)

private def parseStep {α : Type u} (C : Codec α) :
    ParseState α → Option (List α × BitString) ⊕ ParseState α
  | (0, _) => .inl none
  | (_ + 1, ([], _)) => .inl none
  | (_ + 1, (false :: suffix, acc)) => .inl (some (acc.reverse, suffix))
  | (fuel + 1, (true :: input, acc)) =>
      match C.parse input with
      | none => .inl none
      | some (x, rest) => .inr (fuel, (rest, x :: acc))

private theorem parseStep_computable {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) : Computable (parseStep C) := by
  let input : ParseState α × Nat → BitString := fun ctx => ctx.1.2.1
  let acc : ParseState α × Nat → List α := fun ctx => ctx.1.2.2
  let fuel : ParseState α × Nat → Nat := fun ctx => ctx.2
  let tail : ParseState α × Nat → BitString := fun ctx => input ctx |>.tail
  let head : ParseState α × Nat → Option Bool := fun ctx => input ctx |>.head?
  have hInput : Computable input :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hAcc : Computable acc :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hFuel : Computable fuel := Computable.snd
  have hTail : Computable tail := Primrec.list_tail.to_comp.comp hInput
  have hHead : Computable head := Primrec.list_head?.to_comp.comp hInput
  let onFalse : ParseState α × Nat → Option (List α × BitString) ⊕ ParseState α :=
    fun ctx => .inl (some (acc ctx |>.reverse, tail ctx))
  have hOnFalse : Computable onFalse := by
    exact Computable.sumInl.comp (Computable.option_some.comp
      ((Primrec.list_reverse.to_comp.comp hAcc).pair hTail))
  let onTrue : ParseState α × Nat → Option (List α × BitString) ⊕ ParseState α :=
    fun ctx =>
      match C.parse (tail ctx) with
      | none => .inl none
      | some (x, rest) => .inr (fuel ctx, (rest, x :: acc ctx))
  have hOnTrue : Computable onTrue := by
    have hParsed : Computable fun ctx => C.parse (tail ctx) := hC.2.1.comp hTail
    have hSome : Computable₂ fun ctx (result : α × BitString) =>
        (Sum.inr (fuel ctx, (result.2, result.1 :: acc ctx)) :
          Option (List α × BitString) ⊕ ParseState α) := by
      have hCons : Computable fun pair : (ParseState α × Nat) × (α × BitString) =>
          pair.2.1 :: acc pair.1 :=
        Computable.list_cons.comp
          (Computable.fst.comp Computable.snd)
          (hAcc.comp Computable.fst)
      exact (Computable.sumInr.comp
        ((hFuel.comp Computable.fst).pair
          ((Computable.snd.comp Computable.snd).pair hCons))).to₂
    exact (Computable.option_casesOn hParsed (Computable.const (.inl none)) hSome).of_eq
      (fun ctx => by simp [onTrue]; cases C.parse (tail ctx) <;> rfl)
  have hPositive : Computable₂ fun state predecessor =>
      match state.2.1 with
      | [] => (.inl none : Option (List α × BitString) ⊕ ParseState α)
      | tag :: _ => cond tag (onTrue (state, predecessor)) (onFalse (state, predecessor)) := by
    have hTagBranch : Computable₂ fun ctx tag =>
        cond tag (onTrue ctx) (onFalse ctx) :=
      (Computable.cond Computable.snd
        (hOnTrue.comp Computable.fst) (hOnFalse.comp Computable.fst)).to₂
    exact (Computable.option_casesOn hHead (Computable.const (.inl none)) hTagBranch).of_eq
      (fun ctx => by
        obtain ⟨⟨stateFuel, bits, accumulator⟩, predecessor⟩ := ctx
        cases bits with
        | nil => rfl
        | cons tag rest => cases tag <;> rfl)
  exact (Computable.nat_casesOn Computable.fst (Computable.const (.inl none))
    hPositive).of_eq fun state => by
      obtain ⟨fuel, input, acc⟩ := state
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases input with
          | nil => rfl
          | cons tag rest =>
              cases tag
              · rfl
              · cases C.parse rest <;> rfl

private def parseResult {α : Type u} (C : Codec α) (state : ParseState α) :
    Option (List α × BitString) :=
  (parseListAux C state.1 state.2.1).map fun result =>
    (state.2.2.reverse ++ result.1, result.2)

private theorem parseStep_terminates {α : Type u} (C : Codec α) (state : ParseState α) :
    parseResult C state ∈
      PFun.fix (fun state => Part.some (parseStep C state)) state := by
  obtain ⟨fuel, input, acc⟩ := state
  induction fuel generalizing input acc with
  | zero =>
      apply PFun.mem_fix_iff.2
      exact Or.inl (by simp [parseStep, parseResult, parseListAux])
  | succ fuel ih =>
      cases input with
      | nil =>
          apply PFun.mem_fix_iff.2
          exact Or.inl (by simp [parseStep, parseResult, parseListAux])
      | cons tag input =>
          cases tag with
          | false =>
              apply PFun.mem_fix_iff.2
              exact Or.inl (by simp [parseStep, parseResult, parseListAux])
          | true =>
              cases hp : C.parse input with
              | none =>
                  apply PFun.mem_fix_iff.2
                  exact Or.inl (by simp [parseStep, parseResult, parseListAux, hp])
              | some result =>
                  obtain ⟨x, rest⟩ := result
                  apply PFun.mem_fix_iff.2
                  refine Or.inr ⟨(fuel, (rest, x :: acc)), by simp [parseStep, hp], ?_⟩
                  have heq :
                      parseResult C (fuel + 1, (true :: input, acc)) =
                        parseResult C (fuel, (rest, x :: acc)) := by
                    cases hr : parseListAux C fuel rest <;>
                      simp [parseResult, parseListAux, hp, hr, List.reverse_cons,
                        List.append_assoc]
                  rw [heq]
                  exact ih rest (x :: acc)

private theorem parseListAux_computable {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) : Computable₂ (parseListAux C) := by
  have hfix : Partrec (PFun.fix (fun state : ParseState α =>
      Part.some (parseStep C state))) :=
    Partrec.fix (parseStep_computable C hC).partrec
  have hResult : Computable (parseResult C) :=
    hfix.of_eq_tot (parseStep_terminates C)
  have hState : Computable (fun input : Nat × BitString =>
      (input.1, (input.2, ([] : List α)))) :=
    Computable.fst.pair (Computable.snd.pair (Computable.const []))
  exact (hResult.comp hState).to₂.of_eq fun input => by
    obtain ⟨fuel, bits⟩ := input
    cases hp : parseListAux C fuel bits <;> simp [parseResult, hp]

private theorem parseList_computable {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) : Computable (parseList C) := by
  have hFuel : Computable fun input : BitString => input.length + 1 :=
    Primrec.nat_add.to_comp.comp Computable.list_length (Computable.const 1)
  exact (parseListAux_computable C hC).comp hFuel Computable.id

private theorem list_effective {α : Type u} [Primcodable α]
    (C : Codec α) (hC : C.Effective) : (listCodec C).Effective :=
  ⟨encodeList_computable C hC, parseList_computable C hC, listSize_computable C hC⟩

private def decodeVector {α : Type u} [Primcodable α] (n : Nat) (xs : List α) :
    Option (List.Vector α n) :=
  Encodable.decode₂ (List.Vector α n) (Encodable.encode xs)

private theorem decodeVector_computable {α : Type u} [Primcodable α] (n : Nat) :
    Computable (decodeVector (α := α) n) :=
  Primrec.decode₂.to_comp.comp Primrec.encode.to_comp

private theorem decodeVector_eq {α : Type u} [Primcodable α] (n : Nat) (xs : List α) :
    decodeVector n xs = if h : xs.length = n then some ⟨xs, h⟩ else none := by
  by_cases h : xs.length = n
  · simp only [h, ↓reduceDIte]
    have hd := Encodable.decode₂_encode (⟨xs, h⟩ : List.Vector α n)
    change decodeVector n xs = some ⟨xs, h⟩ at hd
    exact hd
  · simp only [h, ↓reduceDIte]
    cases hd : decodeVector n xs with
    | none => rfl
    | some value =>
        exfalso
        have he := Encodable.decode₂_eq_some.mp hd
        change Encodable.encode value.1 = Encodable.encode xs at he
        have hv : value.1 = xs := Encodable.encode_injective he
        exact h (by simpa [hv] using value.2)

private theorem vector_effective {α : Type u} [Primcodable α]
    (C : Codec α) (n : Nat) (hC : C.Effective) : (vectorCodec C n).Effective := by
  have hList := list_effective C hC
  refine ⟨hList.1.comp Computable.vector_toList, ?_,
    hList.2.2.comp Computable.vector_toList⟩
  let finish : List α × BitString → Option (List.Vector α n × BitString) := fun result =>
    (decodeVector n result.1).map fun xs => (xs, result.2)
  have hFinish : Computable finish := by
    exact (Computable.option_map
      ((decodeVector_computable (α := α) n).comp Computable.fst)
      (Computable.snd.pair (Computable.snd.comp Computable.fst)).to₂).of_eq
        (fun result => by simp [finish])
  exact (Computable.option_bind hList.2.1
    (hFinish.comp Computable.snd).to₂).of_eq fun input => by
      simp [vectorCodec, finish, decodeVector_eq]

private theorem finFunction_effective {α : Type u} [Primcodable α]
    (C : Codec α) (n : Nat) (hC : C.Effective) : (finFunctionCodec C n).Effective := by
  have hToVector : Computable ((Equiv.vectorEquivFin α n).symm) := by
    exact Computable.vector_ofFn'
  have hToFunction : Computable (Equiv.vectorEquivFin α n) := by
    apply Computable.encode_iff.mp
    exact Computable.encode.of_eq fun vector => by
      simp [Equiv.vectorEquivFin, Encodable.encode_ofEquiv]
  exact equiv_effective (Equiv.vectorEquivFin α n).symm (vectorCodec C n)
    hToVector hToFunction (vector_effective C n hC)

private def decodeFin (n i : Nat) : Option (Fin n) :=
  Encodable.decode₂ (Fin n) (Encodable.encode i)

private theorem decodeFin_computable (n : Nat) : Computable (decodeFin n) :=
  Primrec.decode₂.to_comp.comp Primrec.encode.to_comp

private theorem decodeFin_eq (n i : Nat) :
    decodeFin n i = if h : i < n then some ⟨i, h⟩ else none := by
  by_cases h : i < n
  · simp only [h, ↓reduceDIte]
    have hd := Encodable.decode₂_encode (⟨i, h⟩ : Fin n)
    change decodeFin n i = some ⟨i, h⟩ at hd
    exact hd
  · simp only [h, ↓reduceDIte]
    cases hd : decodeFin n i with
    | none => rfl
    | some value =>
        exfalso
        have he := Encodable.decode₂_eq_some.mp hd
        change Encodable.encode value.val = Encodable.encode i at he
        have hv : value.val = i := Encodable.encode_injective he
        exact h (by simpa [hv] using value.isLt)

private theorem fin_effective (n : Nat) : (finCodec n).Effective := by
  have hNat := Lax58Proofs.PrimitiveCodecs.primitiveCodecs_valid.nat_effective
  refine ⟨hNat.1.comp Primrec.fin_val.to_comp, ?_,
    hNat.2.2.comp Primrec.fin_val.to_comp⟩
  let finish : Nat × BitString → Option (Fin n × BitString) := fun result =>
    (decodeFin n result.1).map fun i => (i, result.2)
  have hFinish : Computable finish := by
    exact (Computable.option_map
      ((decodeFin_computable n).comp Computable.fst)
      (Computable.snd.pair (Computable.snd.comp Computable.fst)).to₂).of_eq
        (fun result => by simp [finish])
  exact (Computable.option_bind hNat.2.1
    (hFinish.comp Computable.snd).to₂).of_eq fun input => by
      simp [finCodec, finish, decodeFin_eq]

/--
---
conclusion: Lax58.EffectiveCombinators.closure
---
-/
theorem closure : Closure where
  equiv := equiv_effective
  prod := prod_effective
  sum := sum_effective
  option := option_effective
  list := list_effective
  vector := vector_effective
  finFunction := finFunction_effective
  fin := fin_effective

end Lax58Proofs.EffectiveCombinators
