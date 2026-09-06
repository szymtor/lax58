import Lax58.CertifiedDerivationElab
import Lax58.RamComplexity

/-!
---
title: Automatic RAM encoding selection (elaboration infrastructure)
type: elaboration infrastructure
---

This thin frontend expands a mathematical function and two resource bounds
into the encoding-explicit RAM predicate. It reuses the closed constructor
registry, adding only the fixed list and product presentation combinators.
Subtypes erase proofs and finite families keep their intrinsic order.
No presentation instances, arbitrary field encoders, or caller-supplied
agreement witnesses participate in resolution.

Natural and Boolean outputs have fixed one-word conventions. All other
supported outputs use the selected structural arena. `inputMagnitude x`
uses exactly the same input resolver as `RamComputableWithin`.
-/

namespace Lax58.RamComplexityElab

open Lean Meta Elab Term
open Lax58.StructuralPresentation Lax58.StructuralCombinators
open Lax58.CertifiedDerivation Lax58.CertifiedDerivationElab
open Lax58.RamComplexity

universe u

private def subtypeRaw {α : Type u} (raw : α → Raw) (p : α → Prop)
    (x : Subtype p) : Raw := raw x.val

private def familyRaw {n : Nat} {α : Fin n → Type u}
    (raw : (i : Fin n) → α i → Raw) (x : (i : Fin n) → α i) : Raw :=
  Raw.fields (List.ofFn fun i => raw i (x i))

/-- Resolve expressions, never pretty-printed syntax or typeclass instances. -/
private partial def resolveInput (type : Expr) : TermElabM Expr := do
  let type ← instantiateMVars type
  let type ← instantiateMVars (← whnf type)
  if type.hasExprMVar then
    -- Binder-local numeral/typeclass constraints may be solved only after
    -- the surrounding declaration has finished elaborating its signature.
    tryPostpone
    throwError "RAM encoding selection needs a fully determined input/output type, got {type}"
  if type.isConstOf ``Nat then
    return mkConst ``StructuralCombinators.nat
  if type.isAppOfArity ``List 1 then
    return ← mkAppM ``StructuralCombinators.list #[← resolveInput type.appArg!]
  if type.isAppOfArity ``Prod 2 then
    let args := type.getAppArgs
    let left ← resolveInput args[0]!
    let right ← resolveInput args[1]!
    return ← mkAppM ``StructuralCombinators.prod #[left, right]
  if type.isAppOfArity ``Subtype 2 then
    let args := type.getAppArgs
    let base ← mkAppM ``Presentation.toRaw #[← resolveInput args[0]!]
    let raw ← mkAppM ``subtypeRaw #[base, args[1]!]
    return ← mkAppM ``presentationOf #[raw]
  if let .forallE name domain body bi := type then
    let domain ← whnf domain
    if domain.isAppOfArity ``Fin 1 then
      return ← withLocalDecl name bi domain fun i => do
        let raw ← mkAppM ``Presentation.toRaw #[← resolveInput (body.instantiate1 i)]
        let family ← mkAppM ``familyRaw #[← mkLambdaFVars #[i] raw]
        mkAppM ``presentationOf #[family]
  let witness ← resolveCertifiedField type
  let raw ← mkAppM ``CertifiedFieldEncoding.toRaw #[witness]
  mkAppM ``presentationOf #[raw]

private def resolveOutput (type : Expr) : TermElabM Expr := do
  let type ← whnf type
  if type.isConstOf ``Nat then return mkConst ``natOutput
  if type.isConstOf ``Bool then return mkConst ``boolOutput
  let raw ← mkAppM ``Presentation.toRaw #[← resolveInput type]
  mkAppM ``arenaOutput #[raw]

elab "RamComputableWithin " f:term:max time:term:max words:term:max : term => do
  let f ← elabTerm f none
  synthesizeSyntheticMVarsNoPostponing
  let type ← whnf (← inferType f)
  let .forallE _ domain body _ := type
    | throwError "RamComputableWithin expects a function"
  if body.hasLooseBVars then
    throwError "RamComputableWithin expects a nondependent result type; bundle dependent data into an input datatype"
  let input ← resolveInput domain
  let output ← resolveOutput body
  let boundType ← mkArrow domain (mkConst ``Nat)
  let time ← elabTermEnsuringType time (some boundType)
  let words ← elabTermEnsuringType words (some boundType)
  mkAppM ``RamComputableWithinUsing #[input, output, f, time, words]

elab "inputMagnitude " x:term:max : term => do
  let x ← elabTerm x none
  synthesizeSyntheticMVarsNoPostponing
  let input ← resolveInput (← inferType x)
  mkAppM ``inputMagnitudeUsing #[input, x]

end Lax58.RamComplexityElab
