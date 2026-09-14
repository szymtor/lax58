import Lean.Elab.Match
import Lax560851.StructuralCombinators

/-!
---
title: Unrestricted structural folds (elaboration infrastructure)
type: elaboration infrastructure
---

The `structural% value using recursiveCall` term derives the structural fold
of an inductive value from its declaration. Constructor names and explicit
constructor-field order are read from the declaration; direct recursive fields
and finite families of recursive fields are folded recursively. Implicit
indices and witnesses are erased. Only genuinely primitive explicit fields
require an explicit `FieldEncoding`.

`FieldEncoding` and the folds in this module are low-level elaboration
infrastructure, not structurality certificates. Reduction equations using
unrestricted field instances do not establish the provenance of those fields.
`Lax560851.CertifiedDerivationElab` supplies the separate closed derivation path and
does not consult this module's instances.
-/

namespace Lax560851.StructuralDerivation

open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators

universe u

/-- Low-level encoding of a non-recursive constructor field. Possessing an
instance alone confers no complexity-theoretic status. -/
class FieldEncoding (α : Type u) where
  toRaw : α → Raw

/-- Apply the selected primitive-field encoding. -/
def fieldRaw {α : Type u} [P : FieldEncoding α] (x : α) : Raw :=
  P.toRaw x

instance : FieldEncoding Nat where
  toRaw := Raw.nat

instance {n : Nat} : FieldEncoding (Fin n) where
  toRaw i := Raw.nat i.val

/-- Finite function fields are represented by their values in intrinsic
index order. This determines represented content but makes no claim about the
cost of evaluating the Lean function. -/
instance {n : Nat} {α : Type u} [P : FieldEncoding α] :
    FieldEncoding (Fin n → α) where
  toRaw f := Raw.fields (List.ofFn fun i => P.toRaw (f i))

open Lean Meta Elab Term
open Lean.Parser.Term

private def isDirectRecursiveField (inductiveName : Name) (type : Expr) : Bool :=
  type.getAppFn.constName? == some inductiveName

private def isFiniteRecursiveFamily (inductiveName : Name) (type : Expr) : Bool :=
  match type with
  | .forallE _ domain body _ =>
      domain.getAppFn.constName? == some ``Fin &&
        body.getAppFn.constName? == some inductiveName
  | _ => false

private def structuralAlternative (indInfo : InductiveVal)
    (recursiveCall : TSyntax `term) (constructorName : Name) :
    TermElabM (TSyntax ``matchAlt) := do
  let constructor ← getConstInfoCtor constructorName
  forallTelescopeReducing constructor.type fun arguments _ => do
    let mut patternArguments := #[]
    for _ in *...indInfo.numParams do
      patternArguments := patternArguments.push (← `(_))
    let mut fields : Array (Ident × Expr) := #[]
    for i in *...constructor.numFields do
      let argument := arguments[indInfo.numParams + i]!
      let declaration ← argument.fvarId!.getDecl
      if declaration.binderInfo.isExplicit then
        let fieldName := mkIdent (← mkFreshUserName `field)
        fields := fields.push (fieldName, declaration.type)
        patternArguments := patternArguments.push fieldName
      else
        -- Intrinsic indices and dependent witnesses are implicit constructor
        -- arguments. They remain available to dependent pattern matching, but
        -- do not duplicate data already fixed by the indexed value and its
        -- explicit fields. A downstream `Presentation.Lawful` proof remains
        -- responsible for showing that this erasure loses no value.
        patternArguments := patternArguments.push (← `(_))
    let mut encodedFields : TSyntax `term ← `([])
    for (fieldName, fieldType) in fields.reverse do
      encodedFields ←
        if isDirectRecursiveField indInfo.name fieldType then
          `(($recursiveCall:term) $fieldName:ident :: $encodedFields:term)
        else if isFiniteRecursiveFamily indInfo.name fieldType then
          `(List.ofFn (fun i => ($recursiveCall:term) ($fieldName:ident i)) ++
              $encodedFields:term)
        else
          `(Lax560851.StructuralDerivation.fieldRaw $fieldName:ident ::
              $encodedFields:term)
    let tag := constructor.name.eraseMacroScopes.getString!
    let rightHandSide ←
      `(Lax560851.StructuralCombinators.Raw.constructor $(quote tag)
          $encodedFields:term)
    `(matchAltExpr|
      | @$(mkIdent constructor.name):ident $patternArguments:term* =>
          $rightHandSide:term)

/-- Derive one complete constructor-structural match. The caller supplies the
recursive function application so ordinary Lean termination checking remains
authoritative. -/
elab "structural% " value:term " using " recursiveCall:term : term => do
  let valueExpression ← elabTerm value none
  let valueType ← whnf (← inferType valueExpression)
  let some inductiveName := valueType.getAppFn.constName?
    | throwError "structural% expects an inductive value, got {valueType}"
  let indInfo ← getConstInfoInduct inductiveName
  let alternatives := (← indInfo.ctors.mapM
    (structuralAlternative indInfo recursiveCall)).toArray
  let generated ← `(match $value:term with $alternatives:matchAlt*)
  elabTerm generated (some (mkConst ``Raw))

/-- Derive a complete constructor-structural function from its expected
single-argument function type. Unlike an inner `match`, the generated
constructor clauses remain visible to Lean's equation compiler, which is
needed for nested recursive fields such as `Fin n → Tree`.

Example:
```
def treeRaw : Tree → Raw :=
  structuralFun% using treeRaw
```
-/
elab "structuralFun% " "using " recursiveCall:term : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let functionType ← whnf expectedType
  let .forallE _ valueType _resultType _ := functionType
    | throwError
        "structuralFun% expects a single-argument function type, got {expectedType}"
  let valueType ← whnf valueType
  let some inductiveName := valueType.getAppFn.constName?
    | throwError
        "structuralFun% expects an inductive argument type, got {valueType}"
  let indInfo ← getConstInfoInduct inductiveName
  let alternatives := (← indInfo.ctors.mapM
    (structuralAlternative indInfo recursiveCall)).toArray
  let generated ← `(fun $alternatives:matchAlt*)
  elabTerm generated (some expectedType)

end Lax560851.StructuralDerivation
