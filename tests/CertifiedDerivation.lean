import Lax58.CertifiedDerivationElab
import Lax58.StructuralDerivation

/- Run from concepts/: lake env lean ../tests/CertifiedDerivation.lean -/

open Lax58.StructuralPresentation Lax58.StructuralCombinators
open Lax58.CertifiedDerivation

set_option autoImplicit false

namespace CertifiedDerivationTests

inductive Leaf where
  | value (n : Nat)

derive_certified_encoding leafEncoding indexed : Leaf

inductive Branch where
  | node (label : Leaf) (children : Fin 2 → Branch)

derive_certified_encoding branchEncoding indexed : Branch

example (n : Nat) : leafEncoding (.value n) = Raw.constructor "value" [Raw.nat n] := rfl
example : leafEncoding.Laws := leafEncoding.certified.checked
example : branchEncoding.Laws := branchEncoding.certified.checked

-- Low-level overrides cannot change primitive or transitively encoded fields.
instance : Lax58.StructuralDerivation.FieldEncoding Nat where
  toRaw _ := Raw.nat 42

instance : Lax58.StructuralDerivation.FieldEncoding Leaf where
  toRaw _ := Raw.nat 43

example : Lax58.StructuralDerivation.fieldRaw (7 : Nat) = Raw.nat 42 := rfl
example : Lax58.StructuralDerivation.fieldRaw (Leaf.value 7) = Raw.nat 43 := rfl

derive_certified_encoding leafEncodingAgain indexed : Leaf
derive_certified_encoding branchEncodingAgain indexed : Branch

example (n : Nat) : leafEncodingAgain (.value n) = Raw.constructor "value" [Raw.nat n] := rfl
example (n : Nat) (children : Fin 2 → Branch) :
    branchEncodingAgain (.node (.value n) children) =
      Raw.constructor "node" (Raw.constructor "value" [Raw.nat n] ::
        List.ofFn fun i => branchEncodingAgain (children i)) := rfl

inductive Wrapped where
  | value (n : {n : Nat // n > 0}) (xs : Fin 2 → Leaf)

derive_certified_encoding wrappedEncoding indexed : Wrapped
example : wrappedEncoding.Laws := wrappedEncoding.certified.checked
example (n : {n : Nat // n > 0}) (xs : Fin 2 → Leaf) :
    wrappedEncoding (.value n xs) = Raw.constructor "value"
      [Raw.nat n.val, Raw.fields (List.ofFn fun i => leafEncoding (xs i))] := rfl

inductive Dependent where
  | values (n : Nat) (xs : (i : Fin n) → Fin (i.val + 1))

derive_certified_encoding dependentEncoding indexed : Dependent
example : dependentEncoding.Laws := dependentEncoding.certified.checked

inductive Bad where
  | function (advice : Nat → Nat)

instance : Lax58.StructuralDerivation.FieldEncoding (Nat → Nat) where
  toRaw _ := Raw.nat 42

/--
error: CertifiedDerivationTests.Bad.function, field advice✝: unsupported certified field type ℕ →
  ℕ; expected Nat, Fin, a proof-erased subtype, a finite family, or an earlier constructor-certified datatype
-/
#guard_msgs in
derive_certified_encoding badEncoding indexed : Bad

-- A failed command must leave neither an encoder nor a registered witness.
/-- error: Unknown identifier `badEncoding` -/
#guard_msgs in
#check badEncoding

/-- error: Unknown identifier `badEncoding.certified` -/
#guard_msgs in
#check badEncoding.certified

inductive Unregistered where
  | value (n : Nat)

instance : Lax58.StructuralDerivation.FieldEncoding Unregistered where
  toRaw _ := Raw.nat 99

-- Even a well-typed, publicly packaged agreement cannot register a datatype.
def unregisteredAgreement :
    CertifiedFieldEncoding Unregistered (fun _ => Raw.nat 99) True :=
  CertifiedFieldEncoding.ofLaws (fun _ => Raw.nat 99) True.intro

inductive Holder where
  | value (payload : Unregistered)

/--
error: CertifiedDerivationTests.Holder.value, field payload✝: unsupported certified field type Unregistered; expected Nat, Fin, a proof-erased subtype, a finite family, or an earlier constructor-certified datatype
-/
#guard_msgs in
derive_certified_encoding holderEncoding indexed : Holder

inductive Hidden where
  | value {advice : Nat → Nat} (n : Nat)

/--
error: CertifiedDerivationTests.Hidden.value: unsupported implicit field advice✝: ℕ → ℕ
-/
#guard_msgs in
derive_certified_encoding hiddenEncoding indexed : Hidden

inductive ErasedPayload where
  | value {advice : Nat} (n : Nat)

/--
error: CertifiedDerivationTests.ErasedPayload.value: implicit field advice✝ is not an intrinsic index
-/
#guard_msgs in
derive_certified_encoding erasedEncoding indexed : ErasedPayload

/--
error: Invalid `⟨...⟩` notation: Constructor for `Lax58.CertifiedDerivation.CertifiedFieldEncoding` is marked as private
-/
#guard_msgs in
def forged : CertifiedFieldEncoding Nat Raw.nat CertifiedFieldEncoding.nat.Laws :=
  ⟨fun _ => Raw.nat 42, rfl, fun _ => rfl⟩

/--
error: invalid {...} notation, constructor for `CertifiedFieldEncoding` is marked as private
-/
#guard_msgs in
def forgedUpdate : CertifiedFieldEncoding Nat Raw.nat CertifiedFieldEncoding.nat.Laws :=
  { CertifiedFieldEncoding.nat with toRaw := fun _ => Raw.nat 42 }

-- Constructor privacy is not a proof boundary: tactics can access it.
-- The indexed specification and equality obligation must reject this attack.
example : CertifiedFieldEncoding Nat Raw.nat CertifiedFieldEncoding.nat.Laws := by
  fail_if_success
    constructor
    case toRaw => exact fun _ => Raw.nat 42
    case agrees => rfl
  exact CertifiedFieldEncoding.nat

example (P : CertifiedFieldEncoding Nat Raw.nat CertifiedFieldEncoding.nat.Laws) :
    P.toRaw 7 ≠ Raw.nat 42 := by
  intro h
  have hn : (7 : Nat) = 42 := Raw.nat.inj ((congrFun P.agrees 7).symm.trans h)
  omega

-- A record for a different specification is not evidence for Raw.nat and is
-- not a registered datatype certificate. The command never consumes it.
def unrelatedSpecification : CertifiedFieldEncoding Nat (fun _ => Raw.nat 42) True := by
  constructor
  case toRaw => exact fun _ => Raw.nat 42
  case agrees => rfl
  case checked => exact True.intro

-- Closed resolution still works after rejected commands.
derive_certified_encoding afterRejections indexed : Leaf
example (n : Nat) : afterRejections (.value n) = Raw.constructor "value" [Raw.nat n] := rfl

end CertifiedDerivationTests
