import Lax58.WordArena

namespace Lax58Proofs.WordArena
open Lax58.StructuralPresentation
open Lax58.WordArena

universe u

private theorem encodeInto_size (raw : Raw) (memory : WordMemory) :
    (encodeInto raw memory).1.size = memory.size + 3 * raw.nodes := by
  induction raw generalizing memory with
  | nat payload => simp [encodeInto, Raw.nodes]
  | pair left right ihl ihr =>
      simp [encodeInto, ihl, ihr, Raw.nodes]
      omega

private theorem encodeRaw_memoryWordsAux (raw : Raw) :
    (encodeRaw raw).memoryWords = 3 * raw.nodes := by
  simpa [encodeRaw, WordImage.memoryWords] using encodeInto_size raw #[]

private structure Extends (small large : WordMemory) : Prop where
  size_le : small.size ≤ large.size
  get_eq : ∀ i, i < small.size → large[i]? = small[i]?

private theorem extends_refl (memory : WordMemory) : Extends memory memory :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

private theorem extends_trans {a b c : WordMemory} (hab : Extends a b) (hbc : Extends b c) :
    Extends a c := by
  refine ⟨Nat.le_trans hab.size_le hbc.size_le, ?_⟩
  intro i hi
  rw [hbc.get_eq i (Nat.lt_of_lt_of_le hi hab.size_le), hab.get_eq i hi]

private theorem extends_push (memory : WordMemory) (x : Nat) : Extends memory (memory.push x) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  rw [Array.getElem?_eq_getElem (by simpa using Nat.lt_succ_of_lt hi),
    Array.getElem?_eq_getElem hi]
  congr 1
  exact Array.getElem_push_lt hi

private theorem get_push_eq (memory : WordMemory) (x : Nat) :
    (memory.push x)[memory.size]? = some x := by
  rw [Array.getElem?_eq_getElem (by simp)]
  congr 1
  exact Array.getElem_push_eq

private theorem triple_get_zero (memory : WordMemory) (x y z : Nat) :
    (((memory.push x).push y).push z)[memory.size]? = some x := by
  have h := (extends_trans (extends_push (memory.push x) y)
    (extends_push ((memory.push x).push y) z)).get_eq memory.size (by simp)
  rw [h]
  exact get_push_eq memory x

private theorem triple_get_one (memory : WordMemory) (x y z : Nat) :
    (((memory.push x).push y).push z)[memory.size + 1]? = some y := by
  have h := (extends_push ((memory.push x).push y) z).get_eq (memory.size + 1) (by simp)
  rw [h]
  simpa using get_push_eq (memory.push x) y

private theorem triple_get_two (memory : WordMemory) (x y z : Nat) :
    (((memory.push x).push y).push z)[memory.size + 2]? = some z := by
  simpa using get_push_eq ((memory.push x).push y) z

private theorem encodeInto_extends (raw : Raw) (memory : WordMemory) :
    Extends memory (encodeInto raw memory).1 := by
  induction raw generalizing memory with
  | nat payload =>
      exact extends_trans (extends_trans (extends_push memory _) (extends_push _ _))
        (extends_push _ _)
  | pair left right ihl ihr =>
      exact extends_trans (extends_trans (ihl memory) (ihr _))
        (extends_trans (extends_trans (extends_push _ _) (extends_push _ _))
          (extends_push _ _))

private theorem valid_mono {small large : WordMemory} (h : Extends small large)
    {oldRoot newRoot address : Nat} (ha : (WordImage.mk small oldRoot).ValidAddress address) :
    (WordImage.mk large newRoot).ValidAddress address := by
  exact ⟨ha.1, Nat.lt_of_lt_of_le ha.2 h.size_le⟩

private theorem represents_mono {small large : WordMemory} (h : Extends small large)
    {oldRoot newRoot address : Nat} {raw : Raw}
    (hr : (WordImage.mk small oldRoot).Represents address raw) :
    (WordImage.mk large newRoot).Represents address raw := by
  induction hr with
  | nat address_valid tag value padding =>
      have hbound := address_valid.2
      simp only [WordImage.memoryWords] at hbound
      apply WordImage.Represents.nat (valid_mono h address_valid)
      · change large[_]? = _
        rw [h.get_eq _ (by omega)]
        exact tag
      · change large[_]? = _
        rw [h.get_eq _ (by omega)]
        exact value
      · change large[_]? = _
        rw [h.get_eq _ hbound]
        exact padding
  | pair address_valid tag left_reference right_reference left_value right_value ihl ihr =>
      have hbound := address_valid.2
      simp only [WordImage.memoryWords] at hbound
      apply WordImage.Represents.pair (valid_mono h address_valid)
      · change large[_]? = _
        rw [h.get_eq _ (by omega)]
        exact tag
      · change large[_]? = _
        rw [h.get_eq _ (by omega)]
        exact left_reference
      · change large[_]? = _
        rw [h.get_eq _ hbound]
        exact right_reference
      · exact ihl
      · exact ihr

private theorem encodeInto_represents (raw : Raw) (memory : WordMemory)
    (aligned : memory.size % 3 = 0) :
    let out := encodeInto raw memory
    (WordImage.mk out.1 out.2).Represents out.2 raw := by
  induction raw generalizing memory with
  | nat payload =>
      apply WordImage.Represents.nat
      · simp [encodeInto, WordImage.ValidAddress, WordImage.memoryWords, aligned]
      · exact triple_get_zero memory _ _ _
      · exact triple_get_one memory _ _ _
      · exact triple_get_two memory _ _ _
  | pair left right ihl ihr =>
      generalize hleft : encodeInto left memory = leftOut
      obtain ⟨leftMemory, leftAddress⟩ := leftOut
      generalize hright : encodeInto right leftMemory = rightOut
      obtain ⟨rightMemory, rightAddress⟩ := rightOut
      have leftSize := encodeInto_size left memory
      rw [hleft] at leftSize
      have rightSize := encodeInto_size right leftMemory
      rw [hright] at rightSize
      have leftAligned : leftMemory.size % 3 = 0 := by
        rw [leftSize]
        omega
      have rightAligned : rightMemory.size % 3 = 0 := by
        rw [rightSize]
        omega
      have hLeftRep := ihl memory aligned
      rw [hleft] at hLeftRep
      have hRightRep := ihr leftMemory leftAligned
      rw [hright] at hRightRep
      have hLeftRight : Extends leftMemory rightMemory := by
        simpa [hright] using encodeInto_extends right leftMemory
      let finalMemory := rightMemory.push WordImage.pairTag |>.push leftAddress |>.push rightAddress
      have hRightFinal : Extends rightMemory finalMemory :=
        extends_trans (extends_trans (extends_push _ _) (extends_push _ _)) (extends_push _ _)
      have hLeftFinal : Extends leftMemory finalMemory := extends_trans hLeftRight hRightFinal
      simp only [encodeInto, hleft, hright]
      change (WordImage.mk finalMemory rightMemory.size).Represents rightMemory.size (.pair left right)
      apply WordImage.Represents.pair
      · simp [WordImage.ValidAddress, WordImage.memoryWords, finalMemory, rightAligned]
      · exact triple_get_zero rightMemory _ _ _
      · exact triple_get_one rightMemory _ _ _
      · exact triple_get_two rightMemory _ _ _
      · exact represents_mono hLeftFinal hLeftRep
      · exact represents_mono hRightFinal hRightRep

private theorem encodeRaw_representsAux (raw : Raw) :
    (encodeRaw raw).Represents (encodeRaw raw).root raw := by
  simpa [encodeRaw] using encodeInto_represents raw #[] (by decide)

private theorem child_mono {small large : WordMemory} (h : Extends small large)
    {oldRoot newRoot parent child : Nat}
    (hc : (WordImage.mk small oldRoot).ChildAddress parent child) :
    (WordImage.mk large newRoot).ChildAddress parent child := by
  cases hc with
  | left parent_valid child_valid tag reference =>
      have hbound := parent_valid.2
      simp only [WordImage.memoryWords] at hbound
      apply WordImage.ChildAddress.left (valid_mono h parent_valid) (valid_mono h child_valid)
      · change large[_]? = _
        rw [h.get_eq _ (by omega)]
        exact tag
      · change large[_]? = _
        rw [h.get_eq _ (by omega)]
        exact reference
  | right parent_valid child_valid tag reference =>
      have hbound := parent_valid.2
      simp only [WordImage.memoryWords] at hbound
      apply WordImage.ChildAddress.right (valid_mono h parent_valid) (valid_mono h child_valid)
      · change large[_]? = _
        rw [h.get_eq _ (by omega)]
        exact tag
      · change large[_]? = _
        rw [h.get_eq _ hbound]
        exact reference

private theorem reachable_mono {small large : WordMemory} (h : Extends small large)
    {oldRoot newRoot source address : Nat}
    (hr : (WordImage.mk small oldRoot).ReachableFrom source address) :
    (WordImage.mk large newRoot).ReachableFrom source address := by
  induction hr with
  | root => exact WordImage.ReachableFrom.root
  | child parent_reachable child_address ih =>
      exact WordImage.ReachableFrom.child ih (child_mono h child_address)

private theorem reachable_trans {I : WordImage} {a b c : Nat}
    (hab : I.ReachableFrom a b) (hbc : I.ReachableFrom b c) : I.ReachableFrom a c := by
  induction hbc with
  | root => exact hab
  | child _ child_address ih => exact WordImage.ReachableFrom.child ih child_address

private theorem represents_valid {I : WordImage} {address : Nat} {raw : Raw}
    (h : I.Represents address raw) : I.ValidAddress address := by
  cases h with
  | nat address_valid => exact address_valid
  | pair address_valid => exact address_valid

private theorem encodeInto_reachable (raw : Raw) (memory : WordMemory)
    (aligned : memory.size % 3 = 0) :
    let out := encodeInto raw memory
    ∀ address, memory.size ≤ address → (WordImage.mk out.1 out.2).ValidAddress address →
      (WordImage.mk out.1 out.2).ReachableFrom out.2 address := by
  induction raw generalizing memory with
  | nat payload =>
      simp only [encodeInto]
      intro address lower valid
      have upper := valid.2
      simp only [WordImage.memoryWords, Array.size_push] at upper
      have : address = memory.size := by omega
      subst address
      exact WordImage.ReachableFrom.root
  | pair left right ihl ihr =>
      generalize hleft : encodeInto left memory = leftOut
      obtain ⟨leftMemory, leftAddress⟩ := leftOut
      generalize hright : encodeInto right leftMemory = rightOut
      obtain ⟨rightMemory, rightAddress⟩ := rightOut
      have leftSize := encodeInto_size left memory
      rw [hleft] at leftSize
      have rightSize := encodeInto_size right leftMemory
      rw [hright] at rightSize
      have leftAligned : leftMemory.size % 3 = 0 := by rw [leftSize]; omega
      have rightAligned : rightMemory.size % 3 = 0 := by rw [rightSize]; omega
      have hLeftRight : Extends leftMemory rightMemory := by
        simpa [hright] using encodeInto_extends right leftMemory
      let finalMemory := rightMemory.push WordImage.pairTag |>.push leftAddress |>.push rightAddress
      have hRightFinal : Extends rightMemory finalMemory :=
        extends_trans (extends_trans (extends_push _ _) (extends_push _ _)) (extends_push _ _)
      have hLeftFinal : Extends leftMemory finalMemory := extends_trans hLeftRight hRightFinal
      have hLeftReach := ihl memory aligned
      rw [hleft] at hLeftReach
      have hRightReach := ihr leftMemory leftAligned
      rw [hright] at hRightReach
      have hLeftRep := encodeInto_represents left memory aligned
      rw [hleft] at hLeftRep
      have hRightRep := encodeInto_represents right leftMemory leftAligned
      rw [hright] at hRightRep
      have finalValid : (WordImage.mk finalMemory rightMemory.size).ValidAddress rightMemory.size := by
        simp [WordImage.ValidAddress, WordImage.memoryWords, finalMemory, rightAligned]
      have leftChild : (WordImage.mk finalMemory rightMemory.size).ChildAddress
          rightMemory.size leftAddress := by
        apply WordImage.ChildAddress.left finalValid
          (represents_valid (represents_mono hLeftFinal hLeftRep))
        · change finalMemory[_]? = _
          exact triple_get_zero rightMemory _ _ _
        · change finalMemory[_]? = _
          exact triple_get_one rightMemory _ _ _
      have rightChild : (WordImage.mk finalMemory rightMemory.size).ChildAddress
          rightMemory.size rightAddress := by
        apply WordImage.ChildAddress.right finalValid
          (represents_valid (represents_mono hRightFinal hRightRep))
        · change finalMemory[_]? = _
          exact triple_get_zero rightMemory _ _ _
        · change finalMemory[_]? = _
          exact triple_get_two rightMemory _ _ _
      simp only [encodeInto, hleft, hright]
      intro address lower valid
      change (WordImage.mk finalMemory rightMemory.size).ValidAddress address at valid
      change (WordImage.mk finalMemory rightMemory.size).ReachableFrom rightMemory.size address
      by_cases inLeft : address < leftMemory.size
      · have leftValid : (WordImage.mk leftMemory leftAddress).ValidAddress address := by
          refine ⟨valid.1, ?_⟩
          simp only [WordImage.memoryWords]
          have addressAligned := valid.1
          omega
        have reachable := hLeftReach address lower leftValid
        have lifted := reachable_mono (newRoot := rightMemory.size) hLeftFinal reachable
        exact reachable_trans (WordImage.ReachableFrom.child WordImage.ReachableFrom.root leftChild)
          lifted
      · by_cases inRight : address < rightMemory.size
        · have rightValid : (WordImage.mk rightMemory rightAddress).ValidAddress address := by
            refine ⟨valid.1, ?_⟩
            simp only [WordImage.memoryWords]
            have addressAligned := valid.1
            omega
          have reachable := hRightReach address (by omega) rightValid
          have lifted := reachable_mono (newRoot := rightMemory.size) hRightFinal reachable
          exact reachable_trans (WordImage.ReachableFrom.child WordImage.ReachableFrom.root rightChild)
            lifted
        · have upper := valid.2
          simp only [WordImage.memoryWords, finalMemory, Array.size_push] at upper
          have : address = rightMemory.size := by omega
          subst address
          exact WordImage.ReachableFrom.root

private theorem child_represents {I : WordImage} {parent child : Nat} {raw : Raw}
    (hp : I.Represents parent raw) (hc : I.ChildAddress parent child) :
    ∃ childRaw, I.Represents child childRaw := by
  cases hp with
  | nat address_valid tag value padding =>
      cases hc with
      | left _ _ childTag _ =>
          have impossible : (0 : Nat) = 1 := Option.some.inj (tag.symm.trans childTag)
          omega
      | right _ _ childTag _ =>
          have impossible : (0 : Nat) = 1 := Option.some.inj (tag.symm.trans childTag)
          omega
  | pair address_valid tag left_reference right_reference left_value right_value =>
      cases hc with
      | left _ _ _ reference =>
          have childEq := Option.some.inj (left_reference.symm.trans reference)
          subst child
          exact ⟨_, left_value⟩
      | right _ _ _ reference =>
          have childEq := Option.some.inj (right_reference.symm.trans reference)
          subst child
          exact ⟨_, right_value⟩

private theorem reachable_represents {I : WordImage} {root address : Nat} {raw : Raw}
    (rootRep : I.Represents root raw) (reach : I.ReachableFrom root address) :
    ∃ addressRaw, I.Represents address addressRaw := by
  induction reach with
  | root => exact ⟨raw, rootRep⟩
  | child _ edge ih =>
      obtain ⟨parentRaw, parentRep⟩ := ih
      exact child_represents parentRep edge

private theorem encodeRaw_denseAux (raw : Raw) : (encodeRaw raw).Dense := by
  intro address valid
  have reachable := encodeInto_reachable raw #[] (by decide) address (Nat.zero_le _) ?_
  · simpa [encodeRaw] using reachable
  · simpa [encodeRaw] using valid

private theorem encodeRaw_wellFormedAux (raw : Raw) : (encodeRaw raw).RootedWellFormed := by
  have rootRep : (encodeRaw raw).Represents (encodeRaw raw).root raw := by
    simpa [encodeRaw] using encodeInto_represents raw #[] (by decide)
  have dense : (encodeRaw raw).Dense := by
    intro address valid
    have reachable := encodeInto_reachable raw #[] (by decide) address (Nat.zero_le _) ?_
    · simpa [encodeRaw] using reachable
    · simpa [encodeRaw] using valid
  refine ⟨⟨?_, ?_⟩, ⟨raw, rootRep⟩⟩
  · rw [show (encodeRaw raw).memoryWords = 3 * raw.nodes by
      simpa [encodeRaw, WordImage.memoryWords] using encodeInto_size raw #[]]
    omega
  · intro address valid
    exact reachable_represents rootRep (dense address valid)

private theorem encodeInto_root_lt (raw : Raw) (memory : WordMemory) :
    (encodeInto raw memory).2 + 2 < (encodeInto raw memory).1.size := by
  induction raw generalizing memory with
  | nat payload => simp [encodeInto]
  | pair left right ihl ihr => simp [encodeInto]

private def AllLt (memory : WordMemory) (bound : Nat) : Prop :=
  ∀ x ∈ memory.toList, x < bound

private theorem allLt_push {memory : WordMemory} {bound x : Nat}
    (h : AllLt memory bound) (hx : x < bound) : AllLt (memory.push x) bound := by
  intro y hy
  rw [Array.toList_push] at hy
  rcases List.mem_append.mp hy with hold | hnew
  · exact h y hold
  · simp only [List.mem_singleton] at hnew
    subst y
    exact hx

private theorem encodeInto_allLt (raw : Raw) (memory : WordMemory) (bound : Nat)
    (existing : AllLt memory bound) (payloads : raw.maxNat < bound)
    (space : (encodeInto raw memory).1.size ≤ bound) :
    AllLt (encodeInto raw memory).1 bound := by
  induction raw generalizing memory with
  | nat payload =>
      simp only [Raw.maxNat] at payloads
      have positive : 0 < bound := by omega
      exact allLt_push (allLt_push (allLt_push existing (by simpa [WordImage.natTag]))
        payloads) (by omega)
  | pair left right ihl ihr =>
      generalize hleft : encodeInto left memory = leftOut
      obtain ⟨leftMemory, leftAddress⟩ := leftOut
      generalize hright : encodeInto right leftMemory = rightOut
      obtain ⟨rightMemory, rightAddress⟩ := rightOut
      have finalSize : rightMemory.size + 3 ≤ bound := by
        simpa only [encodeInto, hleft, hright, Array.size_push] using space
      have leftSpace : leftMemory.size ≤ bound := by
        have h := (encodeInto_extends right leftMemory).size_le
        rw [hright] at h
        simp only at h
        omega
      have rightSpace : rightMemory.size ≤ bound := by omega
      have leftPayloads : left.maxNat < bound := by
        simp only [Raw.maxNat] at payloads
        omega
      have rightPayloads : right.maxNat < bound := by
        simp only [Raw.maxNat] at payloads
        omega
      have leftAllAux := ihl memory existing leftPayloads
      rw [hleft] at leftAllAux
      have leftAll := leftAllAux leftSpace
      have leftRootLt := encodeInto_root_lt left memory
      rw [hleft] at leftRootLt
      simp only at leftRootLt
      have rightAllAux := ihr leftMemory leftAll rightPayloads
      rw [hright] at rightAllAux
      have rightAll := rightAllAux rightSpace
      have rightRootLt := encodeInto_root_lt right leftMemory
      rw [hright] at rightRootLt
      simp only at rightRootLt
      have tagLt : WordImage.pairTag < bound := by simp [WordImage.pairTag]; omega
      have leftAddressLt : leftAddress < bound := by omega
      have rightAddressLt : rightAddress < bound := by omega
      simp only [encodeInto, hleft, hright]
      exact allLt_push (allLt_push (allLt_push rightAll tagLt) leftAddressLt) rightAddressLt

private theorem encodeRaw_fitsAux (raw : Raw) (w : Nat) :
    raw.PayloadsFitInWord w →
    3 * raw.nodes ≤ 2 ^ w →
    (encodeRaw raw).FitsInWord w := by
  intro payloads space
  constructor
  · change (encodeInto raw #[]).1.size ≤ 2 ^ w
    rw [encodeInto_size]
    simpa using space
  · intro x hx
    simp only [WordImage.words, List.mem_cons] at hx
    rcases hx with rfl | hx
    · change (encodeInto raw #[]).2 < 2 ^ w
      have rootLt := encodeInto_root_lt raw #[]
      have sizeEq := encodeInto_size raw #[]
      simp at rootLt sizeEq
      omega
    · have all := encodeInto_allLt raw #[] (2 ^ w) (by simp [AllLt]) payloads ?_
      · exact all x hx
      · rw [encodeInto_size]
        simpa using space

/--
---
conclusion: Lax58.WordArena.encodeRaw_represents
---
-/
theorem encodeRaw_represents_proof (raw : Raw) :
    (encodeRaw raw).Represents (encodeRaw raw).root raw :=
  encodeRaw_representsAux raw

/--
---
conclusion: Lax58.WordArena.encodeRaw_wellFormed
---
-/
theorem encodeRaw_wellFormed_proof (raw : Raw) :
    (encodeRaw raw).RootedWellFormed :=
  encodeRaw_wellFormedAux raw

/--
---
conclusion: Lax58.WordArena.encodeRaw_dense
---
-/
theorem encodeRaw_dense_proof (raw : Raw) :
    (encodeRaw raw).Dense :=
  encodeRaw_denseAux raw

/--
---
conclusion: Lax58.WordArena.encodeRaw_memoryWords
---
-/
theorem encodeRaw_memoryWords_proof (raw : Raw) :
    (encodeRaw raw).memoryWords = 3 * raw.nodes :=
  encodeRaw_memoryWordsAux raw

/--
---
conclusion: Lax58.WordArena.encodeRaw_totalWords
---
-/
theorem encodeRaw_totalWords_proof (raw : Raw) :
    (encodeRaw raw).totalWords = 3 * raw.nodes + 1 := by
  simp [WordImage.totalWords, encodeRaw_memoryWordsAux]

/--
---
conclusion: Lax58.WordArena.encodeRaw_fits
---
-/
theorem encodeRaw_fits_proof (raw : Raw) (w : Nat) :
    raw.PayloadsFitInWord w →
    3 * raw.nodes ≤ 2 ^ w →
    (encodeRaw raw).FitsInWord w :=
  encodeRaw_fitsAux raw w

/--
---
conclusion: Lax58.WordArena.encode_represents
---
-/
theorem encode_represents_proof {α : Type u} (P : Presentation α) (x : α) :
    (encode P x).Represents (encode P x).root (P.toRaw x) := by
  simpa [encode] using encodeRaw_representsAux (P.toRaw x)

/--
---
conclusion: Lax58.WordArena.encode_memoryWords
---
-/
theorem encode_memoryWords_proof {α : Type u} (P : Presentation α) (x : α) :
    (encode P x).memoryWords = 3 * P.structuralSize x := by
  simpa [encode, Presentation.structuralSize] using encodeRaw_memoryWordsAux (P.toRaw x)

/--
---
conclusion: Lax58.WordArena.encode_totalWords
---
-/
theorem encode_totalWords_proof {α : Type u} (P : Presentation α) (x : α) :
    (encode P x).totalWords = 3 * P.structuralSize x + 1 := by
  simp [encode, Presentation.structuralSize, WordImage.totalWords, encodeRaw_memoryWordsAux]

/--
---
conclusion: Lax58.WordArena.encode_fits
---
-/
theorem encode_fits_proof {α : Type u} (P : Presentation α) (x : α) (w : Nat) :
    P.PayloadsFitInWord x w →
    3 * P.structuralSize x ≤ 2 ^ w →
    (encode P x).FitsInWord w := by
  simpa [encode, Presentation.PayloadsFitInWord, Presentation.structuralSize] using
    encodeRaw_fitsAux (P.toRaw x) w

end Lax58Proofs.WordArena
