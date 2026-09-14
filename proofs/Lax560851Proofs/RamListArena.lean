import Lax560851Proofs.WordArena
import Lax560851.StructuralCombinators

namespace Lax560851Proofs.RamListArena

open Lax560851.StructuralPresentation
open Lax560851.StructuralCombinators
open Lax560851.WordArena

/-- The payload portion of the distinguished list arena: each natural is
stored as its tag, payload, and padding word. -/
def naturalTriples : List Nat → List Nat
  | [] => []
  | value :: rest => [0, value, 0] ++ naturalTriples rest

/-- Exact postorder words for a list arena appended after `base` existing
words. This executable description is also the specification used by the
native-to-arena input adapter. -/
def listArenaWordsFrom (base : Nat) : List Nat → List Nat
  | [] => [0, 0, 0]
  | value :: rest =>
      [0, value, 0] ++ listArenaWordsFrom (base + 3) rest ++
        [1, base, base + 3 + 6 * rest.length]

/-- Pair blocks still to be emitted, from the deepest constructed list cell
back toward the outermost one. `count` records how many outer cells have
already been traversed. -/
def pairSuffix (total : Nat) : Nat → List Nat
  | 0 => []
  | count + 1 =>
      [1, 3 * count, 6 * total - 3 * count - 3] ++ pairSuffix total count

theorem listArenaWordsFrom_flat (total consumed : Nat) (values : List Nat)
    (hlength : consumed + values.length = total) :
    listArenaWordsFrom (3 * consumed) values ++ pairSuffix total consumed =
      naturalTriples values ++ [0, 0, 0] ++ pairSuffix total total := by
  induction values generalizing consumed with
  | nil =>
      simp only [List.length_nil, Nat.add_zero] at hlength
      subst total
      simp [listArenaWordsFrom, naturalTriples]
  | cons value rest ih =>
      have hnextLength : consumed + 1 + rest.length = total := by
        simp only [List.length_cons] at hlength
        omega
      have hright : 3 * (consumed + 1) + 6 * rest.length =
          6 * total - 3 * consumed - 3 := by omega
      rw [listArenaWordsFrom]
      simp only [List.append_assoc]
      rw [show 3 * consumed + 3 = 3 * (consumed + 1) by omega, hright]
      change [0, value, 0] ++
          (listArenaWordsFrom (3 * (consumed + 1)) rest ++
            pairSuffix total (consumed + 1)) = _
      rw [ih (consumed + 1) hnextLength]
      simp [naturalTriples, List.append_assoc]

theorem listArenaWords_flat (values : List Nat) :
    listArenaWordsFrom 0 values =
      naturalTriples values ++ [0, 0, 0] ++ pairSuffix values.length values.length := by
  simpa [pairSuffix] using listArenaWordsFrom_flat values.length 0 values (by simp)

private theorem encodeInto_size (raw : Raw) (memory : WordMemory) :
    (encodeInto raw memory).1.size = memory.size + 3 * raw.nodes := by
  induction raw generalizing memory with
  | nat payload => simp [encodeInto, Raw.nodes]
  | pair left right ihLeft ihRight =>
      simp [encodeInto, ihLeft, ihRight, Raw.nodes]
      omega

private theorem encodeInto_root (raw : Raw) (memory : WordMemory) :
    (encodeInto raw memory).2 + 3 = memory.size + 3 * raw.nodes := by
  induction raw generalizing memory with
  | nat payload => simp [encodeInto, Raw.nodes]
  | pair left right ihLeft ihRight =>
      generalize hleft : encodeInto left memory = leftOut
      obtain ⟨leftMemory, leftRoot⟩ := leftOut
      generalize hright : encodeInto right leftMemory = rightOut
      obtain ⟨rightMemory, rightRoot⟩ := rightOut
      have hleftSize : leftMemory.size = memory.size + 3 * left.nodes := by
        simpa [hleft] using encodeInto_size left memory
      have hrightSize : rightMemory.size = leftMemory.size + 3 * right.nodes := by
        simpa [hright] using encodeInto_size right leftMemory
      simp only [encodeInto, hleft, hright, Raw.nodes]
      omega

private theorem list_nodes (xs : List Nat) :
    (listToRaw nat xs).nodes = 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons value rest ih =>
      change (Raw.pair (.nat value) (listToRaw nat rest)).nodes =
        2 * (rest.length + 1) + 1
      simp only [Raw.nodes, ih]
      omega

theorem encodeInto_list_words (xs : List Nat) (memory : WordMemory) :
    (encodeInto (listToRaw nat xs) memory).1.toList =
      memory.toList ++ listArenaWordsFrom memory.size xs := by
  induction xs generalizing memory with
  | nil =>
      simp [listToRaw, nat, encodeInto, listArenaWordsFrom, WordImage.natTag]
  | cons value rest ih =>
      let afterValue := ((memory.push 0).push value).push 0
      have hvalue : encodeInto (nat.toRaw value) memory =
          (afterValue, memory.size) := by rfl
      generalize htail : encodeInto (listToRaw nat rest) afterValue = tailOut
      obtain ⟨tailMemory, tailRoot⟩ := tailOut
      have htailWords := ih afterValue
      rw [htail] at htailWords
      have htailRoot := encodeInto_root (listToRaw nat rest) afterValue
      rw [htail] at htailRoot
      have hrootValue : tailRoot = memory.size + 3 + 6 * rest.length := by
        simp [afterValue, list_nodes] at htailRoot
        omega
      rw [listToRaw, encodeInto, hvalue]
      simp only
      rw [htail]
      change (((tailMemory.push WordImage.pairTag).push memory.size).push tailRoot).toList = _
      simp only [Array.toList_push]
      rw [htailWords, hrootValue]
      simp [afterValue, listArenaWordsFrom, WordImage.pairTag, List.append_assoc]

theorem encode_list_root (xs : List Nat) :
    (encode (list nat) xs).root = 6 * xs.length := by
  have hroot := encodeInto_root (listToRaw nat xs) #[]
  simp only [encode, encodeRaw, list, Array.size_empty, Nat.zero_add,
    list_nodes] at hroot ⊢
  omega

/-- The entire distinguished input tape, with no unspecified suffix. -/
theorem encode_list_input_exact (xs : List Nat) :
    (encode (list nat) xs).toInput =
      6 * xs.length :: listArenaWordsFrom 0 xs := by
  change (encode (list nat) xs).root ::
      (encodeInto (listToRaw nat xs) #[]).1.toList = _
  rw [encode_list_root, encodeInto_list_words]
  rfl

private theorem naturalTriples_prefix_aux (xs : List Nat) (memory : WordMemory) :
    ∃ suffix,
      (encodeInto (listToRaw nat xs) memory).1.toList =
        memory.toList ++ naturalTriples xs ++ suffix := by
  induction xs generalizing memory with
  | nil =>
      refine ⟨[0, 0, 0], ?_⟩
      simp [listToRaw, nat, encodeInto, naturalTriples, WordImage.natTag]
  | cons value rest ih =>
      let afterValue := ((memory.push 0).push value).push 0
      generalize htail : encodeInto (listToRaw nat rest) afterValue = tailOut
      obtain ⟨tailMemory, tailRoot⟩ := tailOut
      have htailPrefix := ih afterValue
      rw [htail] at htailPrefix
      simp only at htailPrefix
      rcases htailPrefix with ⟨suffix, hsuffix⟩
      refine ⟨suffix ++ [1, memory.size, tailRoot], ?_⟩
      have hvalue : encodeInto (nat.toRaw value) memory =
          (afterValue, memory.size) := by rfl
      rw [listToRaw, encodeInto, hvalue]
      simp only
      rw [htail]
      change (((tailMemory.push WordImage.pairTag).push memory.size).push tailRoot).toList = _
      simp only [Array.toList_push]
      rw [hsuffix]
      simp [afterValue, naturalTriples, List.append_assoc, WordImage.pairTag]

/-- The arena memory begins with exactly the natural payload blocks, in list
order. The nil and pair blocks form an irrelevant suffix for the
arena-to-native streaming adapter. -/
theorem encode_list_input_prefix (xs : List Nat) :
    ∃ suffix,
      (encode (list nat) xs).toInput =
        6 * xs.length :: (naturalTriples xs ++ suffix) := by
  rcases naturalTriples_prefix_aux xs #[] with ⟨suffix, hsuffix⟩
  refine ⟨suffix, ?_⟩
  change (encode (list nat) xs).root ::
      (encodeInto (listToRaw nat xs) #[]).1.toList = _
  rw [encode_list_root, hsuffix]
  rfl

end Lax560851Proofs.RamListArena
