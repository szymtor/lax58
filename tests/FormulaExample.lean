import Lax58.FormulaExample

open Lax58.FormulaExample Lax58.StructuralPresentation Lax58.StructuralCombinators

example : formulaRaw.Laws := formulaRaw.certified.checked

example : sampleStructure = Raw.constructor "conj"
    [Raw.constructor "atom" [Raw.nat 0],
      Raw.constructor "neg" [Raw.constructor "atom" [Raw.nat 1]]] := rfl

example : sampleInput = (Lax58.WordArena.encodeRaw sampleStructure).toInput := rfl

#print axioms Lax58.FormulaExample.formulaRaw.certified
