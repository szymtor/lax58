import Lax560851.FormulaExample

open Lax560851.FormulaExample Lax560851.StructuralPresentation Lax560851.StructuralCombinators

example : formulaRaw.Laws := formulaRaw.certified.checked

example : sampleStructure = Raw.constructor "conj"
    [Raw.constructor "atom" [Raw.nat 0],
      Raw.constructor "neg" [Raw.constructor "atom" [Raw.nat 1]]] := rfl

example : sampleInput = (Lax560851.WordArena.encodeRaw sampleStructure).toInput := rfl

#print axioms Lax560851.FormulaExample.formulaRaw.certified
