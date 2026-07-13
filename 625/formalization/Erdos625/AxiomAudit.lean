import Erdos625.Target

/-!
# Kernel dependency audit

Compiling this module asks Lean to print the axioms used by the public M0
theorems.  Classical choice, propositional extensionality, and quotient
soundness may legitimately enter through mathlib and finite minimization;
`sorryAx` or a project-defined axiom must never appear.
-/

#print axioms Erdos625.coColorable_of_induce_and_compl
#print axioms Erdos625.coColorable_of_induce_and_colorable_compl
#print axioms Erdos625.coColorable_iff_cochromaticNumber_le
#print axioms Erdos625.cochromaticNumber_le_chromaticNumber
#print axioms Erdos625.gapConstant_pos
#print axioms Erdos625.randomGraphMeasure_singleton
#print axioms Erdos625.randomGraphMeasure_singleton_uniform
#print axioms Erdos625.measurableSet_gapEvent
#print axioms Erdos625.gapProbability_le_one
#print axioms Erdos625.erdos625Statement_iff_real
