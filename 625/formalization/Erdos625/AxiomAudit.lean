import Erdos625.IndependentSets
import Erdos625.BoundedDifferences
import Erdos625.PhaseExpansion
import Erdos625.PhaseEstimates
import Erdos625.ProbabilityTools

/-!
# Kernel dependency audit

Compiling this module asks Lean to print the axioms used by representative
public theorems through the current verified bricks. Classical choice,
propositional extensionality, and quotient
soundness may legitimately enter through mathlib and finite minimization;
No placeholder axiom or project-defined axiom may appear.
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
#print axioms Erdos625.phaseDelta_mem_Ico
#print axioms Erdos625.mu_succ_div_identity
#print axioms Erdos625.mu_pred_div_identity
#print axioms Erdos625.markov_measureReal_le
#print axioms Erdos625.paleyZygmund_zero
#print axioms Erdos625.mcdiarmid_two_sided_of_subgaussian
#print axioms Erdos625.binomialHalf_lowerQuarter_le_exp
#print axioms Erdos625.randomGraphMeasure_independentEvent
#print axioms Erdos625.independentSetExpectation_eq_ofReal_mu
#print axioms Erdos625.independenceNumberExceedsEvent_eq_countPositive
#print axioms Erdos625.randomGraphMeasure_independenceNumberExceeds_le_mu_succ
#print axioms Erdos625.alphaZero_eq_two_phaseS_div_q_add_one
#print axioms Erdos625.exists_phaseK_abs_bound
#print axioms Erdos625.eventually_phaseRangeDomain
#print axioms Erdos625.phaseNat_isEquivalent_scaled_logOrder
#print axioms Erdos625.eventually_two_mul_phaseNat_le
#print axioms Erdos625.log_descFactorial_linear_error_le
#print axioms Erdos625.stirlingLogRemainder_mem_Icc
#print axioms Erdos625.cubeMean_exp_center_le
#print axioms Erdos625.integral_boolCubePMF_eq_cubeMean
#print axioms Erdos625.boundedDifferences_hasSubgaussianMGF
#print axioms Erdos625.boundedDifferences_twoSidedTail
