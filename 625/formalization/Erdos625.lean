import Erdos625.Foundation
import Erdos625.GraphModel
import Erdos625.Phase
import Erdos625.PhaseExpansion
import Erdos625.PhaseEstimates
import Erdos625.PhaseAsymptotic
import Erdos625.PhaseConsequences
import Erdos625.ProbabilityTools
import Erdos625.Target
import Erdos625.IndependentSets
import Erdos625.BoundedDifferences
import Erdos625.BlockBoundedDifferences
import Erdos625.RareSeedInversion
import Erdos625.VertexBlockGraph
import Erdos625.VertexBlockExpectation
import Erdos625.InducedCochromaticCapacity
import Erdos625.CochromaticAmplification
import Erdos625.CochromaticSeedGap
import Erdos625.CochromaticCapacityLowerTail
import Erdos625.ProfileEntropyS4
import Erdos625.ProfileOptimizerS4
import Erdos625.ProfileValueStabilityS4
import Erdos625.ProfileValueUniformS4
import Erdos625.ProfileOptimizerContinuityS4
import Erdos625.ProfileOptimizerUniformS4
import Erdos625.ColoringProfileFirstMoment
import Erdos625.ColoringProfileEnumeration
import Erdos625.ColoringProfileEnumerationInverse
import Erdos625.ColoringProfileEnumerationInjective
import Erdos625.ColoringProfileAggregation
import Erdos625.AxiomAudit

/-!
# Erdős Problem 625

Kernel-checked foundations for an incremental formalization of the proposed
random-graph chromatic versus cochromatic gap theorem. Importing this root
module checks the graph/probability model, exact phase arithmetic, elementary
probability bounds, the independent-set first-moment calculation, and the
non-asymptotic setup and finite Taylor/falling-factorial/Robbins estimates for
the phase expansion, together with the full-sequence endpoint-uniform
asymptotic expansion (2.2) and its genuine consequences (2.3), (2.4), and
(2.9). It also includes a genuine bounded-differences MGF proof
on both the uniform finite Boolean cube and arbitrary dependent families of
nonempty finite uniform blocks, plus the exact four-support exponential-family
mean/variance inversion and entropy-optimizer infrastructure. The graph law is
also identified exactly with the uniform vertex-block product law, including
event and expectation transport and the generic deletion-oscillation tail
bridge.  The largest induced `k`-cocolourable subgraph is now defined, its
full-capacity event is characterized exactly, and its chosen vertex-block
profile yields one- and two-sided `G(n,1/2)` tails centered at the actual
expectation.  An attaining induced core also yields the exact deterministic
leftover size and the cocolouring-concatenation inequality corresponding to
manuscript (10.9).  A generic rare endpoint seed plus a one-sided sub-Gaussian
tail is also inverted with the exact `sqrt (2 * v * Lambda)` cost used in
(10.7), and its induced-capacity specialization proves the exact
`sqrt ((n - 1) * Lambda / 2)` endpoint-to-expectation bound for `n ≥ 2`.
The matching one-sided lower tail then proves the exact manuscript (10.8)
failure bound `exp (-r)`, including the non-strict boundary event and with no
two-sided factor.
On the four-point profile support, the optimized entropy-plus-score value is
also proved 1-Lipschitz in the coordinatewise score norm, with a fixed-target
sequential convergence corollary and a genuinely uniform-in-target epsilon
formulation on the full interval `(2,5)`.  Joint score/target continuity then
gives moving-target tilt and optimizer convergence.  On every compact subset
of `(2,5)`, Heine--Cantor supplies uniform tilt and simultaneous four-coordinate
optimizer convergence, together with a genuine eventual positive lower bound.
The finite profile-colouring layer also defines unordered nonempty colour
classes, proves the exact forbidden-edge probability for every fixed
partition, and evaluates the first moment as the actual profile-partition
cardinality times that probability.  The explicit decorated-partition
equivalence now discharges the finite enumeration proposition internally, so
the mass-constrained factorial-quotient first-moment formula (4.2) is an
unconditional theorem of the project.  The mass-`n`, exactly-`k`, size-bounded
profile family is also finitized in a coordinate box, bounded by `(n+1)^b`,
and its aggregate expectation is proved to be the exact sum of the per-profile
expectations.
For the finite enumeration bridge, canonical labelled slots and factorial
decorations are counted exactly.  A decorated profile partition produces a
genuine vertex-to-slot equivalence, and conversely every slot equivalence now
reconstructs the correct unordered profile partition, canonical labels, and
within-part orders.  Explicit inverse-coordinate and kernel-recovery arguments
prove the total forgetful map injective and surjective, yielding the actual
global equivalence and the exact unordered factorial enumeration under the
necessary vertex-mass constraint.
The target proposition itself remains
explicitly unproved until the full dependency chain is formalized.
-/
