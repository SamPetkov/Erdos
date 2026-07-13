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
import Erdos625.ProfileEntropyS4
import Erdos625.ProfileOptimizerS4
import Erdos625.ProfileValueStabilityS4
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
On the four-point profile support, the optimized entropy-plus-score value is
also proved 1-Lipschitz in the coordinatewise score norm, with a fixed-target
sequential convergence corollary.
The target proposition itself remains
explicitly unproved until the full dependency chain is formalized.
-/
