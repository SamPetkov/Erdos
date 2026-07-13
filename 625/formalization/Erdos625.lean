import Erdos625.Foundation
import Erdos625.GraphModel
import Erdos625.Phase
import Erdos625.PhaseExpansion
import Erdos625.PhaseEstimates
import Erdos625.ProbabilityTools
import Erdos625.Target
import Erdos625.IndependentSets
import Erdos625.BoundedDifferences
import Erdos625.AxiomAudit

/-!
# Erdős Problem 625

Kernel-checked foundations for an incremental formalization of the proposed
random-graph chromatic versus cochromatic gap theorem. Importing this root
module checks the graph/probability model, exact phase arithmetic, elementary
probability bounds, the independent-set first-moment calculation, and the
non-asymptotic setup and finite Taylor/falling-factorial/Robbins estimates for
the phase expansion. It also includes a genuine bounded-differences MGF proof
on the uniform finite Boolean cube. The target proposition itself remains
explicitly unproved until the full dependency chain is formalized.
-/
