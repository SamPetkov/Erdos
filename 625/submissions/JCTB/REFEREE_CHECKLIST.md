# Focused referee checklist (not a completed proof audit)

1. Uniform phase first moments: verify every endpoint convention for `delta_n`, the real root corridor and integer rounding, and the strict five-size entropy gain.
2. Exact signed overlap law: check row/column slot ordering, the multinomial configuration-model probability, and the `2^(W+c(H)-|V(H)|)` factor, including empty support.
3. Whole common classes: independently check recurrence endpoints, intermediate-negative-rate argument, and transition between three regimes.
4. Large overlap cells: verify matching structure, all deficit-sum estimates, weighted endpoint-table regrouping, and exclusion of double-counting.
5. Residual overlaps: verify the exact decomposition, conditional factors after exposing cells, cycle-space treatment, and both residual-mass regimes.
6. Final normalized second-moment exponent: check `Lambda_n = O(n^(3/4) log n)` uniformly in phase with all constants and overlap regimes correctly assembled.
7. Amplification: verify one-sided bounded differences, simultaneously valid leftover coloring, `o(n/(log n)^3)` loss, and summable probability bounds.
8. Formalization scope: compare the actual Lean theorem declaration with the manuscript; avoid implying that the strongest refinements are fully formalized.

This is a review plan only and must not be described as independent certification.
