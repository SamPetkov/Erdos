# X06 -- Quantitative capacity/leftover intersection

Status: send now.  Kind: generic probability transport.  No dependency on
Sections VIII--IX.

## Target

In a probability space, if `A intersect B` is contained in `Good`, and the
failure probabilities of `A` and `B` are bounded by `delta` and `epsilon`,
prove

\[
 \mu_{\mathbb R}(Good^c)\le \delta+\varepsilon.
\]

The exact isolated declaration is
`failure_probability_le_add_of_two_success_events`, at
`.aristotle/pending-next/x06_capacity_leftover_quantitative/CapacityLeftoverQuantitative/Main.lean`.

## Required proof content

Use `Good^c subset A^c union B^c`, measure monotonicity, and finite-measure
subadditivity.  Preserve `Measure.real`; do not add an independence
hypothesis.  The supplied measurability assumptions for `A` and `B` may be
used where required by complement identities.

## Downstream use

This is the quantitative `exp(-r) + epsilon_n` seam in manuscript (10.5),
between the accepted capacity tail and X05's simultaneous leftover event.
