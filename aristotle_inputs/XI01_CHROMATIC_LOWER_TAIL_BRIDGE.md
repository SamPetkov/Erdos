# XI01 -- Strict chromatic lower-tail bridge

Status: send now.  Kind: generic probability transport.  No dependency on
Sections VIII--IX.

## Target

For natural-valued random variables `X n` and thresholds `k n`, prove that

```text
Tendsto (fun n => mu n {omega | X n omega <= k n}) atTop (nhds 0)
```

implies

```text
Tendsto (fun n => mu n {omega | k n < X n omega}) atTop (nhds 1).
```

The sample space and probability measure may depend on `n`.  The exact
declaration `strictLower_probability_tendsto_one_of_atMost_tendsto_zero` is at
`.aristotle/pending-next/xi01_chromatic_lower_bridge/ChromaticLowerTailBridge/Main.lean`.

## Required proof content

Show that the strict-lower event is exactly the complement of the at-most
event, use the supplied measurability and probability-measure hypotheses, and
transport convergence through the complement identity.  Do not introduce an
independence assumption or weaken the limit to a subsequence.

## Concrete dependency boundary

This bridge is generic.  Supplying the actual premise for
`X n = chromaticNumberNat` and the manuscript `k_chi^-` is an upstream
Sections IV--V obligation, not a Sections VIII--IX obligation.
