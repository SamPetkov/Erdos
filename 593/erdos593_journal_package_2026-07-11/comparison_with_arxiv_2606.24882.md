# Comparison with arXiv:2606.24882

**Comparison date:** 11 July 2026  
**Paper:** Eric Li, *A Resolution of Erdős Problems 593 and 1177: Obligatory Triple Systems and Exact Spectra*, arXiv:2606.24882v1.

## Verdict

The paper is materially helpful. It independently states the same exact classification and corroborates the main sequence-lift/Levi-bridge architecture. The proof in the accompanying manuscript is not merely a copy of the paper: several load-bearing components use different mechanisms.

## Shared proof spine

Both arguments use a one-apex sequence lift; a transfinite branch proof of uncountable chromaticity; finite trace control that supplies incidence bridges and converts Berge cycles to graph cycles; and a quotient forest with a running-intersection step for reconstruction by one-point amalgamations.

## Substantive differences

| Component | Accompanying proof | Li's preprint |
|---|---|---|
| Expansion atom | Direct proof for $K_{n,n}^+$ using codegrees, closure chains, and a rainbow submatrix lemma | Imports Reiher's stronger uniform theorem |
| One-point closure | Rooted abundance with many disjoint petals | One selected rooted copy per eligible root and a bounded-outdegree graph |
| Structural decomposition | Delete all Levi bridges and analyze bridge-free blocks | Select one bridge at every hyperedge-node and use derivatives |
| Trace result | Necessity theorem: every finite linear trace is assembled from $J_s^+$ factors | Exact if-and-only-if bridge-selector theorem |
| Nonlinear avoidance | Explicit Erdős--Rado triangle system | Classical Erdős--Hajnal--Rothschild interface |
| Odd-cycle avoidance | Explicit shift graphs with a self-contained odd-girth proof | Imported exact high-odd-girth graphs |
| Overall scope | Problem 593 | Problems 593 and 1177, plus exact-cardinal spectra |

## Repairs made after comparison

1. The equivalence $F\in\mathcal B\iff F^\circ\in\mathcal B$ is proved by structural induction, including every amalgamation case.
2. In the rooted-abundance lemma, the auxiliary graph is explicitly built on the bad-root set $B$ using $S_v\cap B$.
3. The bridge-block decomposition includes a running-intersection claim; the fact that the quotient is a forest is not used as a substitute for that claim.

## Confidence statement

No blocking discrepancy was found. The arXiv paper provides strong external corroboration of the classification and the global architecture, but it does not constitute a line-by-line verification of the alternative direct expansion proof or the shift-graph argument. The manuscript should therefore be described as a candidate self-contained proof with an internal and comparative audit, not as formally verified or peer-reviewed.
