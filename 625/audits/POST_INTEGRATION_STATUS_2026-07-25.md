# Erdős 625: post-integration proof status

**Date:** 25 July 2026  
**Cumulative branch:** `agent/625-full-proof-audit-frontier`  
**Primary review PR:** #39  
**Purpose:** authoritative update to the time-stamped status paragraphs in
`FULL_THEOREM_LEMMA_AUDIT_2026-07-25.md` after integrating and repairing the
Section IX branch

## 1. Branch integration completed

PR #40 mechanically merged the public Section IX stack

\[
  \#34\longrightarrow\#35\longrightarrow\#37
\]

into the head branch of PR #39, which was already stacked on the Section VIII
line

\[
  \#36\longrightarrow\#38\longrightarrow\#39.
\]

The cumulative review branch therefore contains both proof directions. The
merge does not by itself establish Proposition 9.2; it makes the remaining
interface visible in one tree.

## 2. Corrected Section IX verdict

The initial audit recorded PR #37's focused target as failing. That statement
is now obsolete.

The local Lean failures in
`Section9QOnlyTwoRegimeAssembly.lean` were mechanical:

1. `omega` was asked to discharge inequalities through nested `Nat.max`
   expressions;
2. a trailing `ring` was called after `field_simp` had already closed its goal;
3. one namespace spelling was corrected.

After explicit monotonicity proofs and the algebra cleanup, the focused q-only
workflow is green at commit
`2ea82c988218dee89d3639f598090ce813501c40`.

More importantly, the repaired theorem controls the **literal attained
attachment sum**, not an independent table law or a polymer surrogate. The
relevant finite/asymptotic chain is now:

1. `normalizedSignedProfileSecondMoment_eq_midpointCanonicalAttachmentSum`
   identifies the normalized signed-profile second moment exactly with the
   attained canonical attachment sum;
2. `midpointCanonicalAttachmentSum_le_bare_mul` factors a pointwise literal
   attachment bound from that exact sum;
3. `exists_midpointCanonicalAttachment_qOnly_twoRegime_error` proves, under
   the eventual phase cap and the exact profile degree cap,

   \[
     \operatorname{AttachmentSum}_n
     \le
     \operatorname{BareSkeletonSum}_n
     \exp\!\left\{\varepsilon_n\frac{n}{(\ln n)^4}\right\},
     \qquad \varepsilon_n\to0.
   \]

For the four-size midpoint profile, the hypotheses are the intended structural
ones: the largest block size is at most the phase integer and every profile
margin is at most that largest size.

**Current Section IX classification:** **GREEN conditional only on the Section
VIII bare-skeleton estimate.** It is no longer an independent analytic
bottleneck.

## 3. Current Section VIII verdict

The repository already has kernel-checked finite components for:

- the exact signed-overlap/canonical-demand decomposition;
- the labelled-witness incidence and unlabelled-skeleton fibre quotient;
- the endpoint block-pairing factorial identity;
- the denominator-free squared endpoint transportation inequality;
- the square-free AM--GM linearization;
- the exact all-high deficit arithmetic;
- the literal one-cell high-deficit weight bound;
- the optional-deficit product for one fixed physical endpoint block pairing.

The new note `SECTION8_GLOBAL_DECORATION_BRIDGE.md` supplies the missing
paper-level assembly. Its central finite comparison is

\[
  \frac{w(\mathcal M,j)}{w(\mathcal M,m)}
  \le
  \prod_{e\in\mathcal M}n^{h_e}R_{m_e,d_e}(h_e),
\]

where completing a high cell of multiplicity `j_e=m_e-h_e` to full
containment changes the single global denominator by

\[
  \frac{(n)_{J+H}}{(n)_J}=(n-J)_H\le n^H.
\]

The completion map gives a disjoint fibre decomposition over full endpoint
block pairings. Summing the geometric deficit charges in each physical cell
and then applying endpoint transportation yields

\[
  \operatorname{BareSkeletonSum}_n
  \le
  \exp\!\left\{
    O(n^{2/3}(\ln n)^{4/3})+O(\sqrt{n\ln n})
  \right\}
  =
  \exp\!\left\{o\!\left(\frac n{(\ln n)^4}\right)\right\}.
\]

The exact local ratio, the global falling-factorial identity, the product
comparison, and the geometric fibre sum are regression-tested in
`full_proof_audit_regression.py`.

### Remaining formal theorem

The main unresolved Lean obligation is one global Section VIII theorem, with
four explicit subinterfaces:

1. identify every attained canonical high physical skeleton uniquely as a
   full endpoint block pairing plus one allowed deficit per selected physical
   cell;
2. prove the global weight comparison, including the single denominator ratio
   above;
3. identify the sum of full-pairing weights with the exact endpoint table sum
   `sum_L fourEndpointW(L)` using the existing fibre cardinality theorem;
4. combine the endpoint AM--GM/multinomial sum and the all-deficit fibre sum at
   the attained four-size midpoint profile.

The current generic Lean product theorem incurs one extra factor of order
`ln n` in the exponent, giving

\[
  O(n^{2/3}(\ln n)^{7/3})
\]

rather than the sharper paper-level
`O(n^{2/3}(\ln n)^{4/3})`. Both are
`o(n/(ln n)^4)`. Thus the weaker formal endpoint is sufficient for
Proposition 9.2; a geometric-series lemma is needed only to match the sharper
exponent in the paper.

## 4. Current theorem status

The theorem-level status is now:

| Layer | Status |
|---|---|
| Sections 2--7: locations, entropy, exact overlap algebra, partial diagonals | logically coherent; finite improvements available |
| Section 8 bare-skeleton estimate | paper-level global bridge written; global Lean assembly pending |
| Section 9 literal attained attachment estimate | repaired and focused-CI green |
| Proposition 9.2 | follows once the Section 8 bare-skeleton theorem is instantiated and composed with the existing exact Section 9 identity |
| Lemmas 10.1--10.2 and final event intersection | logically coherent conditional on Proposition 9.2 |
| `Erdos625Statement` | not yet kernel-proved |

The proof effort should therefore be concentrated on the single global
Section VIII assembly theorem. Additional cycle decompositions, residual
surrogates, or support scans do not address the current bottleneck.

## 5. Stronger paper once Section VIII is closed

The cumulative audit supports the following upgraded main-paper package:

1. a phase-resolved gap coefficient
   \[
     \frac{(\ln2)^2}{8}\bigl(\ln2-D_4(\delta_n)\bigr);
   \]
2. the certified uniform coefficient
   \[
     \frac{(\ln2)^2}{8}\ln(1000/639)
     =0.026896409808379\ldots;
   \]
3. the simultaneous complement corollary
   \[
     \min\{\chi(G_n),\chi(\overline G_n)\}-\zeta(G_n)
     \ge c\frac n{(\ln n)^3};
   \]
4. the matching-restriction theorem for weighted even subgraphs;
5. the abstract rare-seed-to-typical-completion method;
6. the matching-decoration transfer principle isolated in the new Section VIII
   bridge.

Items 1--3 remain conditional on completion of the normalized second moment;
items 4--6 are reusable finite or method-level results whose exact scope is
recorded in `TRANSFERABLE_RESULTS_AND_COROLLARIES_2026-07-25.md`.

## 6. CI interpretation

For this repository, a green root `Lean` workflow is not enough to certify a
new isolated module if that module is absent from the root aggregate. The
focused workflow attached to each proof branch is therefore load-bearing.

At the time of this update:

- the repaired q-only focused target has a recorded successful run;
- the exact Python audit had already passed before the final Section VIII
  regression expansion;
- the cumulative head is rerunning the root and focused workflows.

The PR must remain draft until the exact cumulative head has green focused
Section VIII, focused Section IX, audit-regression, and root Lean checks.
