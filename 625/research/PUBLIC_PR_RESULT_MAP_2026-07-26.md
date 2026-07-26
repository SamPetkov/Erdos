# Public Erdős 625 PR result map

**Cutoff:** 26 July 2026  
**Purpose:** distinguish the original public proof record, merged formalization bricks, later audit/simplification branches, and theorem-upgrade research

This map is descriptive. An open PR is not treated as merged into `main`, and a
successful finite or focused check is not treated as a proof of
`Erdos625Statement`.

---

## 1. Public proof chronology

| PR | Date | Role | Status interpretation |
|---:|---|---|---|
| #1 | 12 Jul | Public verification bundle containing the candidate proof | Earliest explicit public PR timestamp for the candidate proof; provisional internal verification only |
| #2 | 12 Jul | Source audit, styled proof, release archive | Historical/source validation; no external proof verification |
| #3 | 12 Jul | Manuscript citations and current verification record | Bibliographic and presentation work |
| #4 | 12 Jul | Adversarial leap audit and written-proof repair | Substantive internal repair; theorem still candidate |
| #5 | 12 Jul | Exact finite illustrative animation | Expository only |
| #6 | 13 Jul | Synchronize proof components and traceability | Consolidation; no new theorem claim |

Public chronology anchor:

```text
PR #1 created: 2026-07-12 19:08:31 UTC
PR #1 head:    945ed733af198fe8698e14079ddc079f2bc554d7
PR #1 merged:  2026-07-12 19:29:28 UTC
```

---

## 2. Merged Lean/formalization progression

### Model, probability, phase, and first moment

| PR | Main mathematical content |
|---:|---|
| #7 | Exact finite graph/cocoloring model, `zeta<=chi`, random graph law, definition of `Erdos625Statement` |
| #8 | Phase/floor arithmetic, independent-set first moment, Markov/Paley--Zygmund, Boolean-cube bounded differences |
| #9 | Vertex-block concentration, cochromatic induced capacity, rare-seed inversion and amplification infrastructure |
| #10 | Exact bounded-profile enumeration and first-moment formula |
| #11 | Finite profile duality, variational calculus, chromatic reduction |
| #12 | Growing-support analytic bricks, overlap foundations, first Section VIII atoms |

### Exact overlap/configuration-model counting

| PR | Main mathematical content |
|---:|---|
| #13 | Citation refresh and first stub-allocation atom |
| #14 | Stub allocations, prescribed-demand numerator, matching-extension counts |
| #15 | Embedding matching extensions |
| #16 | Global row/column stubs and configuration-model witnesses |
| #17 | Large self-contained partial checkpoint; closed unmerged, later work continued elsewhere |
| #18--#21 | Successive integrated formalization checkpoints, including Section VIII/IX and amplification bricks |

### Manuscript and accepted arithmetic leaves

| PR | Main mathematical content |
|---:|---|
| #22 | Rewritten and synchronized Problem 625 manuscript |
| #23 | Public artifact synchronization and updated Steiner citation |
| #24 | Checked Section IX finite arithmetic leaves |
| #25 | Small/large residual asymptotic scale adapters |
| #28 | Phase-root and midpoint formalization checkpoint |
| #29 | Derivative affine-core error bound |

PR #26 concerns Problem 593 and does not affect Problem 625.

---

## 3. Broad review and theorem-upgrade line

### PR #27: research notebook

PR #27 is a broad draft notebook containing corrected Section VII--IX notes,
experiments, and several possible theorem extensions. It is useful as a source
of ideas but should not be merged wholesale into the canonical proof without
splitting and rechecking its claims.

Surviving ideas were extracted into narrower PRs.

### PR #30: verified Section VII and IX simplifications

Main results:

1. stronger central partial-diagonal rate on the same domain;
2. direct injection
   \[
   F\mapsto F\setminus M
   \]
   on even edge sets after exposing a matching;
3. replacement of the large-residual cycle/walk enumeration by
   \[
   \sum_F\prod_{e\in F\setminus M}q_e
   \le\prod_{e\notin M}(1+q_e).
   \]

This was later formalized and integrated through PRs #34--#37.

### PR #31: root-gap constant propagation

Conditional deterministic result:

\[
 r_+-r_4^{\mathrm{co}}
 =\left(\frac{q^2}{4}A_4(\delta_n)+o(1)\right)
   \frac n{(\log n)^3}
\]

and midpoint placement retains one half, giving `/8`, not `/32`, in the final
coefficient. The PR verifies rounding and propagation, not the full second
moment.

### PR #32: stronger four-support entropy certificate

Exact certificate:

\[
 D_4(\delta)<\log(639/500),
 \qquad
 A_4(\delta)>\log(1000/639)
\]

uniformly in the limiting phase interval.

Combined with PR #31, the conditional uniform coefficient is

\[
 \frac{q^2}{8}\log(1000/639)
 =0.026896409808379\ldots.
\]

### PR #33: support-frontier diagnostic

The finite grid scan reports approximately

```text
{2,3,4,5,6}: 0.525994631053
{2,3,4,5}:   0.520701335491
```

so the fifth size gains only about `1.017%` while increasing the endpoint
transport dimension. This is numerical evidence, not a certified support
optimality theorem.

---

## 4. Focused Section IX closure line

### PR #34: finite matching-restriction product

Kernel-checked finite statements:

- deletion of an exposed matching is injective on even bipartite edge sets;
- weighted even-family sum is bounded by the full residual subset product;
- the fixed-family residual sum is bounded by the local-increment product times
  the residual-q product.

The cumulative audit later extracts the generic theorem:

\[
 \sum_{A\in\mathcal C}\prod_{e\in A\setminus I}q_e
 \le\prod_{e\notin I}(1+q_e)
\]

whenever deletion of `I` is injective on the finite family `C`.

### PR #35: direct actual-attachment envelope

Carries PR #34 through the literal capped attachment numerator and proves a
profile-level large-residual envelope of order

\[
 \exp\{O((\log n)^2)\}.
\]

### PR #37: q-only two-regime attachment theorem

Uses

\[
 \lambda_{ab}\le q_{ab}
\]

so both products are controlled by one total-q sum. It proves, over the literal
attained attachment sum,

\[
 \operatorname{AttachmentSum}_n
 \le
 \operatorname{BareSkeletonSum}_n
 \exp\left\{\varepsilon_n\frac n{(\log n)^4}\right\},
 \qquad\varepsilon_n\to0.
\]

The focused source branch was repaired and built successfully. PR #40 merged
this Section IX stack into the cumulative audit branch.

---

## 5. Focused Section VIII closure line

### PR #36: endpoint transport core

Kernel-checks the square-free, denominator-free form of the endpoint
transportation inequality. This is the exact finite algebra behind manuscript
Lemma 8.1.

### PR #38: AM--GM and all-high-deficit simplification

Replaces the Cauchy/table-family route by square-free AM--GM and one-sided
multinomial sums. It also replaces near/middle high-cell ranges by one
all-deficit geometric expansion using

\[
 h\left\lfloor\frac{2m}{3}\right\rfloor
 \le hm-\frac{h(h+1)}2.
\]

The paper-level resulting exponent is

\[
 O\bigl(n^{2/3}(\log n)^{4/3}\bigr)
 +O\bigl(\sqrt{n\log n}\bigr)
 =o\left(\frac n{(\log n)^4}\right).
\]

### PR #39: cumulative theorem/lemma audit

PR #39 integrates the Section VIII and Section IX simplification lines and
records the authoritative theorem frontier:

- Sections II--VII and X are structurally coherent;
- Section IX is reduced to the Section VIII bare-skeleton estimate;
- one global Section VIII physical-fibre/deficit theorem remains decisive;
- `Erdos625Statement` remains unproved.

It also contains the phase-resolved theorem, stronger coefficient, complement
corollary, balanced seed, reusable restriction-product theorem, and exact
regression ledger.

### PR #40: mechanical branch integration

Merged PRs #34, #35, and #37 into the head of PR #39. It makes no new
mathematical claim.

### PR #41: exact endpoint reference normalization

PR #41 proves:

1. the combined block-pairing and full-stub factorial quotient;
2. the common signed endpoint atom weight;
3. exact identification of the decorated sum with `fourEndpointW(L)`;
4. injectivity of the decorated-to-physical endpoint map.

It also contains a candidate reverse-data construction. That newest reverse
module must be directly built and audited before it is treated as proved.

The remaining endpoint task is surjectivity/two round trips. The remaining
global task is the aggregate all-deficit reindexing.

---

## 6. Current integration graph

The focused proof stack is

```text
#34 -> #35 -> #37
                \
                 #40 -> #39 -> #41 -> current value-upgrade PR
                /
#36 -> #38 ----
```

The theorem-upgrade PRs #31 and #32 were created independently from `main`.
Their mathematics is summarized and regression-checked in the cumulative audit,
but they should be cherry-picked or restated deliberately rather than merged
blindly with unrelated branch history.

PR #33 is diagnostic and need not be part of the canonical proof history.

---

## 7. Result classification

### Already finite/kernel checked

- exact graph and cochromatic definitions;
- many first-moment and phase-expansion bricks;
- exact signed overlap/cycle-space algebra;
- prescribed-demand and configuration-model finite counts;
- endpoint transport core;
- matching-restriction product;
- q-only literal attachment theorem;
- endpoint decorated reference normalization;
- decorated-to-physical endpoint injectivity;
- rare-seed concentration and deterministic completion infrastructure.

### Conditional on the remaining global Section VIII theorem

- Proposition 9.2;
- full-sequence `Omega(n/(log n)^3)` gap;
- phase-resolved `/8` coefficient;
- uniform coefficient `0.026896409808379...`;
- simultaneous complement corollary;
- balanced rare seed at the same exponential scale.

### New research targets

- near-root placement and `/4` coefficient;
- exact phase minimum of `A_4`;
- balance necessity for near-optimal cocolorings;
- slowly growing support and limiting coefficient `(ln 2)^3/4`;
- matching `O(n/(log n)^3)` upper bound;
- fixed-`p` extension;
- two-independent-graph alternative model.

---

## 8. Review policy

For every future PR, the description should state separately:

1. what theorem is proved in the PR itself;
2. which manuscript statements it assumes;
3. whether the result is finite, asymptotic, computational, or diagnostic;
4. whether the exact focused target is compiled by CI;
5. whether the PR changes the canonical theorem statement;
6. whether it changes the external claim status.

No green root build should be used to certify a newly added isolated Lean module
unless that module lies in the root import closure or has its own focused build.
