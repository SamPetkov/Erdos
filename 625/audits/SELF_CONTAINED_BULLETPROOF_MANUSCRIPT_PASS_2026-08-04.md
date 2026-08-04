# Erdős 625: self-contained manuscript and formalization pass

**Date:** 4 August 2026  
**Base:** public PR #56, `agent/625-ams-manuscript-clarity`  
**Branch:** `agent/625-self-contained-bulletproof-manuscript`

## 1. Objective

The 13-page AMS draft in PR #56 is a polished proof synopsis, not a
self-contained paper. This pass turns it into a complete generated manuscript
that includes the canonical proofs of Sections 1--7 and 10, replaces Sections
8--9 by the shorter audited route, supplies a new final constant ledger, and
places the exact formalization status inside the PDF.

The editorial standard is reader-first mathematical exposition:

- every standard invariant is defined before use;
- every manuscript-specific proof object is distinguished from the standard
  graph-theoretic objects;
- finite identities, deterministic inequalities, asymptotic estimates, and
  probability conclusions are separated;
- no sentence substitutes for a load-bearing theorem;
- no private or public CI status is used as a proxy for a mathematical proof;
- the theorem status is visible in the PDF, not only in pull-request metadata.

## 2. Self-contained assembly

`625/scripts/build_self_contained_ams_v3.py` checks the exact Git-blob SHA of
`625/arxiv/main.tex`, extracts the complete canonical Sections 1--7 and 10 by
semantic section markers, converts the legacy ruled statement boxes to the
ordinary `amsthm` hierarchy, normalizes notation and mathematical English, and
inserts the audited replacement Sections 8, 9, and 11.

The generated manuscript therefore contains the full argument rather than only
an introduction, roadmap, and the two difficult replacement sections.

The generator fails closed if the canonical source changes. This prevents
line-number drift or a silent mixture of two different mathematical versions.

## 3. Status-safe front matter

The master TeX defines a compile-time switch:

```tex
\newif\ifErdosProofClosed
\ErdosProofClosedfalse
```

The default verification mode:

- prints an explicit status banner;
- states the target theorem conditionally on the remaining formal gates;
- uses an audit-safe abstract;
- keeps the publication switch disabled.

The publication mode may be enabled only after the checklist in Appendix A is
green on one integrated commit and has received independent mathematical
review.

## 4. Canonical Section VIII route

The former draft mixed two valid but different finite routes.

The sharp route assumes every local endpoint base is at most `1/2` and retains

```text
product_(i,j) (1 + 2 rho_ij)^(L_ij).
```

The coarse route defines the sum of the sixteen endpoint bases

```text
rho_16 = sum_(i,j) rho_ij
```

and needs only `rho_16 <= 1`, giving

```text
(1 + (alpha+1) rho_16)^K.
```

The main manuscript now uses the coarse route because it is the cleanest route
consumed by the private finite reduction. The sharp weighted regrouping is
stated separately as a stronger reusable result.

The new Section VIII contains complete statements and proofs of:

1. the completion-free aggregate high-skeleton weight;
2. the exact one-cell deficit ratio;
3. the one-global-denominator comparison;
4. the finite optional-choice product;
5. the coarse common-charge deficit sum;
6. exact unweighted and weighted reference regrouping;
7. square-free endpoint transport and multinomial summation;
8. the coarse phase corridor and the bound
   `rho_16 = O(log n / n^(1/4))`;
9. the final bare-skeleton estimate.

The sentence “endpoint transportation absorbs the remaining product” has been
removed. The endpoint transportation is now a named proposition with its
formulas and proof.

## 5. Self-contained Section IX

The replacement residual section now defines, rather than merely names,

```text
theta_ab
Delta_x
lambda_ab
q_ab
```

and proves the following sequence:

1. the exact conditional attachment decomposition;
2. the fixed-even-set threshold expansion;
3. injectivity of deletion outside the exposed matching;
4. the restriction-product bound;
5. pointwise `lambda_ab <= q_ab`;
6. the q-only envelope `A(M,j) <= exp(2 sum q_ab)`;
7. the intrinsic total-q estimate at scale `U^2`;
8. the complementary deterministic residual-size estimate;
9. the uniform attachment error;
10. the normalized signed second moment.

The legacy simple-cycle, walk-kernel, mixed-cycle, and `tau` calculations are
not part of the main exposition.

## 6. Constant ledger

The final section derives the phase-resolved coefficient before inserting a
fixed certificate:

```text
(log 2)^2/8 * (log 2 - D_4(delta_n)).
```

It then records the exact rational four-support certificate

```text
D_4(delta) < log(639/500),
log 2 - D_4(delta) > log(1000/639),
```

and obtains the fixed coefficient

```text
(log 2)^2/8 * log(1000/639)
  = 0.026896409808379...
```

The midpoint factor is justified directly: the root separation has coefficient
`/4`, midpoint placement retains one half, and all integer and amplification
corrections are lower order. No additional fixed halving is inserted.

## 7. Formalization appendix

Appendix A maps the paper-level results to exact private Lean declarations and
uses four explicit statuses: `welded`, `running`, `needs review`, and
`blocked`.

As of 4 August 2026:

- the Section VIII finite chain through the realized-table deficit sum is
  welded privately;
- the coarse phase corridor is welded;
- the exact common-charge theorem
  `eventually_fourEndpointThreeQuarterRho_le_one` has one approved, running
  Aristotle request and is not yet proof evidence;
- concrete phase inputs/chromatic tail, the four-size first-moment assembly,
  the complete partial-diagonal asymptotics, and the global final attachment
  assembly remain unclosed.

The appendix forbids enabling publication mode before those gates close.

## 8. Lean project recommendations

The current root imports hundreds of fine-grained modules, including legacy and
simplified routes. For publication, create a curated theorem-facing hierarchy:

```text
Erdos625/Paper/Phase.lean
Erdos625/Paper/FirstMoment.lean
Erdos625/Paper/PartialDiagonals.lean
Erdos625/Paper/HighSkeletons.lean
Erdos625/Paper/Attachments.lean
Erdos625/Paper/Amplification.lean
Erdos625/Paper/Main.lean
```

Keep an exhaustive internal root for historical development, but remove the
legacy cycle/walk route from the paper-facing dependency chain.

The remaining broad DAG nodes should be split before proof search. In
particular, partial diagonals should become:

```text
empty-corner estimate
central-rate negativity
full-corner asymptotic wrapper
partial-diagonal assembly
```

A machine-readable paper--Lean manifest should generate the formalization table
and axiom report automatically.

## 9. Validation contract

The dedicated workflow must:

- generate the body from the frozen canonical source;
- run the structural checker under ordinary and optimized Python;
- compile the complete AMS manuscript with BibTeX;
- reject unresolved references and citations;
- reject missing status markers, undefined proof-object notation, and the old
  synopsis-only transition sentences;
- require all numbered Sections 1--11 and Appendix A;
- require a substantial page and word count consistent with a full paper;
- upload the generated PDF and generated body as review artifacts.

A successful build validates the TeX assembly and editorial invariants. It is
not evidence that the remaining Lean or mathematical proof obligations have
closed.
