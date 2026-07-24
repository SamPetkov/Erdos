# Erdős Problem 625 review sequence and integration roadmap

**Snapshot:** 24 July 2026, based on `main` commit
`cda78922ea6c87bfc81f9bf693374dd045dac624`.

**Status:** coordination and review record.  This file is not a proof, external
peer review, a priority claim, or a completed formal verification.  The
canonical manuscript remains a candidate solution and `Erdos625Statement`
remains unproved in Lean.

## 1. Purpose

A broad exploratory review originally accumulated in pull request #27.  The
mature parts have now been separated into narrow pull requests so that each
claim can be reviewed, tested, and integrated independently.  This file records
that separation, the dependency structure, the exact coefficient ledger, and
the recommended integration order.

## 2. Pull-request map

| PR | Role | Current classification |
|---|---|---|
| [#27](https://github.com/SamPetkov/Erdos/pull/27) | Broad revisions, Section 8 bookkeeping, alternative supports, non-midpoint placement, and corollaries | **Research notebook; keep draft** |
| [#30](https://github.com/SamPetkov/Erdos/pull/30) | Section 7 central-rate improvement and Section 9 residual-restriction simplification | **Focused result; ready for review** |
| [#31](https://github.com/SamPetkov/Erdos/pull/31) | Propagation of the phase-resolved root displacement through midpoint rounding and amplification | **Focused conditional result; ready for review** |
| [#32](https://github.com/SamPetkov/Erdos/pull/32) | Stronger exact four-support entropy certificate | **Focused conditional result; ready for review** |

The narrower PRs were created directly from the then-current `main`; they do
not depend on the branch history of #27.

## 3. Result isolated in PR #30

### 3.1 Central partial-diagonal rate

On the same domain as the central range of Lemma 7.1,

\[
 \Phi_T(z)\le -\frac{1-R}{100}
 \qquad\left(\frac1{64}\le R\le1\right),
\]

improving the manuscript's displayed coefficient `1/5000` to `1/100`.  The
proof uses the same two convexity intervals, with the endpoint signs certified
by rational logarithm bounds.

### 3.2 Residual restriction instead of cycle traversal

For the exposed high matching `M`, restriction

\[
 F\longmapsto F\setminus M
\]

is injective on even edge sets.  Therefore

\[
 \sum_{F\ \mathrm{even}}\prod_{e\in F\setminus M}q_e
 \le \prod_{e\notin M}(1+q_e)
 \le \exp\!\left(\sum_{e\notin M}q_e\right).
\]

Together with the corrected one-sided off-matching square-sum inequality and
the local increment estimate already used by the manuscript, this gives

\[
 \mathcal A(M,j)
 \le \exp\!\left\{C\left(U^2+\frac{U^4}{m_0}\right)\right\}.
\]

In the large-residual regime the cost is `exp(O(N^2))`, rather than the
manuscript's `exp(O(N^8))`.  This removes the simple-cycle decomposition,
residual-walk enumeration, mixed matching-cycle encoding, `tau`, and `h tau`
from that branch of the argument.

The finite injection and the generic product-to-exponential algebra already
have Lean counterparts.  The complete probability specialization is not yet
claimed as formally closed.

## 4. Result isolated in PR #31

The canonical phase-resolved root displacement is

\[
 r_+-r_4^{co}
 =\left(\frac{q^2}{4}\{q-D_4(\delta_n)\}+o(1)\right)
   \frac{n}{N^3}.
\]

For the midpoint integer and chromatic lower integer, exact floor/ceiling
arithmetic gives

\[
 k_\chi^- - k_{co}
 > \frac{r_+-r_4^{co}}2-N-3.
\]

Since `(N+3)/(n/N^3) -> 0` and amplification subtracts only `o(n/N^3)`, no
additional fixed halving occurs after the midpoint.  Conditional on the
canonical inputs and their asserted phase-uniformity, the surviving coefficient
is

\[
 \frac{q^2}{8}\{q-D_4(\delta_n)\}.
\]

Using only the existing manuscript certificate gives the phase-independent
coefficient

\[
 \frac{(\ln2)^2}{8}\ln\frac{200}{153}.
\]

PR #31 verifies the deterministic rounding and coefficient propagation; it
does not independently prove equation (5.11), the uniform `o(1)`, the second
moment, or amplification.

## 5. Result isolated in PR #32

For the same four-size support `{2,3,4,5}`, exact rational interval arithmetic
proves

\[
 D_4(\delta)<\ln\frac{639}{500},
 \qquad
 \ln2-D_4(\delta)>\ln\frac{1000}{639}.
\]

The certificate uses

\[
 \frac{49}{20}\ln2<\lambda_4<\frac{83}{20}\ln2
\]

and a split at `(29/10) ln 2`.  Its four omitted-weight estimates imply the
uniform omitted ratio `<139/500`.

PR #32 proves the elementary limiting certificate conditional on the same
variational dual comparison used by Lemma 5.1.  It does not independently
prove finite-to-limiting optimizer convergence or any later probabilistic
module.

## 6. Explicit coefficient ledger

Let

\[
 c_{\rm old}=\frac{(\ln2)^2}{32}\ln\frac{200}{153}.
\]

The four relevant coefficients are:

| Inputs accepted | Coefficient | Decimal value |
|---|---:|---:|
| Current canonical display | `((ln 2)^2/32) ln(200/153)` | `0.004021983962242...` |
| PR #31 only | `((ln 2)^2/8) ln(200/153)` | `0.016087935848968...` |
| PR #32 only, canonical `/32` propagation | `((ln 2)^2/32) ln(1000/639)` | `0.006724102452095...` |
| PR #31 and PR #32 | `((ln 2)^2/8) ln(1000/639)` | `0.026896409808379...` |

The combined value is about `6.69` times the currently displayed coefficient.
The table is a dependency ledger, not a request to change the canonical theorem
before the relevant reviews are accepted.

## 7. Dependency structure

```text
canonical phase/root and variational setup
             |
       +-----+------------------+
       |                        |
       v                        v
PR #31: rounding and      PR #32: limiting
constant propagation     entropy certificate
       |                        |
       +-----------+------------+
                   |
                   v
        possible constant integration

PR #30 is logically separate: it simplifies Sections 7 and 9 without relying
on either constant improvement.
```

In particular:

- #30 can be reviewed and merged first;
- #31 does not depend on the stronger certificate in #32;
- #32 does not depend on the `/8` propagation in #31;
- the combined constant should be integrated only after both reviews are
  accepted;
- #27 should not be used as the source of canonical replacement text while its
  Section 8 globalization remains under review.

## 8. Support-frontier diagnostic

The companion script `experiments/support_frontier_scan.py` scans every support
of size three through five that contains `{2,3}` and is contained in
`{2,...,8}`.  It minimizes the limiting advantage

\[
 q-D_S(T)
\]

over a 1001-point grid spanning the complete target interval.  The full
support is evaluated with cutoffs 80 and 100 as a truncation-stability check.
This is numerical diagnostic evidence, not a proof.

Selected results are:

| Support | Scanned minimum of `q-D_S` |
|---|---:|
| `{2,3,4,5,6}` | `0.525994631053` |
| `{2,3,4,5}` | `0.520701335491` |
| `{2,3,4,6,7}` | `0.399733765460` |
| `{2,3,5}` | `0.092144964328` |

Adding deficit `6` to the canonical support improves the scanned limiting
advantage by only about `1.017%`, while changing the dense transportation table
from `4 by 4` to `5 by 5`.  Removing deficit `4` produces a much larger loss.
The canonical support `{2,3,4,5}` therefore remains close to the practical
frontier between entropy advantage and proof complexity.

No support-replacement theorem is claimed.  A different support would require
a complete replay of integer rounding, partial diagonals, dense
transportation, high-skeleton summation, and residual attachments.

## 9. Recommended integration order

1. Review and merge PR #30.
2. Review PR #32's finite certificate and its variational interpretation.
3. Review PR #31's uniform root displacement, rounding, and final event
   intersection.
4. Open one canonical-integration PR only after those reviews are complete.
   That PR should update the canonical Markdown, generated TeX, PDFs, audit
   records, equation references, and displayed constant together.
5. Keep #27 as a research notebook until the complete Section 8
   labelled/unlabelled high-skeleton summation is independently closed.

## 10. Remaining highest-priority proof boundary

Further support or constant optimization is lower priority than the global
Section 8 bookkeeping.  The concentrated unresolved review obligation remains
the exact passage from canonical demand/witness/residual fibres to the complete
unlabelled high-skeleton sum, with every multiplicity and conditional
expectation factor explicit.

## 11. Reproduction commands

After the relevant branches are checked out, the focused scripts are:

```text
python 625/experiments/section7_section9_supercheck.py
python 625/experiments/root_gap_constant_supercheck.py
python 625/experiments/four_support_entropy_certificate.py
python 625/experiments/support_frontier_scan.py
```

The first three scripts accompany PRs #30--#32.  The fourth belongs to this
roadmap PR and is deliberately labelled diagnostic.
