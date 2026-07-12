# Adversarial leap audit of the complete proof

**Date:** 2026-07-13
**Canonical manuscript:** ../proofs/COMPLETE_PROOF_SELF_CONTAINED.md
**Verdict after revision:** **internal PASS; no blocking logical failure found.**

This is an internal mathematical audit, not external peer review, formal
verification, publication, priority verification, or community acceptance.
The target was treated as unproved throughout the review.

## 1. Exact target

For \(G_n\sim G(n,1/2)\), the manuscript claims

\[
 \Pr\left\{\chi(G_n)-\zeta(G_n)\ge
 \frac{(\ln2)^2}{32}\ln\frac{200}{153}
 \frac{n}{(\ln n)^3}\right\}\longrightarrow1
\]

along the full integer sequence.  The audit checked the root asymptotics,
integer profile construction, exact signed overlap representation, complete
second-moment summation, rare-event amplification, rounding, and probability
quantifiers.  Numerical diagnostics were kept separate from proof.

## 2. Independent review split

Three read-only reviews were performed independently before the manuscript
was changed.

1. Sections 1--5: phase expansion, root geometry, support loss, signed root,
   and tangent integer rounding.
2. Sections 6--8: exact sign sum, all partial diagonals, dense transport, and
   every high-cell multiplicity.
3. Sections 9--11: residual local/cycle attachments, normalized second
   moment, amplification, and the final full-sequence conclusion.

After the repairs, the same three routes were reviewed again against the
patched text.

## 3. Severity-ranked findings and dispositions

| Severity | Original proof obligation | Finding before revision | Repair now in the canonical manuscript | Regression result |
|---|---|---|---|---|
| Major | Lemma 3.1 and (5.9)--(5.11) | The derivative was stated only near ordinary roots, then used on the segment to the not-yet-localized signed root. This was circular. | Lemma 3.1 now proves a uniform corridor for every zero of \(L_S+ck\), \(0\le c\le q\), and proves the derivative throughout that corridor; both roots are localized before the mean-value theorem. | PASS |
| Major | Lemma 8.3, (8.25)--(8.30) | Per-cell and conditional bounds were not explicitly promoted to the global sum of all high skeletons, leaving a hidden-multiplicity/dependence risk. | Equations (8.25a), (8.26a), and (8.29a)--(8.29b) now give the endpoint-decoration product, joint threshold expansion, two residual-mass branches, and final conditioned global sum. | PASS |
| Major formal overclaim, theorem-local | Lemma 9.1 | The statement claimed \(\log\mathcal A=o(n/N^4)\), but the proof supplied only an upper bound and the cap indicator can make \(\mathcal A<1\). | Lemma 9.1 now states exactly the one-sided estimate needed by Proposition 9.2, including explicit \(\exp(CN^8)\) and \(\exp(Cn/N^5)\) bounds. | PASS |
| Moderate | Lemma 3.1, (3.8)--(3.9) | Uniform bounded tilts, dominated convergence, and optimizer convergence were compressed. | Equations (3.8a), (3.9a), and (3.9b) state the finite value function, a fixed compact mean interval, uniform tilt/value convergence, and uniform positivity of the four optimizer coordinates. | PASS |
| Minor | Lemma 7.1 | The sentence using \(R\le47/100\) omitted the already-required domain \(R\ge1/64\). | The numerical rate is now stated on \(1/64\le R\le47/100\), and the domination of the entropy/Stirling errors is explicit. | PASS |
| Minor | Lemma 8.3 | The one-turn monotonicity and the small-residual multiplicity premise were compressed. | Equation (8.24a) proves log-convexity; the small branch now uses the exact residual-degree implication \(r_e\le a\), hence \(\binom{r_e}{2}\le(a-1)r_e/2\). | PASS |
| Minor | (5.14)--(5.16) | Raw and effective multipliers were conflated, and the signs of the two rounding errors were undefined. | The multipliers and signed errors are now defined, and both constraint-cancellation identities are displayed. | PASS |
| Minor | Lemmas 10.1--10.2 | The \(cN\) greedy count and the use of a growing deterministic \(r_n\) were implicit. | Equation (10.3a) gives the recurrence; Lemma 10.2 is uniform for deterministic \(r=r(n)>0\) with a common \(\varepsilon_n=o(1)\). | PASS |
| Minor | (10.12)--(11.1) | An anonymous \(o(n/N^3)\) appeared inside the probability event, and the final intersection referred to equation numbers as events. | The deterministic sequence \(a_n\) and its tail bound are explicit in (10.12)--(10.13), and the two events are named in Section 11. | PASS |

No repair changes the claimed theorem, the constant
\((\ln2)^2\ln(200/153)/32\), the four class sizes, or the full-sequence
high-probability quantifier.

## 4. Reconstructed dependency chain

The audited logical order is:

\[
\begin{gathered}
\text{phase expansion and uniform root corridor}\\
\Downarrow\\
\text{unrestricted chromatic lower location}
\quad+\quad
\text{four-size signed midpoint with positive first moment}\\
\Downarrow\\
\text{exact sign sum and exact partial diagonals}\\
\Downarrow\\
\text{endpoint transport + near/middle high-cell globalization}\\
\Downarrow\\
\text{uniform one-sided residual attachment bound}\\
\Downarrow\\
\log\frac{\mathbb EZ^2}{(\mathbb EZ)^2}=o(n/N^4)\\
\Downarrow\\
\text{Paley--Zygmund seed + deterministic-sequence amplification}\\
\Downarrow\\
\chi(G_n)-\zeta(G_n)\ge
\left(\frac{q^2\gamma_4}{16}-o(1)\right)\frac n{N^3}
\quad\text{with high probability.}
\end{gathered}
\]

The profile is constructed before any second-moment conclusion is used.
Lemma 7.1 depends only on first-moment/profile facts; Lemmas 8.1--8.3 then
use Lemmas 6.2 and 7.1; residual topology is added only afterward.  No
circular second-moment input remains.

## 5. Independent finite diagnostics

After the proof repairs,
verification/erdos625_independent_checks.py passed all five groups:

- Lemma 6.1 sign-sum identity on 625 overlap matrices;
- exact normalized signed second moment for \(n=6\), profile \((3,3)\);
- Lemma 6.2 on 4,170 finite prescribed-cell cases;
- Lemma 8.1 on 2,901 typed transportation tables, maximum ratio \(1\);
- exact near-containment ratio (8.21) on 684 cases.

Additional diagnostic scans checked:

- the Lemma 5.1 four-size tilt and omitted-mass constant over the entire
  phase interval;
- the two Lemma 7.1 rate bounds on their stated \(R,T\) domains;
- the log-convex one-turn inequality in (8.24a) over a wide finite range;
- representative dense four-type transportation matrices.

These computations are transcription and counterexample diagnostics only;
they are not used as proof of an asymptotic statement.

## 6. Remaining verification boundary

No unresolved mathematical obligation was identified by these audits after
the repairs.  The strongest remaining verification steps would be external
specialist peer review and/or proof-assistant formalization of the four
concentrated asymptotic modules:

1. the uniform root/optimizer lemma;
2. the complete partial-diagonal rate;
3. the conditioned global high-skeleton expansion;
4. the weighted residual cycle expansion.

Until one of those stronger processes is completed, the accurate status is:
**candidate all-\(n\) solution, strengthened and internally audited, not
externally or formally verified.**
