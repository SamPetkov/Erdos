# Full mathematical re-audit of the Erdős 625 TeX

**Date:** 26 July 2026  
**Audited source:** `625/arxiv/main.tex` on `agent/625-value-upgrade-program`  
**Source blob:** `c4d090b73cd5efcdb98cc30f79bb5f53c6c9bc97`  
**Scope:** every section from the phase expansion through the final event intersection, together with the theorem upgrades proposed in PR #43

## 0. Status vocabulary

This audit uses five labels.

- **GREEN:** no new mathematical defect was found in the stated argument, subject to its declared inputs.
- **AMBER:** the idea is plausible or correct at fixed parameters, but a quantitative uniformity statement is still missing for the proposed extension.
- **RED:** the canonical TeX currently relies on a global identification or estimate that has not been supplied by the checked public/private proof stack.
- **BLUE:** a theorem-strength or proof-simplification improvement that should be incorporated after closure.
- **TYPO:** a source-level mathematical notation error that should be corrected even though the intended formula is clear.

A GREEN label is not external peer review and is not a claim that the corresponding section has been completely formalized in Lean.

---

## 1. Executive verdict

### 1.1 The unique submission-blocking proof seam remains Section VIII

The decisive unresolved theorem is the **weight-preserving physical-fibre and all-deficit reindexing** behind Lemma 8.3. The canonical TeX moves from a partial high physical matching to a full-containment reference table as though the relevant objects were obtained by independently decorating distinguished full cells. A partial physical stub matching generally has many full completions, and some of its unused stubs may participate in residual cells. Therefore the required argument is not an objectwise completion bijection.

The correct statement is aggregate. For a fixed block-level matching support `P`, endpoint multiplicities `m_e`, deficits `h_e`, and actual multiplicities `j_e=m_e-h_e`, one must first sum the partial physical stub-matching fibre. Its aggregate weight is

\[
 w(P,j)=
 \frac{\prod_{e\in P}(s_e)_{j_e}(t_e)_{j_e}}
      {(n)_J\prod_{e\in P}j_e!}
 \prod_{e\in P}g(j_e),
 \qquad J=\sum_{e\in P}j_e.
\]

The exact one-cell aggregate ratio is

\[
 R_{m,d}(h)=
 \frac{\binom mh}{(d+1)(d+2)\cdots(d+h)}
 2^{-hm+h(h+1)/2},
\]

and the single global denominator ratio is

\[
 \frac{(n)_{J+H}}{(n)_J}=(n-J)_H\le n^H,
 \qquad H=\sum_eh_e.
\]

Only after establishing the exact finite reindexing may one conclude

\[
 \frac{w(P,m-h)}{w_{\rm full}(P)}
 \le\prod_{e\in P}n^{h_e}R_{m_e,d_e}(h_e).
\]

PR #41 closes the full-endpoint reference normalization and proves injectivity of the decorated-to-physical map. A candidate reverse-data construction exists, but the reverse map, its round trips, and the global partial-deficit fibre identity are not yet accepted. The private DAG independently identifies this same seam and rejects a generic subexponential-sum wrapper as insufficient.

**Verdict:** Lemma 8.3, Proposition 9.2, and the main theorem remain conditional until this finite global theorem is checked.

### 1.2 No second independent fatal gap was found outside that seam

Sections 2--7 and 10--11 form a coherent dependency chain when Proposition 9.2 is supplied. The exact signed-overlap identity, partial-diagonal recurrence architecture, chromatic lower reduction, and rare-seed amplifier remain mathematically compatible with the newer Section VIII--IX route.

This does not mean that the existing Section VIII--IX prose should be retained. The canonical TeX still presents the older near/middle and cycle-kernel proofs. The newer aggregate all-deficit and matching-restriction route is shorter, more exact, and better aligned with the checked finite modules.

### 1.3 Three proposed upgrades in PR #43 need narrower statements

1. **Near-root placement:** `theta_n log n -> infinity` is presently only a proposed sufficient criterion. The exact placement dependence of every use of the positive first-moment margin has not yet been collected in one theorem. The candidate `theta_n=(log n)^(-1/2)` remains plausible, but the roadmap must not present the criterion as established before the replay is done.
2. **Balance necessity:** replacing `2^k` by `binom(k,rho k)` proves a stability statement inside the selected four-size signed witness family. It does not exclude arbitrary imbalanced cocolorings using different class-size profiles. Global necessity requires a first-moment union bound over all signed profiles.
3. **Slow-support complexity:** if a dimension-dependent second-moment exponent is written as `K(m)n/(log n)^4`, then `K(m_n)=o(log n)` is not enough. The required condition is directly `Lambda(n,m_n)=o(n/(log n)^4)`. A complexity envelope must be compared with the actual smaller fixed-support error scale, not multiplied by the target scale itself.

### 1.4 The canonical theorem constant is unnecessarily weakened

The source loses fixed factors after the phase-resolved root displacement. The correct midpoint propagation is

\[
 \chi(G_n)-\zeta(G_n)
 \ge
 \left[
  \frac{(\ln2)^2}{8}\bigl(\ln2-D_4(\delta_n)\bigr)-o(1)
 \right]\frac{n}{(\ln n)^3}.
\]

Combining this with the stronger exact entropy certificate gives

\[
 \frac{(\ln2)^2}{8}\ln\!\left(\frac{1000}{639}\right)
 =0.026896409808379\ldots,
\]

about `6.68735` times the displayed coefficient in the canonical TeX.

---

## 2. Section-by-section audit table

| TeX layer | Verdict | Mathematical conclusion | Required action |
|---|---:|---|---|
| Abstract and Theorem 1 | RED/BLUE | The statement depends on the unresolved Section VIII global theorem; its coefficient is also weaker than necessary. | Keep candidate status until closure; then replace by the phase-resolved theorem and stronger corollary. |
| Section 1, elementary tools | GREEN | The stated Stirling, bounded-differences, Paley--Zygmund, binomial-tail, and Markov forms are compatible with later uses. | No mathematical rewrite required. |
| Section 2, complete phase | GREEN | The phase expansion and adjacent-size consequences are internally consistent and uniform on the attained phase interval. | Clarify that `delta=1` is used only as a continuous endpoint extension. |
| Section 3, continuous roots | GREEN for fixed placement; AMBER for shrinking placement | Root corridor, derivative, and support comparison are coherent. | For `theta_n->0`, collect a quantitative placement-uniform theorem rather than relying on a generic error slogan. |
| Section 4, chromatic lower location | GREEN | The bounded-profile first moment plus the independence-number cap removes the apparent profile restriction. | No structural change. |
| Section 5, signed first moment | GREEN/BLUE | The root displacement is the main phase-sensitive theorem. The later constant propagation is over-conservative. | Insert the stronger entropy certificate and retain the full `/8` midpoint coefficient. |
| Section 6, exact signed overlap | GREEN | The compatible-sign count and prescribed-cell bound are exact finite statements. | Promote the cycle-space identity as a named reusable proposition. |
| Section 7, partial diagonals | GREEN with one TYPO and one BLUE improvement | The empty/central/full corner architecture is coherent for the fixed midpoint profile. | Fix `2^ell_bullet`; replace decimal central-rate checks by the exact stronger rational certificate; expose placement dependence for `theta_n`. |
| Section 8, endpoint/high skeletons | RED | Full endpoint normalization is now checked, but the attained partial physical-fibre/all-deficit reindexing is missing. | Replace the old near/middle proof by the aggregate all-deficit theorem. |
| Section 9, residual attachments | GREEN on the newer q-only route; obsolete canonical route | The public q-only matching-restriction chain controls the literal attained attachment sum. | Replace cycle/walk enumeration by the direct restriction-product theorem and two-regime assembly. |
| Section 10, amplification | GREEN/BLUE | The one-Lipschitz capacity argument and simultaneous leftover coloring give the claimed tunable tail. | State the tunable tail as a named proposition. |
| Section 11, event intersection | GREEN conditional on Proposition 9.2; BLUE coefficient | The union-bound intersection is valid. | Use the phase-resolved coefficient and add the complement-symmetric corollary. |
| PR #43 near-root target | AMBER | Plausible; `theta=N^{-1/2}` is a strong candidate. | Replace the asserted criterion by an explicit list of quantities that must be `o(theta n/log n)` or uniform at `k_theta`. |
| PR #43 balance necessity | AMBER/overstated | Valid for the selected four-size witness family; not yet for arbitrary cocolorings. | Restrict the theorem or first prove an all-signed-profile lower location. |
| PR #43 slow support | AMBER/correction required | The limiting coefficient is plausible, but the complexity criterion is dimensionally wrong as written. | Require `Lambda(n,m_n)=o(n/(log n)^4)` directly. |
| PR #43 cochromatic corridor | AMBER/correction required | The present midpoint construction gives an upper location near the midpoint, not `r_4^co+o(H_n)`. | Make the latter conditional on the near-root theorem. |

---

## 3. Abstract, introduction, and theorem statement

### 3.1 Claim boundary

The abstract says “We prove” the final full-sequence theorem. That wording becomes appropriate only after the Section VIII reindexing theorem has been supplied and the integrated proof has been independently reviewed. Until then, the repository should retain candidate-proof language outside the frozen manuscript.

### 3.2 The theorem should be phase-resolved

Let

\[
 A_4(\delta)=\ln2-D_4(\delta),
 \qquad H_n=\frac{n}{(\ln n)^3}.
\]

The strongest theorem already latent in the fixed-midpoint architecture is

\[
 \Pr\!\left(
  \chi(G_n)-\zeta(G_n)
  \ge\left[\frac{(\ln2)^2}{8}A_4(\delta_n)-o(1)\right]H_n
 \right)\to1.
\]

This statement preserves the genuine phase information. The uniform numerical constant should be a corollary, not the main theorem.

### 3.3 Background additions

The historical paragraph should eventually include the origin and generalized-coloring framework already identified in PR #41:

- Lesniak--Straight for the cochromatic number;
- Erdős--Gimbel--Straight and Erdős--Gimbel--Kratsch for early extremal/comparison theory;
- Scheinerman and Bollobás--Thomason for generalized chromatic numbers of dense random graphs;
- Gimbel--Kündgen--Molloy only as adjacent fractional work.

These are background improvements, not proof dependencies.

### 3.4 Roadmap must match the new proof

The introduction currently says that Section 8 treats near/middle high cells and Section 9 pays for cycle attachments by a separate cycle-kernel argument. A Version 2 roadmap should instead say:

1. Section 8 identifies the exact physical high-skeleton fibres, compares every deficit to the full endpoint reference, and sums one all-high geometric product;
2. Section 9 uses injective restriction outside the exposed matching and one q-only two-regime estimate for the literal attained attachment sum.

---

## 4. Sections 1--2: elementary estimates and the complete phase

### 4.1 Elementary inequalities

No incompatibility was found between the displayed forms and their uses. In particular:

- Lemma 10.2 uses `n-1` independent vertex blocks, which is consistent with the general parameter `r` in the bounded-differences statement;
- the one-sided bounded-differences exponent used in (10.7)--(10.8) has the correct factor `2/(n-1)`;
- the lower-quarter binomial estimate is more than sufficient for Lemma 10.1.

### 4.2 Phase endpoint convention

The actual phase satisfies `0<=delta<1`. Lemma 5.1 and the research upgrades use the compact closure `[0,1]`. The paper should state once that all limiting phase functions extend continuously to `delta=1`; no integer `n` is asserted to attain that endpoint.

### 4.3 Adjacent-size consequences

The ratios

\[
 \frac{\mu_{s+1}}{\mu_s}=\frac{n-s}{s+1}2^{-s},
 \qquad
 \frac{\mu_{s-1}}{\mu_s}=\frac{s}{n-s+1}2^{s-1}
\]

correctly give the upper independence-number cap and the lower first-moment scale needed in Section 7. No new gap was found here.

---

## 5. Section 3: continuous roots

### 5.1 Fixed-corridor argument

The affine-plus-curved decomposition, Gaussian domination, bounded selected tilts, positive variance floor, and envelope derivative form a coherent proof of the root corridor and slope for fixed `c in [0,ln 2]`.

### 5.2 Uniform support comparison

For the four-size support, compact-uniform convergence of the optimizer and its positive coordinate floor is exactly what is needed for the finite integer correction in Section 5. For the unrestricted support, the Gaussian majorant controls the moving finite cutoff.

### 5.3 New quantitative lemma needed for shrinking placement

The proposed near-root theorem should not be reduced to the single sentence “all errors are `O(n/N^4)`.” Define the exact placement

\[
 k_{\theta_n}=\left\lceil
 r_4^{\rm co}+\theta_n(r_+-r_4^{\rm co})
 \right\rceil.
\]

A complete uniformity theorem should list separately:

1. the signed first-moment margin at `k_theta`, expected to be of order
   \[
   \theta_n\frac nN;
   \]
2. the finite profile/Stirling error, currently logarithmic;
3. the full-corner denominator `1/EZ`, which requires the preceding margin to dominate the polynomial number of residual profiles;
4. the normalized-second-moment error, which must remain `o(n/N^4)` uniformly in the moving profile;
5. the amplifier loss, which need only be `o(H_n)` for the final near-root coefficient.

The candidate `theta_n=N^{-1/2}` leaves a very large first-moment margin `n/N^{3/2}` and is therefore plausible. What remains missing is the theorem that every Section 7--9 constant is uniform over that moving placement.

---

## 6. Section 4: unrestricted chromatic lower location

The logic is valid:

1. profiles with exactly `k` nonempty parts and maximum size `alpha+1` are counted;
2. the number of bounded profiles contributes only `exp(O(N^2))`;
3. moving `ceil(N)` classes below the continuous root decreases the logarithmic first moment by order `N^3`;
4. on the event `alpha(G)<=alpha+1`, any coloring with at most `k` parts can be split to exactly `k` bounded nonempty parts.

This is a genuine unrestricted lower bound, not merely a lower bound inside the chosen four-size profile family.

---

## 7. Section 5: signed first moment and constants

### 7.1 Stronger entropy certificate

The old certificate

\[
 D_4(\delta)<\ln(153/100)
\]

should be replaced by the stronger exact certificate

\[
 D_4(\delta)<\ln(639/500),
 \qquad
 A_4(\delta)>\ln(1000/639).
\]

The newer proof uses rational interval bounds and should replace the longer decimal-tail calculation in the canonical TeX once reviewed.

### 7.2 Correct coefficient ledger

Equation (5.11) gives

\[
 r_+-r_4^{\rm co}
 =\left[\frac{(\ln2)^2}{4}A_4(\delta_n)+o(1)\right]H_n.
\]

At the rounded midpoint,

\[
 r_+-k_{\rm co}
 =\left[\frac{(\ln2)^2}{8}A_4(\delta_n)+o(1)\right]H_n.
\]

Subtracting `ceil(ln n)` and the amplifier's `o(H_n)` loss causes no further fixed halving. Therefore the fixed certified coefficient is

\[
 \frac{(\ln2)^2}{8}\ln(1000/639),
\]

not the `/32` coefficient currently displayed.

### 7.3 Integer correction

The corrections

\[
 \Delta k_2=e_1-3e_0,
 \qquad
 \Delta k_3=2e_0-e_1
\]

solve both conservation equations exactly. Since every limiting coordinate is bounded away from zero, bounded corrections preserve nonnegativity. The tangent Hessian loss is `O(1/k)` and is negligible.

### 7.4 Balanced seed is valid

Restricting to exactly `floor(k/2)` clique labels costs at most a factor `k+1` in the first moment and `(k+1)^2` in the normalized second moment. This gives a balanced **rare seed** at the same exponential scale. Preservation under amplification is a separate theorem.

---

## 8. Section 6: exact overlap representation

### 8.1 Exact sign sum

The support graph on cells of multiplicity at least two correctly encodes sign compatibility. The identity

\[
 2^{W+c(H)-|V(H)|}
 =\left(\prod_{a,b}g(r_{ab})\right)2^{\beta(H)}
\]

is exact, and the even-subgraph interpretation of `2^beta` is the binary cycle-space cardinality.

### 8.2 Prescribed-cell estimate

The row-stub choices, column-stub choices, local bijections, and one global falling factorial in (6.8) are correctly normalized. The later product majorant (6.9) is an upper bound and does not replace the exact denominator when exact cancellation is needed.

### 8.3 Expository improvement

The cycle-space identity and the generic restriction-product inequality should be stated as separate named finite propositions. This makes it transparent which parts are model-independent.

---

## 9. Section 7: partial diagonals

### 9.1 Source-level mathematical typo

Equation (7.2) contains

```tex
2^\ell_\bullet
```

but the intended factor is

```tex
2^{\ell_\bullet}.
```

Without braces the TeX expression places `ell` in the superscript and the bullet in a subscript. This is a notation error even though the subsequent recurrence uses the intended quantity.

### 9.2 Empty and full corners

The forward recurrence is controlled by the large value of `mu_{alpha-2}` and its neighboring sizes. The reverse recurrence is controlled by the small first moment on at most `n/32` residual vertices. The polynomial number of four-coordinate residual profiles is absorbed by the positive signed first-moment margin.

### 9.3 Central rate

The entropy/Stirling reduction and the two linear bounds on `Phi_T` are coherent. The paper currently uses decimal endpoint checks and constants `1/5000` and `1/200`. PR #30 supplies an exact rational strengthening to `1/100` on the relevant central domain. The stronger exact certificate should replace the decimal prose.

### 9.4 Placement dependence

For a moving placement `theta_n`, the full-corner estimate no longer has a fixed `c_Z k` exponent. It has an exponent of expected order

\[
 \theta_n\frac nN.
\]

A near-root theorem must prove that this still dominates the polynomial profile count and every error used in the central estimate. For `theta_n=N^{-1/2}` it does, but this comparison has not yet been written as a theorem.

---

## 10. Section 8: exact diagnosis and replacement

### 10.1 What is already closed

The checked stack now supplies:

- the endpoint block-pairing factorial identity;
- the full-cell stub-matching cardinality;
- their combined quotient;
- the exact equality between the decorated endpoint reference sum and `W(L)`;
- injectivity of the decorated-to-physical endpoint map;
- the square-free endpoint transport inequality;
- the one-cell all-high deficit arithmetic;
- the generic optional-deficit product bound.

Thus the endpoint factorial bookkeeping is no longer the issue.

### 10.2 What is not closed

The missing theorem must identify the actual attained physical high-skeleton family with the aggregate block-support/deficit/partial-stub parameterization and preserve its weight. Specifically, it must prove that summing the local partial physical fibres gives the aggregate formula `w(P,j)` and that the collection of all such fibres is a disjoint reindexing of the canonical high-skeleton sum.

The reverse endpoint construction alone is not enough: nonendpoint deficits use partial local matchings, not the full local matchings of the endpoint fibre.

### 10.3 Why the old near/middle prose should be removed

The canonical proof says that one may distinguish full endpoint cells and independently assign deficits, with “no additional multiplicity.” That conclusion is true only after proving the aggregate fibre formula. It does not follow from an objectwise unique completion.

The old proof also contains finite summation ranges of the form

```text
j <= 3a/4 + O(1),
```

which are not exact finite statements. They must be replaced by typewise integer cutoffs, or eliminated by the single all-high route.

Finally, Step IV bounds residual local and cycle factors inside a lemma whose contract says those factors are deferred to Section 9. Because those factors are at least one, the resulting inequality may still be an upper bound, but the stated division of labour is no longer literally true and the same residual structure is then charged again in Proposition 9.2.

### 10.4 Recommended all-deficit replacement

For every positive deficit with `2h<m`, prove

\[
 n^hR_{m,d}(h)
 \le
 \left(\frac{nm}{2^{\lfloor2m/3\rfloor}}\right)^h.
\]

Let

\[
 \rho_n=
 \max_{\alpha-5\le m\le\alpha-2}
 \frac{nm}{2^{\lfloor2m/3\rfloor}}
 =O\!\left(\frac{N^{7/3}}{n^{1/3}}\right).
\]

For large `n`, `rho_n<=1/2`, and one selected block cell contributes at most

\[
 1+\sum_{h\ge1}\rho_n^h
 \le1+2\rho_n.
\]

Since a block support is a matching with at most `k_co` cells, all deficits cost at most

\[
 (1+2\rho_n)^{k_{\rm co}}
 =\exp\{O(n^{2/3}N^{4/3})\}.
\]

Combine this with the endpoint AM--GM transport estimate

\[
 \sum_LW(L)
 \le\exp\{O(\sqrt{nN})\}\sum_rD(r)
 =\exp\{O(\sqrt{nN})\}
\]

to obtain

\[
 \operatorname{BareSkeletonSum}_n
 \le
 \exp\{O(n^{2/3}N^{4/3})+O(\sqrt{nN})\}
 =\exp\{o(n/N^4)\}.
\]

This proof has one global finite seam and no near/middle residual split.

---

## 11. Section 9: direct q-only replacement

### 11.1 Generic restriction theorem

If deletion of a coordinate set is injective on a finite subset family, then

\[
 \sum_{A\in\mathcal C}\prod_{e\in A\setminus I}q_e
 \le\prod_{e\notin I}(1+q_e).
\]

For even edge sets, deletion of the exposed matching is injective because their symmetric difference would be an even subset of a matching.

### 11.2 Consequence for the literal attachment

The new route applies this product bound directly to the attained residual attachment. Since

\[
 \lambda^{\rm loc}_{ab}\le q_{ab},
\]

both the local-increment product and the outside-matching even-subgraph product are charged to one total-q sum. In the intrinsic regime `2^U<=m^3`, this gives an `exp(O(U^2))` bound. In the complementary regime, the exact implication

\[
 m<2^{\lceil U/3\rceil}
\]

combines with the deterministic residual bound.

The final theorem should be stated directly in aggregate form:

\[
 \operatorname{AttachmentSum}_n
 \le
 \operatorname{BareSkeletonSum}_n
 \exp\{o(n/N^4)\}.
\]

This is cleaner than proving a separate cycle-kernel supremum for every skeleton and then multiplying.

### 11.3 Canonical TeX action

Remove the simple-cycle decomposition, residual-walk kernel, mixed matching-cycle encoding, `tau`, and `h tau` from the main proof. They may remain in the repository as an independently interesting older route, but they should not be the authoritative Version 2 argument.

---

## 12. Section 10: rare-event amplification

### 12.1 Simultaneous leftover coloring

The complement-density union bound and nested-neighborhood argument correctly produce an independent set of size `c log n` inside every set of size at least `n^{1/3}`. Repeated removal gives the simultaneous coloring bound.

### 12.2 Capacity Lipschitz property

Changing one vertex-exposure block affects the maximum induced `k`-cocolorable capacity by at most one: deleting the affected vertex makes the two graph configurations identical on the surviving induced set. This justifies McDiarmid with `n-1` blocks.

### 12.3 Tunable tail

The general conclusion

\[
 \Pr\!\left(
 \zeta(G_n)>k_n+C\left[
 \frac{\sqrt{n\Lambda_n}+\sqrt{nr}}{N}+n^{1/3}+1
 \right]\right)
 \le e^{-r}+o(1)
\]

should be promoted to a named proposition. It is a reusable output and not merely an intermediate estimate.

---

## 13. Section 11: final theorem and corollaries

### 13.1 Event intersection

The intersection of the chromatic lower event and cochromatic upper event uses only a union bound; no independence is needed. This part is correct once Proposition 9.2 is available.

### 13.2 Remove the two unnecessary fixed halvings

The canonical route obtains a phase-resolved root gap, then replaces it by a half-sized uniform gap, takes a midpoint, and finally halves the resulting coefficient once more to absorb an `o(1)`. The final two conservative steps are unnecessary once uniform continuity and the exact entropy slack are stated.

The Version 2 final theorem should retain

\[
 \frac{(\ln2)^2}{8}A_4(\delta_n)
\]

up to `o(1)`.

### 13.3 Complement corollary

Since `zeta(complement G)=zeta(G)` and `G(n,1/2)` is complement invariant,

\[
 \min\{\chi(G_n),\chi(\overline G_n)\}-\zeta(G_n)
 \ge c\frac n{N^3}
\]

holds with high probability for every certified main-theorem coefficient `c`.

---

## 14. Audit of the proposed new theorem programs

### 14.1 Near-root placement: retain as AMBER

The deterministic placement formula is exact and the final retained gap approaches the full root displacement when `theta_n->0`. The candidate `theta_n=N^{-1/2}` is conservative. The missing work is not a new entropy calculation; it is a uniform replay of the fixed positive first-moment margin through Sections 7--9.

The roadmap should define an explicit margin

\[
 M_n(\theta)=
 L_{S_4}(n,k_\theta)+(\ln2)k_\theta
 \asymp\theta\frac nN
\]

and list every proof error that must be `o(M_n(theta))` or uniform at the moving profile. Until this is done, `theta_nN->infinity` is a proposed sufficient criterion, not a proved lemma.

### 14.2 Balance stability: restrict the current theorem

The calculation with `binom(k,rho k)` proves:

> Among the chosen four-size signed profiles, a fixed imbalance in the sign labels shifts the signed first-moment root by a positive multiple of `H_n`.

It does not prove:

> Every arbitrary cocoloring within `o(H_n)` of the global optimum is balanced.

The latter requires excluding all alternative class-size profiles. That is an all-signed-profile first-moment theorem and belongs with the lower-location half of the matching-upper-bound project.

The immediate rigorous structural program is therefore:

1. balanced rare seed;
2. labelled-slot amplifier producing one near-optimal balanced cocoloring;
3. four-size witness-family stability;
4. global balance necessity only after all-profile exclusion.

### 14.3 Slowly growing support: correct the complexity condition

The target condition is

\[
 \Lambda(n,m_n)=o(n/N^4),
\]

where `Lambda(n,m)` is the logarithm of the normalized second-moment bound for support width `m`.

If one proves

\[
 \Lambda(n,m)\le K(m)B_n
\]

for a fixed-support error scale `B_n=o(n/N^4)`, then choose `m_n` so that

\[
 K(m_n)B_n=o(n/N^4).
\]

Writing `Lambda=O(K(m)n/N^4)` and imposing only `K(m_n)=o(N)` is insufficient; it would generally be larger than the required target scale.

The support itself must also be specified. A natural first choice is

\[
 S_m=\{-1,0,1,\ldots,m\},
\]

with `m=o(alpha)`, rather than the ambiguous phrase “m consecutive sizes.”

### 14.4 Cochomatic location corridor: make the upper side conditional

The present midpoint construction gives

\[
 \zeta(G_n)
 \le
 \frac{r_4^{\rm co}(n)+r_+(n)}2+o(H_n),
\]

not

\[
 \zeta(G_n)\le r_4^{\rm co}(n)+o(H_n).
\]

The latter follows only after a near-root placement theorem. The proposed corridor must therefore be split:

- current midpoint upper location, conditional on proof closure;
- near-root upper location, conditional on the new placement theorem;
- all-profile lower location, a separate new theorem.

### 14.5 Exact phase minimum

The envelope derivative formula is correct. Since

\[
 T_0'(\delta)=-1,
\]

the sign of `A_4'` is the sign of `lambda_4-lambda_infinity`. Directed interval arithmetic over finitely many target intervals is a credible rigorous route. The numerical value remains diagnostic.

### 14.6 General density and two-layer model

The one-class first-moment reward for `G(n,p)` is correct, but it should use notation different from the current local overlap factor `g(x)`. The overlap calculation becomes a component partition function with a size-dependent external field.

The two-independent-graph model has the same witness first moment but a different second moment. It must remain explicitly attributed and separate until the coupling and normalized moment are obtained from a primary source or proved in the paper.

---

## 15. Recommended Version 2 architecture

1. **Theorem statement:** phase-resolved `/8` theorem, stronger fixed constant as corollary, complement corollary.
2. **Sections 2--4:** retain, with only minor uniformity clarifications.
3. **Section 5:** replace the old entropy certificate; correct constant propagation; optionally add the balanced seed.
4. **Section 6:** retain exact sign and prescribed-cell identities; isolate reusable finite propositions.
5. **Section 7:** fix the TeX exponent, use the exact stronger central-rate certificate, and state placement dependence explicitly.
6. **Section 8:** replace all near/middle prose by the exact physical-fibre equivalence, aggregate local ratio, all-deficit geometric product, and endpoint AM--GM transport.
7. **Section 9:** replace cycle/walk enumeration by the matching-restriction q-only two-regime theorem.
8. **Section 10:** retain and promote the tunable tail.
9. **Section 11:** retain the union-bound intersection, insert the phase-resolved coefficient and corollaries.

This would shorten the technically most vulnerable part of the paper while strengthening its theorem.

---

## 16. Acceptance checklist before canonical rewrite

The canonical TeX should not be rewritten around the stronger theorem until the following are green on one integrated branch:

1. reverse endpoint physical-fibre map and both round trips;
2. exact partial-cell physical fibre and its cardinality/weight identity;
3. disjoint global reindexing of every attained canonical high skeleton;
4. aggregate deficit comparison with the single global denominator;
5. all-deficit product at the actual midpoint profile;
6. endpoint AM--GM summation at the actual table/margin types;
7. direct literal q-only attachment theorem;
8. exact normalized-second-moment composition;
9. line-by-line constant propagation from the phase root to the final event;
10. manuscript compilation, bibliography, equation-reference, and source-sync checks.

The stronger fixed coefficient, complement corollary, and tunable tail require no new random-graph mechanism after these gates are closed.
