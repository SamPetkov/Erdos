# Erdős 625: canonical Version 2 reader-first prose revision

## Status

This is a manuscript-level exposition pass stacked on the corrected Version 2
roadmap.  It does not modify the frozen canonical TeX and does not convert the
remaining Section VIII closure theorem into a proved result.  The proposed text
is copy-ready only after the attained-demand/all-deficit physical-fibre theorem
and its aggregate weight identity have been checked.

The current proof frontier must remain explicit:

```text
attained canonical high skeleton
  <-> block support + admissible deficits + local partial physical matchings
```

with exact preservation of the aggregate weight.  Until this theorem is closed,
the normalized second moment, the final main theorem, and the stronger Version
2 constant remain conditional.

## Principal editorial diagnosis

The candidate manuscript contains the right global ideas but asks the reader to
learn the proof in the wrong order.  The first-moment root comparison is
conceptual.  The second-moment proof is a finite disintegration followed by two
small aggregate estimates.  The current exposition instead introduces much of
the technical vocabulary before the reader knows which quantity each section
is bounding.

The revision therefore imposes four rules.

1. **Three layers, stated immediately:** location, existence, amplification.
2. **One object dictionary before Section VIII:** profile blocks, block support,
   full multiplicities, deficits, physical matching fibres, endpoint tables,
   and residual attachments are never conflated.
3. **One aggregate formula per technical section:** Section VIII proves the
   bare-skeleton estimate; Section IX proves the conditional attachment estimate.
4. **No obsolete machinery in the main narrative:** the near/middle split,
   residual walk kernel, simple-cycle decomposition, mixed matching-cycle
   encoding, and polymer terminology are removed from Version 2 unless retained
   in a historical appendix.

## The proof in one paragraph

For \(G_n\sim G(n,1/2)\), an ordinary colouring requires every class to be
independent.  A cocolouring may declare each class either independent or
complete.  At density \(1/2\), the two declarations have the same probability
cost, so a partition into \(k\) classes gains an exact sign multiplicity
\(2^k\).  Restricting class sizes to four consecutive phase values creates a
signed first-moment root below the ordinary colouring root by order
\(n/(\log n)^3\).  An exact signed-overlap identity reduces the second moment to
partial diagonals, a matching of high cells, and a residual even-subgraph
attachment.  Summing all physical high-cell fibres through one global
falling-factorial denominator gives the bare-skeleton estimate; injective
restriction outside the exposed matching gives the residual estimate.  This
produces a positive-probability signed seed, and a leftover-colouring plus
bounded-differences argument amplifies it to high probability.  Intersecting
that event with the ordinary chromatic lower bound yields the gap.

That paragraph should end the first page of the paper.

## Recommended title and abstract

The title

> A Polynomial-Scale Gap Between the Chromatic and Cochromatic Numbers of a
> Random Graph

is accurate and should be retained.

The abstract should not lead with the original `/32` constant while the
corrected theorem architecture supports a different conditional Version 2
constant.  Two copy-ready variants are supplied in
`625/arxiv/READER_FIRST_FRONT_MATTER_V2.tex`:

- an audit-safe research-status abstract for the present branch;
- a post-closure publication abstract using the phase-resolved coefficient.

Only the second should be used in a submission, and only after the global
Section VIII theorem is complete.

## Recommended section order

```text
1. Introduction and theorem
2. Phase notation and one-class asymptotics
3. Ordinary-colouring location
4. Signed four-size location
5. Exact signed-overlap identity
6. Partial diagonals and canonical high support
7. Endpoint reference transport
8. Physical high-cell fibres and all deficits
9. Residual attachment by matching restriction
10. Positive-probability seed and amplification
11. Final event intersection
Appendix A. Exact phase and entropy certificates
Appendix B. Finite fibre identities and formalisation map
Appendix C. Superseded Section VIII--IX machinery
```

The current Sections 2--5 may remain largely intact, but their introductions
should say which root is being located and whether a statement moves the root or
only certifies a finite approximation.  Sections VIII and IX should be replaced
by the corrected aggregate route.

## Reader contract at the end of the introduction

The introduction should state the proof obligations in the following form.

### Layer I: location

- locate the ordinary-colouring root \(r_+(n)\);
- locate the signed four-size root \(r_4^{\mathrm{co}}(n)\);
- prove the phase-uniform separation
  
  \[
    r_+(n)-r_4^{\mathrm{co}}(n)
    =
    \left[
      \frac{(\log2)^2}{4}A_4(\delta_n)+o(1)
    \right]\frac{n}{(\log n)^3};
  \]
- place the signed seed at the midpoint, retaining one half of this separation.

### Layer II: existence

For the signed-profile count \(Z_n\), prove

\[
  \frac{\mathbb E Z_n^2}{(\mathbb E Z_n)^2}
  \le
  \exp\!\left\{o\!\left(\frac{n}{(\log n)^4}\right)\right\}.
\]

Every object in Sections 6--9 exists only to prove this displayed inequality.
Those sections do not alter the first-moment roots.

### Layer III: amplification

Use Paley--Zygmund to obtain a possibly rare seed, then use a one-Lipschitz
cocolourable-capacity variable and leftover colouring to obtain a
high-probability upper bound for \(\zeta(G_n)\).  Combine it with the independent
high-probability lower bound for \(\chi(G_n)\) by a union bound.

## Object dictionary

This dictionary should appear before the high-skeleton section.

| Object | Meaning | Do not confuse with |
|---|---|---|
| profile block | one actual colour or clique class | an abstract type slot |
| block atom | type/slot label used to organise blocks | a physical vertex set |
| high-demand table | actual high-cell multiplicities \(j_{ab}\) | the endpoint table |
| block support \(P\) | matching of block pairs with positive high demand | a matching of physical vertices |
| full multiplicity \(m_e\) | \(\min\{s_e,t_e\}\) for one support edge | actual multiplicity \(j_e\) |
| deficit \(h_e\) | \(m_e-j_e\) | residual attachment size |
| partial physical matching | literal size-\(j_e\) matching of stubs | a chosen full completion |
| endpoint table \(L\) | counts of support edges by endpoint types | the full high-demand table |
| bare skeleton | exposed high-cell data before residual attachment | the complete overlap table |
| residual attachment | conditional contribution of non-high cells | the high-cell deficit fibre |

A partial physical matching can have many full completions.  The proof compares
whole finite fibres; it never chooses a canonical completion objectwise.

## Section-by-section prose revision

### Introduction

Keep the historical background concise.  The introduction needs only:

1. the definition of the two parameters;
2. the Erdős--Gimbel question;
3. the theorem or current audited target;
4. the one-paragraph mechanism;
5. the three-layer reader contract;
6. a compact relation-to-prior-work paragraph.

The detailed chronology of phase-dependent partial results should be shortened
or moved to a background subsection.  It should not separate the theorem from
its proof mechanism by several pages.

Replace ornate phrases such as `exquisitely phase-sensitive` by direct
mathematical language such as `phase-sensitive but uniform over the full
threshold window`.

### Sections 2--4: ordinary location

Open the block with:

> These sections establish a lower location for the chromatic number without
> assuming that an optimal colouring has a prescribed profile.

At the end of each section, state explicitly what has been proved for the root
and what remains to convert it into a high-probability chromatic lower bound.

### Section 5: signed four-size root

Begin with the extra entropy in one sentence:

> At \(p=1/2\), declaring a class independent or complete has the same edge
> cost; summing the two choices contributes an exact factor \(2\) per class.

Then explain why four sizes are used: they cover the entire phase interval with
a uniform entropy advantage while keeping the transportation problem finite.
Do not introduce the full overlap machinery until the root displacement has
been stated and interpreted.

### Section 6: exact overlap identity

State the exact identity first and explain its terms afterward:

\[
  \operatorname{SignedOverlapWeight}(r)
  =
  \left(\prod_{a,b}g(r_{ab})\right)2^{\beta(H_r)}.
\]

Then say:

> The local product records cell multiplicities; the cycle-space factor records
> the remaining sign compatibility.  This is an exact finite identity, not an
> approximation.

### Section 7: partial diagonals

The section title and opening should say that common whole classes are being
removed.  The central-rate estimate is an input to the normalized second moment,
not a new random-graph location theorem.

### Section 8: physical high-cell fibres

Replace the old near/middle narrative by the following spine.

1. canonical high support is a block matching;
2. for fixed support \(P\) and multiplicities \(j_e\), the literal physical
   fibre has aggregate weight
   
   \[
     w(P,j)
     =
     \frac{\prod_{e\in P}(s_e)_{j_e}(t_e)_{j_e}}
          {(n)_J\prod_{e\in P}j_e!}
     \prod_{e\in P}g(j_e);
   \]
3. compare \(j_e=m_e-h_e\) with the full endpoint reference;
4. use the single global denominator ratio
   
   \[
     \frac{(n)_{J+H}}{(n)_J}=(n-J)_H\le n^H;
   \]
5. sum every deficit through one geometric product;
6. transport the full endpoint reference by square-free AM--GM.

The result of the section is one displayed statement:

\[
  \operatorname{BareSkeletonSum}_n
  \le
  \exp\!\left\{o\!\left(\frac{n}{(\log n)^4}\right)\right\}.
\]

Every lemma should be introduced by saying which factor in this bound it
controls.

### Section 9: residual attachment

Begin with the injection, not with cycle terminology:

> Deleting the exposed matching is injective on even residual edge sets.

Then derive

\[
  \sum_{F\ \mathrm{even}}
    \prod_{e\in F\setminus M}q_e
  \le
  \prod_{e\notin M}(1+q_e).
\]

Charge the local increment and even-subgraph products to the same total-\(q\)
bound.  The section ends with

\[
  \operatorname{AttachmentSum}_n
  \le
  \operatorname{BareSkeletonSum}_n
  \exp\!\left\{
    \eta_n\frac{n}{(\log n)^4}
  \right\},
  \qquad \eta_n\to0.
\]

No residual walk kernel, simple-cycle decomposition, traversal parameter, or
polymer surrogate should appear in the Version 2 main text.

### Sections 10--11: amplification and intersection

Make the logic explicit:

- the second moment gives positive probability, not high probability;
- the amplification variable is one-Lipschitz under vertex exposure;
- leftover colouring absorbs uncovered vertices at lower order;
- the chromatic and cochromatic events need not be independent;
- a union bound is sufficient.

## Standard transition paragraphs

Before ordinary location:

> We first locate the ordinary colouring threshold.  This part of the argument
> contains no signed structure and will later supply the lower bound for
> \(\chi(G_n)\).

Before the signed profile:

> We now repeat the location calculation with signed classes.  The sole new
> first-moment resource is the exact choice between independent and complete
> classes.

Before the overlap identity:

> The first moment identifies a lower signed root.  To show that this root is
> attained, we must control the overlap of two signed partitions.

Before Section VIII:

> After common whole classes are removed, every canonical high cell belongs to
> a matching.  We sum these high cells by their literal physical matching fibres
> and their deficits from full containment.

Before Section IX:

> The exposed high matching fixes the only large overlap cells.  What remains is
> an even residual edge set, and restriction outside the matching is injective.

Before amplification:

> The normalized second moment produces a seed with positive probability.  The
> final step converts that seed into a high-probability cocolouring without
> changing the leading root separation.

## Claim-status discipline

The manuscript should use exactly three status labels.

- **proved in the manuscript:** ordinary mathematical argument complete;
- **exactly certified:** finite identity or sign reconstructed by a deterministic
  verifier;
- **formally checked:** specific Lean theorem with stated dependency and axiom
  scope.

Do not use `verified` without specifying which of these meanings is intended.

Until closure, the front matter must say `candidate proof` or `conditional
Version 2 theorem`.  After closure, remove the status language from the theorem
statement itself but retain a concise reproducibility paragraph.

## Material to move out of the main narrative

- the superseded near/middle split;
- the old `E_mid`, `Xi_4`, and residual-mass dichotomy;
- simple-cycle and mixed-cycle encodings used only by the old Section IX route;
- long Lean theorem-name inventories;
- CI implementation details;
- alternative support scans and near-root research programmes;
- full endpoint table and LDL-style finite ledgers.

These remain useful audit artifacts and should be indexed in an appendix or
repository map.

## Editorial acceptance test

After reading the abstract and introduction, a probabilistic combinatorialist
should be able to answer:

1. why cocolourings gain a factor \(2^k\);
2. where the \(n/(\log n)^3\) scale comes from;
3. why the proof needs a second moment;
4. what the exact signed-overlap identity separates;
5. why high support is a matching;
6. why there is one global \((n)_J\) denominator;
7. why deleting the exposed matching controls the residual even family;
8. why amplification is needed after Paley--Zygmund.

If the reader must first parse the old cycle-walk machinery or the full Lean DAG,
the main exposition is still not reader-first.
