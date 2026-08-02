# Erdős 625: AMS writing and clarity pass

**Date:** 2 August 2026  
**Branch:** `agent/625-ams-manuscript-clarity`  
**Scope:** actual copy-ready TeX prose for the eventual Version 2 manuscript

## 1. Purpose

This pass revises the manuscript text itself.  It is not another proof audit or
pull-request description.  The branch supplies a compilable editorial draft
containing a replacement abstract and introduction, a proof-architecture
section, and shorter reader-facing versions of the high-skeleton and residual
attachment sections.

The canonical `625/arxiv/main.tex` remains unchanged.  The new fragments are
post-closure text and must not be imported until the normalized second-moment
estimate and final theorem have been validated on one integrated branch.

## 2. AMS-style decisions

The editorial draft follows the ordinary `amsart` hierarchy:

```text
Theorem / Proposition / Lemma / Corollary
Definition
Remark
```

The final manuscript should use standard theorem environments rather than
colored ruled boxes.  Mathematical statements are stated first and proved
second.  Definitions precede their first substantive use.  Exact identities,
deterministic inequalities, asymptotic estimates, and probabilistic
conclusions are kept in separate paragraphs or propositions.

The prose uses American mathematical English consistently:

```text
coloring, cocoloring, normalized, fiber
```

The draft also uses `\log` consistently for the natural logarithm, with the
convention stated once in the full manuscript.

## 3. Abstract and introduction

The revised abstract is a single paragraph of fewer than 150 words.  It states:

1. the invariant and probabilistic model;
2. the quantitative conclusion;
3. the phase-uniform difficulty;
4. the four mathematical mechanisms used in the proof.

It removes promotional language such as “exquisitely phase-sensitive” and
replaces it by the quantitative statement that the first-moment root moves by
order `n/(log n)^3`.

The introduction now has a fixed order:

1. standard graph-theoretic definitions;
2. the Erdős--Gimbel question;
3. the main theorem;
4. the significance of the full-sequence quantifier;
5. concise historical background;
6. the three main proof ideas;
7. organization of the paper.

The introduction does not begin the technical proof, and it does not repeat the
same roadmap twice under different headings.

## 4. Proof architecture

The rewritten proof architecture separates the argument into:

1. ordinary and signed first-moment roots;
2. exact signed-overlap identity;
3. high cells as a block matching with deficits;
4. exact physical-fiber summation and one global denominator loss;
5. all-deficit summation and weighted regrouping by endpoint table;
6. q-only residual attachment;
7. amplification and final event intersection.

The section introduces every symbol before using it.  In particular, it
explains the roles of

```text
P, s_e, t_e, m_e, d_e, j_e, h_e, J, H, L(P), W(L), and q_e.
```

The text states explicitly that no individual partial matching is assigned a
canonical full completion.  The complete physical fiber is summed first.

## 5. Section VIII rewrite

The new Section VIII text is organized around five named finite statements:

1. aggregate high-skeleton weight;
2. exact local ratio;
3. aggregate deficit comparison;
4. finite optional-choice identity;
5. weighted reference regrouping.

The principal formula is

```text
w(P,j)
  = product_e (s_e)_{j_e}(t_e)_{j_e}
    / ((n)_J product_e j_e!)
    * product_e g(j_e).
```

The prose distinguishes the local ratio from the global denominator change.
It explicitly states that the factor `n^H` is paid once, after the physical
fibers have been summed.

The old near/middle split, objectwise completion language, and residual-cycle
bookkeeping do not appear in this replacement.

## 6. Section IX rewrite

The new residual section begins with the exact conditional decomposition and
then states a general restriction-product lemma.  The proof of the lemma is one
paragraph: injectivity embeds the restricted family into a power set, whose
weighted sum is a product.

For the even-subgraph application, the text gives the precise reason for
injectivity: an even subset of a matching must be empty.  It then explains that
one activity `q_e` controls both the local increment product and the
cycle-space product.

The section contains no simple-cycle decomposition, walk kernel, mixed-cycle
encoding, or duplicated local/cycle charge.

## 7. Displayed mathematics

The editorial fragments use automatically numbered `equation` environments
and labels.  They do not use manual `\tag{...}` commands.  Displayed equations
are integrated grammatically into the surrounding sentences and carry
punctuation where the sentence continues.

Long formulas are preceded by a sentence explaining their role.  A displayed
formula is not followed by “where” unless the newly introduced notation is
short and local.

## 8. Citation and attribution style

Historical claims are attached to primary references.  Citations are placed at
the ends of the sentences they support.  The proof architecture does not cite
software, audits, or pull requests.  Formalization and reproducibility material
belong in a separate final section and must not interrupt the mathematical
argument.

## 9. Files

```text
625/arxiv/AMS_THEOREM_ENVIRONMENTS_V2.tex
625/arxiv/FRONTMATTER_INTRODUCTION_POSTCLOSURE_V2.tex
625/arxiv/PROOF_ROADMAP_INSERT_V2.tex
625/arxiv/SECTION8_ALL_DEFICIT_AMS_V2.tex
625/arxiv/SECTION9_Q_ONLY_AMS_V2.tex
625/arxiv/AMS_EDITORIAL_DRAFT_V2.tex
625/experiments/check_ams_manuscript_clarity.py
```

## 10. Promotion boundary

The editorial draft is intentionally separate from `main.tex`.  It may be
promoted only after the following mathematical results are green on one
integrated branch:

1. the complete Section VIII bare-skeleton estimate;
2. the attained q-only attachment estimate;
3. the normalized signed second moment;
4. the seed amplification at the required deterministic scale;
5. the final full-sequence event assembly.

At promotion time, the bibliography, theorem numbering, cross-references,
notation, and coefficient statement must be synchronized in one commit.
