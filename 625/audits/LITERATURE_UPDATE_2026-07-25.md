# Erdős 625 literature update

**Search date:** 25 July 2026  
**Scope:** cochromatic number of `G(n,1/2)`, generalized hereditary
partition parameters, and the alternative two-independent-graph coupling
suggested in the Erdős Problems discussion

## 1. Current public status

The Erdős Problems database continues to mark Problem 625 as open. Its current
summary records:

- the nonconcentration-based lower obstruction of Heckel and, independently,
  Steiner;
- Heckel's conjectured scale `n/(log n)^3`;
- Heckel's positive result for roughly 95 percent of integer values of `n`.

The targeted search did not find an indexed paper, through the search date,
claiming a full-sequence high-probability lower bound of order
`n/(log n)^3`. This is a search result, not a claim about unpublished work or
material absent from the searched indexes.

Primary/current sources:

- Thomas Bloom, *Erdős Problem #625*,
  <https://www.erdosproblems.com/625>.
- Annika Heckel, *On a question of Erdős and Gimbel on the cochromatic
  number*, Electron. J. Combin. 31 (2024), P4.72;
  <https://arxiv.org/abs/2408.13839>.
- Annika Heckel, *The difference between the chromatic and the cochromatic
  number of a random graph*, <https://arxiv.org/abs/2409.17614>.
- Raphael Steiner, *On the Difference Between the Chromatic and Cochromatic
  Number*, SIAM J. Discrete Math. 39 (2025), 2268--2274,
  DOI 10.1137/24M1715180.

## 2. Publication-status correction

Steiner's 2024 preprint is now a journal article. SIAM records acceptance on
22 September 2025 and online publication on 17 November 2025. The abstract
states that it gives positive evidence for the Erdős--Gimbel prize question;
it does not claim the full random-graph resolution pursued here.

The bibliography and introduction should therefore cite the journal version,
not only the arXiv preprint.

## 3. Foundational cochromatic literature absent from the present background

The present introduction begins with the 1993 problem paper, but the invariant
and the surrounding comparison questions predate it. A more complete historical
paragraph should include at least:

1. L. Lesniak and H. J. Straight, *The cochromatic number of a graph*, Ars
   Combin. 3 (1977), 39--46. This is the standard origin reference for the
   parameter.
2. P. Erdős, J. Gimbel, and H. J. Straight, *Chromatic number versus
   cochromatic number in graphs with bounded clique number*, European J.
   Combin. 11 (1990), 235--240, DOI 10.1016/S0195-6698(13)80123-0.
3. P. Erdős, J. Gimbel, and D. Kratsch, *Some extremal results in
   cochromatic and dichromatic theory*, J. Graph Theory 15 (1991), 579--585,
   DOI 10.1002/jgt.3190150604.
4. P. Erdős and J. Gimbel, *Some problems and results in cochromatic theory*,
   Ann. Discrete Math. 55 (1993), 261--264, which contains the problem used in
   the manuscript.

Steiner's 2025 paper gives a compact modern map of these three early papers and
of which associated conjectures and questions have since been settled.

## 4. Generalized-chromatic random-graph framework missing from the draft

Edward R. Scheinerman's

> *Generalized Chromatic Numbers of Random Graphs*, SIAM J. Discrete Math. 5
> (1992), 74--80, DOI 10.1137/0405006

studies `P`-chromatic numbers for hereditary graph classes. For an infinite
hereditary class `P` and fixed `0<p<1`, it proves the first-order scale
`Theta(n/log n)`.

Béla Bollobás and Andrew Thomason subsequently proved the sharper general
result

> *Generalized chromatic numbers of random graphs*, Random Structures &
> Algorithms 6 (1995), 353--356, DOI 10.1002/rsa.3240060222.

Their theorem associates an explicit coloring-number parameter `r(P)` with a
nontrivial hereditary property and gives the corresponding exact first-order
constant for its generalized chromatic number in a dense random graph.

The cochromatic number is the `P`-chromatic number for the hereditary class
consisting of complete and empty graphs. These two papers therefore provide the
proper first-order framework for the present fine comparison. They do not
address the phase-sensitive difference `chi-zeta`, but they explain why both
parameters have the same `n/log n` order before the manuscript resolves their
third-order separation.

Before inserting the Bollobás--Thomason formula into the paper, the manuscript
should state explicitly how their coloring-number parameter specializes to the
complete-or-empty hereditary class, rather than leaving the reader to infer it.

Sources:

- <https://epubs.siam.org/doi/10.1137/0405006>;
- <https://doi.org/10.1002/rsa.3240060222>.

## 5. Adjacent cocoloring literature

John Gimbel, André Kündgen, and Michael Molloy's

> *Fractional Cocoloring of Graphs*, Graphs Combin. 38 (2022), article 64,
> DOI 10.1007/s00373-022-02463-5

introduces and studies the fractional cochromatic number. Among other results,
it compares fractional chromatic and cochromatic numbers under clique
restrictions and determines the maximal order of the fractional parameter up
to constants.

This does not enter the random-graph second moment, but it is relevant if the
paper includes a broader related-work paragraph or if a later paper studies a
fractional or linear-programming relaxation of the signed witness.

## 6. Informal two-independent-graph reduction

The discussion thread for Problem 625 contains an informal reduction reported
by Zach Hunter and observed with Micha Christoph, Annika Heckel, and Raphael
Steiner. Sample independent graphs

```text
G1, G2 ~ G(n,1/2),
```

and let `X` be the minimum number of parts in a partition in which every part
is independent in at least one of `G1` or `G2`. The comment states that a
McDiarmid-coupling argument couples this variable so that

```text
X >= zeta(G)
```

for a single `G ~ G(n,1/2)`.

Source:
<https://www.erdosproblems.com/forum/thread/625>.

This is a discussion comment, not a published theorem with a citable proof in
the searched literature. It should not be used as an input to the present
paper without obtaining or supplying the full coupling argument.

### Why it may be useful later

The two-layer model removes explicit clique declarations: a class is assigned
to layer 1 or layer 2 and must be independent in that layer. Its first moment
retains the same `2^k` assignment gain that drives the signed four-size
profile. It may therefore provide:

1. an alternative conceptual interpretation of the signed witness;
2. a cleaner coupling-based route to comparison with `zeta(G)`;
3. a separate model in which concentration of `X` and comparison with
   `chi(G)` can be studied directly.

Recent random-graph papers use McDiarmid's coupling in other transversal or
multilayer settings; for example Micha Christoph, Anders Martinsson, and
Aleksa Milojević, *Universality for transversal Hamilton cycles in random
graphs*, <https://arxiv.org/abs/2505.05385>. This confirms that the technique is
active, but it does not establish the cochromatic reduction.

For the current manuscript, this direction is a follow-up project rather than
a replacement for the nearly completed Section VIII--IX proof.

## 7. Restriction-product theorem and novelty caution

The cumulative proof stack extracts the finite statement

```text
if deletion of I is injective on a finite set family C, then
sum_{A in C} product_{e in A \ I} q_e
  <= product_{e notin I} (1+q_e).
```

For a graph cycle space, deletion of a forest is injective; for a binary
matroid cycle space, deletion of an independent set is injective. These are
immediate coding/cycle-space consequences of the generic finite theorem.

The targeted search did not identify a paper presenting this exact weighted
subset-product inequality under the same name. That absence is not evidence
of novelty: the statement is elementary and is likely implicit in standard
cycle-space, coding-theory, or matroid arguments. The present Erdős 625 paper
should use it as a proof lemma without a novelty claim. A separate follow-up
would require a dedicated literature review and applications beyond this one
second-moment problem.

## 8. Recommended manuscript changes after proof closure

1. Update Steiner's reference to the 2025 SIAM journal publication.
2. Add Lesniak--Straight (1977), Erdős--Gimbel--Straight (1990), and
   Erdős--Gimbel--Kratsch (1991) to the historical paragraph.
3. Add Scheinerman (1992) and Bollobás--Thomason (1995) to the first-order
   random-graph background; the latter is the sharper general antecedent.
4. Keep the Erdős Problems page as a current-status pointer, not as the primary
   source for the original problem.
5. Mention fractional cocoloring only as adjacent work unless the manuscript
   develops a concrete fractional corollary.
6. Mention the two-independent-graph model only in a concluding-remarks or
   future-work paragraph, clearly labelled as an informal external suggestion,
   unless a complete proof and attribution are obtained.
7. Make no novelty claim for the generic restriction-product lemma without a
   separate coding/matroid literature audit.
