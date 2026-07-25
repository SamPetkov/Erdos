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

## 3. Older generalized-chromatic framework missing from the current draft

Edward R. Scheinerman's

> *Generalized Chromatic Numbers of Random Graphs*, SIAM J. Discrete Math. 5
> (1992), 74--80, DOI 10.1137/0405006

studies `P`-chromatic numbers for hereditary graph classes. For an infinite
hereditary class `P` and fixed `0<p<1`, it proves the first-order scale
`Theta(n/log n)`.

The cochromatic number is the `P`-chromatic number for the hereditary class
consisting of complete and empty graphs. Scheinerman therefore supplies useful
historical first-order context, although it does not address the fine
chromatic--cochromatic difference or the `n/(log n)^3` scale. It should be
considered for the background paragraph and bibliography.

Source:
<https://epubs.siam.org/doi/10.1137/0405006>.

## 4. Informal two-independent-graph reduction

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

## 5. Restriction-product theorem and novelty caution

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

## 6. Recommended manuscript changes after proof closure

1. Update Steiner's reference to the 2025 SIAM journal publication.
2. Add Scheinerman's 1992 generalized-chromatic-number paper to the historical
   first-order discussion.
3. Keep the Erdős Problems page as a current-status pointer, not as the primary
   source for the original problem.
4. Mention the two-independent-graph model only in a concluding-remarks or
   future-work paragraph, clearly labelled as an informal external suggestion,
   unless a complete proof and attribution are obtained.
5. Make no novelty claim for the generic restriction-product lemma without a
   separate coding/matroid literature audit.
