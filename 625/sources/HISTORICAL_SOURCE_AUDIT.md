# Historical and problem-record source audit

Audit date: 2026-07-12.

This file distinguishes bibliographic verification from reading an original
full text. `Verified metadata` is not treated as `verified-original`. The four
originals supplied by the user on 2026-07-12 were inspected directly; their
checksums are recorded below. The copyrighted PDFs remain local and are not
redistributed in this repository or its release ZIP.

## Problem record and discussion

### Erdős Problems #625

- Original web record read directly: <https://www.erdosproblems.com/625>.
- LaTeX/bibliography view read directly:
  <https://www.erdosproblems.com/latex/625>.
- Full three-comment forum thread read directly:
  <https://www.erdosproblems.com/forum/thread/625>.
- Status displayed on 2026-07-11: open. The site expressly warns that this is
  the site owner's current belief, not a literature-proof of openness.
- The forum's two-graph coupling and expectation/concentration assertions are
  comments dated 2025-09-15 and are not peer-reviewed theorem statements.

### CDC prompt architecture

- Original two-page PDF acquired as `research/downloads/cdc_prompt.pdf` and
  extracted to `research/sources/text/cdc_prompt.txt`.
- It is a workflow reference, not mathematical evidence about Problem #625.

## Historical mathematical sources

### Erdős and Gimbel (1993)

- Bibliographic identity: P. Erdős and J. Gimbel, “Some Problems and Results
  in Cochromatic Theory,” *Annals of Discrete Mathematics* 55 (1993),
  261–264, DOI <https://doi.org/10.1016/S0167-5060(08)70393-5>.
- User-supplied original PDF checked in full (4 pages), local filename
  `10.1016@S0167-50600870393-5.pdf`, SHA-256
  `C89CC993A5A2BD0068E9C81FD4EB07B88FA1D48DD8CA80F676753D8CB24B1683`.
- The abstract defines the cochromatic number as the minimum number of parts
  partitioning the vertex set so that each part induces an empty or a complete
  graph.
- On printed page 263 the paper takes the random graph on `n` labelled
  vertices with edge probability `1/2`. From the clique and independence
  bounds it obtains `n/(2 log_2 n) <= z(G_n)` almost surely, while
  `z(G_n) <= chi(G_n)` and Bollobás's chromatic upper bound give
  `chi(G_n) <= (1+o(1))n/(2 log_2 n)` almost surely.
- It then states explicitly that it was not known whether
  `chi(G_n)-z(G_n)` tends to infinity “a.s.” This confirms the historical
  origin and the source's asymptotic-probability wording for Problem #625.

### Gimbel (2016)

- Bibliographic identity: John Gimbel, “Some of My Favorite Coloring Problems
  for Graphs and Digraphs,” in *Graph Theory: Favorite Conjectures and Open
  Problems 1* (2016), 95–108, DOI
  <https://doi.org/10.1007/978-3-319-31940-7_7>.
- User-supplied original PDF checked in full (14 pages), local filename
  `gimbel2016.pdf`, SHA-256
  `16A38578CFF14B653813FA5D399448F949CB24F5DD716200E43356DF6F1F0D75`.
- Section 7.4, printed page 100, defines `R_n` on `n` labelled vertices with
  each edge present with probability `1/2`, states
  `chi(R_n)/z(R_n) -> 1` almost surely, and presents Problem 2 as asking
  whether `chi(R_n)-z(R_n) -> infinity` almost surely.
- The same page records Erdős's offer of $100 for a positive answer and $1000
  for a negative answer, together with his later view that $1000 was too high.
- The chapter therefore confirms that the problem remained open in this 2016
  survey and fixes the exact random-graph model, limiting mode, and prize note.

### Bollobás (1988)

- Bibliographic identity: B. Bollobás, “The Chromatic Number of Random
  Graphs,” *Combinatorica* 8(1) (1988), 49–55,
  <https://doi.org/10.1007/BF02122551>.
- User-supplied original PDF checked in full (7 pages), local filename
  `10.1007@BF02122551.pdf`, SHA-256
  `DAD7548A214E73A991C152EC0C1F56A67070B463642B54BC1B0529ECF507F5DE`.
- Theorem 4 on printed page 52 assumes fixed `0<p<1`, sets `q=1-p`,
  `d=1/q`, and
  `s_0=floor(2 log_d n-2 log_d log_d n+2 log_d(e/2)+1)`. It proves that
  almost every `G(n,p)` satisfies
  `n/s_0 <= chi(G(n,p)) <= (n/s_0)(1+3 log log n/log n)`, hence
  `chi(G(n,p))=(1+o(1))n/(2 log_d n)`.
- At `p=1/2` this is the chromatic asymptotic used in the 1993 historical
  argument. The self-contained candidate proof does not import Bollobás's
  proof as a logical dependency.

### Bollobás and Erdős (1976)

- Original nine-page author-archive scan acquired from the Rényi Institute:
  <https://www.renyi.hu/~p_erdos/1976-05.pdf>.
- Local file: `research/downloads/bollobas_erdos_cliques_1976.pdf`.
- Text extraction and rendered-page inspection completed. The paper works on
  a common infinite-graph coupling and records the first-order clique scale,
  followed by sharper distributional estimates.

### Frieze (1990)

- Original scan acquired from Alan Frieze's CMU publication page:
  <https://www.math.cmu.edu/~af1p/Texfiles/indgnp.pdf>.
- Local file: `research/downloads/frieze_independence_1990.pdf`.
- The scan has no usable text layer, so pages were rendered and inspected
  visually. Its displayed theorem assumes `d=np`, fixed `epsilon>0`, and
  `d_epsilon <= d=o(n)`; it is not itself the constant-`p=1/2` theorem.

### Janson, Łuczak, and Ruciński (2000)

- Bibliographic identity: S. Janson, T. Łuczak, and A. Ruciński,
  *Random Graphs*, Wiley, 2000.
- User-supplied original scan acquired, local filename
  `ee3faf8268b1aa80fabc349b39f63363.pdf`, 335 pages, SHA-256
  `DCE5CFC3A6D387DE5F81461C9270B9EF8179759D74E5E617919673AC6E409EC7`.
- The relevant portion was checked directly. Because the scan has no usable
  text layer, the table of contents and printed pages 190–192 were rendered
  and inspected visually. Section 7.4 is “The chromatic number of dense
  random graphs.”
- Theorem 7.14 gives, for fixed `0<p<1` and `b=1/(1-p)`, bounds holding
  a.a.s. (with probability tending to one):
  `n/(2 log_b n-log_b log_b n) <= chi(G(n,p)) <=
  n/(2 log_b n-8 log_b log_b n)`.
- Remark 7.15 records the sharper estimate
  `chi(G(n,p))=n/(2 log_b n-2 log_b log_b n+O_C(1))` for constant `p`, and
  its stated extension to slowly vanishing `p` with a larger error term.
- This book corroborates the dense-colouring background and Bollobás
  attribution; it is not a logical dependency of the self-contained proof.

## Source-impact conclusion

The four previously unavailable originals are now `verified-original` for
the claims attributed to them in this dossier. They clear the earlier
source-access condition and confirm the
historical problem statement, its a.a.s./with-high-probability formulation,
and the ordinary chromatic-number asymptotic. They require no correction to
the candidate theorem, its explicit constant, or any proof step. This is a
source and provenance audit; it is not external peer review, publication, priority
verification, or community acceptance of the proposed solution.
