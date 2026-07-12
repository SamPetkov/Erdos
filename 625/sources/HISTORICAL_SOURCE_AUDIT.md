# Historical and problem-record source audit

Audit date: 2026-07-11.

This file distinguishes bibliographic verification from reading an original
full text. `Verified metadata` is not treated as `verified original`.

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

- Bibliographic identity verified: P. Erdős and J. Gimbel, “Some Problems and
  Results in Cochromatic Theory,” *Annals of Discrete Mathematics* 55 (1993),
  261–264, DOI <https://doi.org/10.1016/S0167-5060(08)70393-5>.
- Publisher abstract and metadata were read directly at the ScienceDirect
  record. OpenAlex reports the work as closed access.
- The University of Alaska technical-report catalogue confirms a 1991 report
  with the same title, but exposes no report file.
- The available PagePlace PDF is only a 21-page front-matter preview and does
  not contain pages 261–264.
- Direct publisher PDF attempts returned HTTP 403/406. Therefore the original
  article has **not** yet been read; any claim attributed specifically to it
  remains blocked from `verified-original` status.

### Gimbel (2016)

- Bibliographic identity and abstract verified at Springer: John Gimbel,
  “Some of My Favorite Coloring Problems for Graphs and Digraphs,” in *Graph
  Theory: Favorite Conjectures and Open Problems 1* (2016), 95–108, DOI
  <https://doi.org/10.1007/978-3-319-31940-7_7>.
- The publisher page exposes subscription preview content only. The in-app
  institutional redirect was blocked before authentication and no PDF asset
  was available. OpenAlex reports closed access.
- Consequently the original chapter has **not** yet been read.

### Bollobás (1988)

- Bibliographic identity and DOI verified: B. Bollobás, “The Chromatic Number
  of Random Graphs,” *Combinatorica* 8(1) (1988), 49–55,
  <https://doi.org/10.1007/BF02122551>.
- The University of Memphis author repository record and publisher DOI both
  point to closed publisher content; OpenAlex reports closed access.
- The original full article has **not** yet been acquired. The asymptotic
  theorem is independently stated in multiple later primary papers, but that
  does not satisfy the user's original-text requirement.

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

- Publisher metadata and the author-hosted table of contents were verified.
  The relevant dense-colouring section is §7.4.
- No original full book text has yet been acquired; exact theorem/page
  attribution to the book remains unverified.

## Retrieval limitation

The unresolved paywalled items are not silently replaced by secondary
summaries. They remain explicit source-audit failures. A final claimed proof
may be mathematically self-contained, but it will not be described as having
met the user's mandatory-original-source condition unless these texts are
obtained and checked.
