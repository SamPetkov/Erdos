# Erdős 625: standard definitions and terminology audit

**Audit date:** 27 July 2026  
**Scope:** graph theory, random graphs, probabilistic combinatorics, configuration-model counting, and binary cycle spaces  
**Manuscript audited:** `625/arxiv/main.tex`  
**Parent proof branch:** PR #53  

## 1. Verdict

The manuscript uses the standard mathematical definitions of the chromatic
number, cochromatic number, \(G(n,1/2)\), bipartite matchings, even subgraphs,
and the binary cycle space. The proof does not rely on a nonstandard version
of the cochromatic number.

The required corrections are principally terminological and expositional:

1. state the standard definition using **independent sets and cliques**, while
   noting the equivalent induced-empty/induced-complete formulation;
2. call the signed object a **signed cocoloring witness**, not a new graph
   invariant;
3. define the falling-factorial convention explicitly, including the case
   \(r>x\);
4. distinguish the stub-level bipartite configuration model from the simple
   support graph derived from its cell counts;
5. define an even subgraph as an edge set of even degree at every vertex and
   identify \(eta(H)=|E|-|V|+c(H)\) explicitly as the dimension of the binary
   cycle space;
6. label `profile`, `demand`, `high cell`, `skeleton`, `endpoint table`, and
   `attachment` as manuscript-specific bookkeeping terms.

These changes do not alter any theorem. They prevent readers from mistaking
auxiliary proof objects for standard graph invariants and make the hypotheses
of the Section VIII product decomposition transparent.

## 2. Authoritative usage

The standard cochromatic definition was introduced by Lesniak and Straight:
the cochromatic number is the minimum number of parts in a partition of the
vertex set such that each part induces an empty or complete graph. Modern work
usually phrases the same definition as the minimum number of colors in a
vertex coloring for which every color class is an independent set or a clique.
The manuscript's notation \(\zeta(G)\) and its partition definition agree with
this usage.

Relevant references already present in `625/arxiv/references.bib` are:

- `lesniak-straight-1977`, the origin reference;
- `erdos-gimbel-straight-1990` and `erdos-gimbel-1993`, early cochromatic
  theory and the problem source;
- `heckel-2024-question`, `heckel-2025-difference`, and `steiner-2024`, which
  use the modern independent-set/clique formulation and the notation
  \(\zeta(G)\);
- `scheinerman-1992` and `bollobas-thomason-1995`, for generalized chromatic
  numbers associated with hereditary graph properties;
- `janson-luczak-rucinski-2000`, for standard random-graph notation and
  high-probability terminology.

The cochromatic number is also the generalized \(\mathcal P\)-chromatic number
for the hereditary class

\[
  \mathcal P_{\mathrm{co}}
  :=\{K_m,\overline{K_m}:m\ge 0\}.
\]

Thus

\[
  \zeta(G)=\chi_{\mathcal P_{\mathrm{co}}}(G).
\]

This observation is background only; the proof does not invoke a theorem about
generalized chromatic numbers.

## 3. Standard graph-theoretic definitions

### 3.1 Graphs, induced subgraphs, independent sets, and cliques

All graphs in the manuscript are finite, simple, and undirected. For
\(S\subseteq V(G)\), \(G[S]\) is the induced subgraph on \(S\).

- \(S\) is an **independent set** (also called a stable set) when \(G[S]\) is
  edgeless.
- \(S\) is a **clique** when \(G[S]\) is complete.

The manuscript should consistently use `independent set` and `clique` as the
primary terms. “Induces an empty graph” and “induces a complete graph” are
correct equivalent formulations.

### 3.2 Partitions and colorings

A vertex partition means a family of nonempty, pairwise disjoint subsets whose
union is \(V(G)\). Empty color classes are not counted. Ordered and labelled
partitions used later in the proof are auxiliary presentations of such
partitions.

The chromatic number is

\[
  \chi(G)=\min\{k:V(G)	ext{ is partitioned into }k	ext{ independent sets}\}.
\]

A **cocoloring** is a vertex partition in which each part is an independent set
or a clique. Its parts are cocolor classes. The cochromatic number is

\[
  \zeta(G)=\min\{k:G	ext{ has a cocoloring with }k	ext{ classes}\}.
\]

This is a partition parameter, not an overlapping cover parameter. The paper
should avoid `clique cover` or `cochromatic cover` unless overlap is explicitly
intended.

Two immediate standard consequences are

\[
  \zeta(G)=\zeta(\overline G),\qquad
  \zeta(G)\le \min\{\chi(G),\chi(\overline G)\}.
\]

They are not needed for the proof but provide useful consistency checks.

### 3.3 Random graph and high probability

\(G(n,p)\) denotes the simple labelled random graph on vertex set
\([n]=\{1,\ldots,n\}\) in which the \(inom n2\) edges are present independently
with probability \(p\). The manuscript fixes \(p=1/2\).

An event \(E_n\) holds **with high probability** (whp) when

\[
  \Pr(E_n)\longrightarrow 1
  \qquad(n	o\infty).
\]

The notations \(G(n,1/2)\) and \(G_{n,1/2}\) both occur in the literature. The
manuscript may retain \(G(n,1/2)\), but should use it consistently.

### 3.4 Falling factorial

The manuscript uses

\[
  (x)_r=x(x-1)\cdots(x-r+1),\qquad (x)_0=1.
\]

For nonnegative integers, the convention must be stated explicitly:

\[
  (x)_r=0\quad	ext{when }r>x.
\]

This is the convention implemented by Lean's `Nat.descFactorial`. It makes all
finite counting identities total, including infeasible demand tables, and
avoids hidden feasibility hypotheses.

## 4. Standard probabilistic-combinatorial objects

### 4.1 Profiles

A coloring profile is an auxiliary integer vector recording the number of
classes of each allowed size. This usage is common in random graph coloring,
but the exact indexing by deficits from \(\alpha\) is manuscript-specific.

The paper should distinguish:

- the abstract profile vector;
- an unordered partition having that profile;
- an ordered or labelled slot presentation used in the second moment.

Labelling slots multiplies the witness count by a deterministic factorial and
does not change the normalized second moment.

### 4.2 Overlap matrix

For ordered partitions \((V_a)_a\) and \((W_b)_b\), the overlap matrix is the
contingency table

\[
  r_{ab}=|V_a\cap W_b|.
\]

Its row sums and column sums are the two class-size lists. The law

\[
  p(r)=rac{\prod_a s_a!\prod_b t_b!}
             {n!\prod_{a,b}r_{ab}!}
\]

is the standard exact law of the overlap contingency table for two independent
uniform ordered partitions with those margins.

### 4.3 Bipartite configuration model

The bipartite configuration model used here is the following finite object:

1. row vertex \(a\) receives \(s_a\) labelled stubs;
2. column vertex \(b\) receives \(t_b\) labelled stubs;
3. the two stub sets have equal total cardinality;
4. choose a uniform perfect matching between the row and column stubs.

The cell count \(r_{ab}\) is the number of matched stub pairs joining row type
\(a\) to column type \(b\).

This is a stub-level matching model. It may induce multiple matched pairs
between the same row and column types. It should not be described as a simple
graph. The simple graph \(H(r)\) introduced later is a separate support graph
constructed from the cell counts.

### 4.4 Matchings and partial matchings

A matching is an edge set in which no two edges share an endpoint. A partial
matching need not cover all vertices or stubs; a perfect matching covers every
vertex or stub.

The Section VIII physical skeleton is a partial matching of row and column
stubs. Its positive **type support** is a matching of block types only after
the high-cell threshold and degree caps have been used. These are different
levels:

- physical matching: edges between individual stubs;
- block-support matching: selected pairs of row and column classes;
- configuration-model perfect matching: all ambient stubs are paired.

The manuscript and Lean formalization correctly separate these three notions.

## 5. Binary cycle-space terminology

### 5.1 Support graph

For an overlap table \(r\), \(H(r)\) is the simple bipartite graph whose row and
column vertices are the partition slots incident with a cell satisfying
\(r_{ab}\ge2\), and whose edges are those cells. Isolated slot vertices are
omitted.

Let \(c(H)\) be the number of connected components of this simple graph, with
\(c(arnothing)=0\). The omission of isolated vertices does not change the
quantity \(|E|-|V|+c\), but stating the convention removes ambiguity.

### 5.2 Even subgraphs

An even subgraph of \(H\) is an edge set \(F\subseteq E(H)\) such that every
vertex has even degree in the spanning subgraph \((V(H),F)\). It need not be
connected. In the formalization, an even subgraph is represented directly by
its edge set.

The even edge sets form the binary cycle space under symmetric difference.
Its dimension is

\[
  eta(H)=|E(H)|-|V(H)|+c(H),
\]

also called the cycle rank, circuit rank, cyclomatic number, or first Betti
number of \(H\). Therefore

\[
  |\mathcal C(H)|=2^{eta(H)}.
\]

The manuscript's equation (6.7) is exactly this standard identity.

The phrase “independent cycle choices” should be replaced by “elements of the
binary cycle space” or “binary cycle-space degrees of freedom”: an arbitrary
cycle-space element need not be a single simple cycle.

## 6. The signed witness is auxiliary, not a new invariant

The term `signed cocoloring` is not a standard graph invariant. The safest
term is **signed cocoloring witness**:

- start with a vertex partition;
- mark each class by `I` or `K`;
- an `I`-marked class must be independent;
- a `K`-marked class must be a clique.

For the four-size profile used in the proof, every class has size at least two
for sufficiently large \(n\). Hence a class cannot simultaneously be
independent and a clique, and forgetting the marks identifies realized signed
witnesses with ordinary cocolorings of that fixed partition.

The factor \(2^k\) is therefore a witness-counting factor, not the definition of
a new cochromatic parameter. The manuscript already states this idea, but the
word `witness` should be incorporated into the formal definition and retained
throughout Section 5.

## 7. Manuscript-specific terminology

The following terms are useful but are not standard graph invariants. Each
must be defined locally before use.

| Term | Exact role |
|---|---|
| deficit coordinate | class size expressed relative to the phase reference \(\alpha\) |
| four-size profile | profile supported on the four selected deficit coordinates |
| demand table | prescribed number of physical stub pairs in each type cell |
| positive demand support | type cells with positive demand |
| high cell | a cell whose multiplicity lies strictly above the selected half-cap |
| endpoint multiplicity | the full-containment reference multiplicity \(\min\{s,t\}\) |
| deficit \(h\) | endpoint multiplicity minus actual multiplicity |
| physical high skeleton | partial matching of actual stubs realizing the high demand table |
| block skeleton/support | matching of row-class and column-class types carrying positive high demand |
| endpoint table | the \(4	imes4\) table counting selected block pairs by endpoint types |
| local reward | the signed-overlap factor attached to one cell multiplicity |
| residual attachment | the remaining local and cycle-space factor after the high skeleton is fixed |

The use of `skeleton` is legitimate as bespoke terminology, but it must never
be conflated with the graph-theoretic \(k\)-core, a spanning forest, or the
configuration-model multigraph itself.

## 8. Definition-dependent proof checks

### 8.1 The \(2^k\) signed first-moment factor

The factor is valid because:

1. every chosen class has at least two vertices for all sufficiently large
   \(n\);
2. for \(G(n,1/2)\), an \(s\)-set is independent with probability
   \(2^{-inom s2}\), and is a clique with the same probability;
3. for \(s\ge2\), the two events are disjoint;
4. the edge constraints inside distinct classes concern disjoint edge sets.

Thus the marked witness probability for a fixed partition is exactly
\(2^k2^{-B}\), where \(B\) is the total number of prescribed internal edge
bits.

### 8.2 Threshold \(r_{ab}\ge2\) in the sign support graph

A cell containing zero or one common vertex contains no internal edge bit
prescribed by both partitions. It imposes no equality between the two class
marks. A cell containing at least two vertices contains at least one shared
internal edge and forces the row and column marks to agree. Hence the support
graph threshold \(r_{ab}\ge2\) is definitionally correct.

### 8.3 Cycle-space factor

Compatible marks are constant on each connected component of \(H(r)\), and the
local reward splits one factor from each support edge. The remaining exponent
is \(|E|-|V|+c\), the standard binary cycle-space dimension. Equation (6.4)
does not use a nonstandard notion of cycle.

### 8.4 Matching-supported local product

The product of independent one-cell partial matching fibres in PR #53 is valid
only when the positive type support is a matching. If two positive cells share
a row type or column type, their local stub selections compete for the same
ambient stubs and do not factor independently. The standard matching
hypothesis is therefore load-bearing, not cosmetic.

### 8.5 Maximum versus maximal

Whenever optimization language is used, `maximum` means largest cardinality
and `maximal` means inclusion-maximal. The manuscript's independence number
uses maximum independent sets. The proof should not substitute `maximal` in
this context.

## 9. Lean alignment

The formalization agrees with the standard definitions:

- `IsBipartiteMatching` states uniqueness of the column neighbor in each row
  and uniqueness of the row neighbor in each column;
- `IsBipartiteEven` states even degree at every row and column vertex;
- `UnlabelledTypedSkeleton` is a finite partial matching of typed row and column
  stubs;
- `UnlabelledTypedSkeleton.typeTable` counts physical edges by their two types;
- `positiveDemandSupport` is the finite support of nonzero demand cells;
- `Nat.descFactorial` implements the total falling-factorial convention;
- `cycleRank` and the even-edge-set cardinality theorem implement the binary
  cycle-space identity.

The names `UnlabelledTypedSkeleton`, `canonicalDemand`, and `attachment` are
project-specific definitions. Their correctness must be judged by their
explicit fields and theorems, not by importing an external meaning for those
words.

## 10. Recommended Version 2 wording

The companion file

```text
625/arxiv/STANDARD_DEFINITIONS_INSERT_V2.tex
```

contains copy-ready text for the introduction, notation section, signed-witness
definition, configuration-model convention, and cycle-space convention.

The minimum required manuscript edits are:

1. cite `lesniak-straight-1977` at the first cochromatic definition;
2. use `independent set or clique` as the primary wording;
3. define a signed cocoloring **witness**;
4. add the total falling-factorial convention;
5. distinguish the stub perfect matching from the simple support graph;
6. define \(c(H)\), even subgraphs, and \(eta(H)\) explicitly;
7. add one sentence declaring the Section VIII vocabulary manuscript-specific.

## 11. Acceptance checklist

Before the final TeX is submitted, verify all of the following.

- [ ] `partition` is explicitly nonempty and disjoint;
- [ ] `cocoloring` is defined by independent-set/clique classes;
- [ ] \(\zeta(G)\) is identified as the cochromatic number introduced by
      Lesniak--Straight;
- [ ] `signed cocoloring witness` is not presented as a new invariant;
- [ ] the class-size-\(\ge2\) condition is stated where the \(2^k\) factor is used;
- [ ] \((x)_r\) includes \((x)_0=1\) and the \(r>x\) zero convention;
- [ ] the configuration model is a uniform perfect matching of two stub sets;
- [ ] the support graph \(H(r)\) is explicitly simple;
- [ ] \(c(H)\) and the empty-graph convention are explicit;
- [ ] an even subgraph is defined by even degrees, not by connectedness;
- [ ] \(eta(H)\) is identified with the binary cycle-space dimension;
- [ ] `matching` is used only when no two selected cells share a row or column;
- [ ] all bespoke Section VIII terms are locally defined;
- [ ] no use of `cover` silently replaces the required vertex partition;
- [ ] the mathematical definitions in the TeX and Lean statements agree.

## 12. Final assessment

No proof step was found to depend on a nonstandard definition of chromatic or
cochromatic number. The main risk was terminological: the manuscript moves
between ordinary cocolorings, explicitly marked signed witnesses, a stub-level
configuration matching, a simple support graph, and several bespoke skeleton
objects. Once these levels are named separately, the proof's combinatorial
contracts are substantially easier to audit.
