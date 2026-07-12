# Certified exact experiments for \(\chi\) and \(\zeta\)

## Material Passport

- Origin Skill: experiment-agent
- Origin Mode: validate
- Origin Date: 2026-07-11
- Verification Status: VERIFIED
- Version Label: validation_v1
- Source: `exact_chi_zeta.py` / deterministic local computation
- Overall Confidence: SOLID for the finite instances listed; no asymptotic inference is licensed

## Scope and result

The accompanying standard-library program computes exact chromatic and
cochromatic numbers for labelled graphs of moderate order.  It also emits one
certified optimal partition profile for each invariant.  The retained data file
contains 27 deterministic \(G(n,1/2)\) instances: three seeds at each even
\(n\) from 12 through 28.  Every row finished with `status=exact`, and every row
passed an independent solve of its complement.

These are finite diagnostics.  In particular, the observed gaps do **not**
constitute evidence that \(\chi(G_n)-\zeta(G_n)\) converges, diverges, or has a
particular asymptotic scale.

## Artifacts

| Artifact | Purpose | SHA-256 at validation |
|---|---|---|
| `exact_chi_zeta.py` | deterministic generator, exact solver, certificate checks, self-tests | `DF90D14FE86A8FF3B1B8E2165EB7FB554811CD58D86D9F2CC3C6C7573AA1E0C0` |
| `EXACT_EXPERIMENTS.csv` | 27 exact sampled instances and profiles | `C88DF0883911A6E4BA9BB590B1F2C610A461F12606081B4B4AD55B0CEAC49F35` |

The Python environment used for the retained run was Python 3.14.3 on Windows.
No commercial solver, third-party Python package, or network service was used.

## Exact method and certificate argument

Represent each vertex set by an integer bitmask.

1. Bron--Kerbosch with pivoting enumerates all maximal cliques of \(G\).
   Running the same algorithm on \(\overline G\) enumerates all maximal
   independent sets of \(G\).
2. For \(\chi(G)\), the cover columns are the maximal independent sets.  For
   \(\zeta(G)\), they are the union of the maximal independent sets and maximal
   cliques.
3. Restricting to maximal sets is lossless: every independent set (respectively
   clique) extends to a maximal one.  A homogeneous partition therefore gives
   a cover of the same cardinality.  Conversely, assign every vertex in a cover
   to one selected column containing it.  A minimum-cardinality cover has a
   private vertex in every column, so this produces the same number of nonempty,
   disjoint homogeneous classes.  Thus the relevant minimum set-cover value is
   exactly \(\chi\) or \(\zeta\), not a relaxation.
4. The exact cover search uses iterative deepening.  At a state with uncovered
   set \(U\), it chooses a vertex \(v\in U\) and exhausts every undominated
   column containing \(v\).  If
   \(A\cap U\subseteq B\cap U\), candidate \(A\) is safely omitted because
   replacing it by \(B\) covers at least the same residual vertices.  Failed
   states are memoized only in the logically safe direction.
5. The search begins at certified lower bounds: the volume bound
   \(\lceil |U|/\max_C|C\cap U|\rceil\), a greedily constructed
   pairwise-incompatible packing, and, for ordinary colouring at the root, the
   exact clique number \(\omega(G)\).  A deterministic greedy cover supplies an
   upper bound.  Exhausting every intervening depth certifies optimality.
6. The selected minimum cover is disjointified, then checked directly against
   the graph.  The program verifies that its classes are nonempty, disjoint,
   cover every vertex, have the declared clique/independent type, and number
   exactly the claimed optimum.

`chi_profile` and `zeta_profile` are JSON arrays of `[type,size]`, with `I`
meaning independent and `C` meaning clique.  They record one optimal
certificate profile; an instance can have other optimal profiles.

## Validation

### Exhaustive independent oracle

The command

```powershell
python research\experiments\exact_chi_zeta.py --self-test --exhaustive-n 6
```

checked all 33,867 labelled graphs with \(1\le n\le6\), plus the order-zero
boundary case.  For every graph it:

- compared both optima with an independent brute-force dynamic program over
  **all** nonempty independent/homogeneous subsets;
- compared the Bron--Kerbosch output with brute-force maximal-set enumeration;
- verified every returned partition certificate;
- solved the complement and checked
  \(\zeta(G)=\zeta(\overline G)\),
  \(\alpha(G)=\omega(\overline G)\), and
  \(\omega(G)=\alpha(\overline G)\).

Output: `SELF-TEST PASS`; elapsed time 31.297 s.

As an additional non-exhaustive adversarial check, 100 deterministic random
graphs at each of \(n=7,8,9\) (300 graphs total) were compared with the same
all-subsets oracle.  Both \(\chi\) and \(\zeta\) matched in every case
(`RANDOM_ORACLE_PASS 300`).  These graphs are validation fixtures and are not
included in the scientific CSV.

### Sample complement audit

The retained sample was generated with

```powershell
python research\experiments\exact_chi_zeta.py --sample `
  --n 12,14,16,18,20,22,24,26,28 --seeds 0,1,2 `
  --check-complement --timeout 120 `
  --output research\experiments\EXACT_EXPERIMENTS.csv
```

The `--check-complement` option independently enumerates and solves the
complement within the same per-instance limit.  All 27 rows report
`complement_checked=True`.  The sum of recorded first-run instance times was
2.178 s; the maximum was 0.344 s.  Timing is machine-dependent and is not part
of the mathematical result.

### Deterministic re-run

The complete sample command was re-run to a temporary CSV.  All 29 non-timing
fields in every one of the 27 rows matched exactly, including graph hashes,
invariants, profiles, enumeration counts, branch counts, bounds, and complement
status.  Timing fields were deliberately excluded, following the reproducibility
protocol.  Verdict: **REPRODUCIBLE**.

## Retained data summary

Here \(a=\lfloor\alpha_0(n)\rfloor\), the CSV column `alpha` is the **actual**
independence number of the sampled graph, and

\[
\mu_a=\binom{n}{a}2^{-\binom{a}{2}},\qquad
x(n)=\frac{\log\mu_a}{\log n}.
\]

The phase and \(x(n)\) depend only on \(n\).  Bracketed entries below correspond
to seeds 0, 1, and 2, in that order.

| \(n\) | phase \(\{\alpha_0\}\) | \(x(n)\) | actual \(\alpha\) | \(\omega\) | \(\chi\) | \(\zeta\) | gap |
|---:|---:|---:|---|---|---|---|---|
| 12 | 0.3714 | -0.1034 | [4,4,4] | [4,4,4] | [4,4,4] | [4,4,4] | [0,0,0] |
| 14 | 0.6425 | 0.2540 | [4,4,4] | [5,5,4] | [5,5,5] | [4,4,4] | [1,1,1] |
| 16 | 0.8854 | 0.5232 | [5,4,5] | [4,6,5] | [5,6,5] | [5,4,5] | [0,2,0] |
| 18 | 0.1052 | -0.1966 | [5,4,5] | [5,5,5] | [5,6,5] | [5,4,5] | [0,2,0] |
| 20 | 0.3059 | 0.0561 | [5,6,5] | [6,6,5] | [6,6,6] | [5,5,5] | [1,1,1] |
| 22 | 0.4905 | 0.2662 | [5,5,5] | [6,5,5] | [6,6,6] | [5,5,6] | [1,1,0] |
| 24 | 0.6615 | 0.4446 | [6,7,6] | [7,5,5] | [7,5,6] | [6,5,6] | [1,0,0] |
| 26 | 0.8207 | 0.5984 | [6,7,6] | [6,6,6] | [7,6,6] | [6,6,6] | [1,0,0] |
| 28 | 0.9696 | 0.7329 | [6,6,6] | [6,5,6] | [7,6,7] | [6,6,6] | [1,0,1] |

Across these 27 deliberately small samples, the gap was 0 in 13 rows, 1 in 12
rows, and 2 in 2 rows.  The two gap-2 rows illustrate why profiles are useful:

- \(n=16\), seed 1: colouring sizes \([4,3,3,2,2,2]\), versus a four-clique
  cocolouring with sizes \([5,4,4,3]\);
- \(n=18\), seed 1: colouring sizes \([3,3,3,3,3,3]\), versus a four-clique
  cocolouring with sizes \([5,5,4,4]\).

At such small orders, this behaviour is strongly affected by ordinary
graph/complement fluctuations and must not be extrapolated.

## CSV schema notes

- `alpha0`, `alpha0_floor`, and `alpha0_phase` use
  \(\alpha_0=2\log_2n-2\log_2\log_2n+2\log_2(e/2)+1\).
- `log2_mu_alpha0_floor` stores \(\log_2\mu_a\), avoiding overflow/underflow.
- `log_mu_alpha_over_log_n` stores \(\log\mu_a/\log n\); its value is independent
  of the logarithm base.
- `alpha` and `omega` are exact graph invariants, not asymptotic proxies.
- `graph_sha256` hashes \(n\) and the packed upper-triangular adjacency bits.
- `generator=splitmix64-v1/high-bit/p=1/2` fully specifies the graph stream:
  one SplitMix64 output per lexicographically ordered vertex pair, with an edge
  iff its high bit is 1.
- A row is usable as a certified datum only when `status=exact`.  A deadline is
  reported as `status=timeout`; the program never labels a bound as an optimum.
- The 120-second limit is per graph and includes the optional complement audit.

## Interpretation boundary

The experiment validates the implementation and supplies exact finite examples
across several fractional-\(\alpha_0\) phases.  It can help falsify finite
profile conjectures or select analytic cases for study.  It cannot resolve the
all-\(n\), high-probability quantifiers in Erdos Problem 625, estimate a limiting
probability from three seeds, or validate a proposed \(n/\log^3 n\) scale.
