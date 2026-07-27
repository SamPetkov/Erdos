# Exact physical-fibre ratio at fixed high support

## Status and purpose

This note proves the finite counting identity used by the corrected Section VIII
route once the block support is fixed.  It strengthens the exposition by
replacing a sequence of local comparisons with one exact formula.

It does **not** close the remaining global theorem.  The unresolved step is
still the disjoint reindexing of every attained canonical high skeleton by:

```text
block support + admissible deficits + local partial physical matchings,
```

with neither omission nor multiplicity and with exact aggregate weight
preservation.  The theorem below begins after that support-and-multiplicity data
has been fixed.

## Setup

Let \(P\) be a matching of selected block pairs.  For \(e\in P\), let the two
endpoint blocks have sizes \(s_e,t_e\), and put

\[
  m_e:=\min\{s_e,t_e\},
  \qquad
  d_e:=|s_e-t_e|.
\]

Choose a deficit \(0\le h_e\le m_e\), and write

\[
  j_e:=m_e-h_e,
  \qquad
  J:=\sum_{e\in P}j_e,
  \qquad
  H:=\sum_{e\in P}h_e.
\]

Thus the full-containment reference has total multiplicity \(J+H\).

A size-\(j\) physical fibre between labelled blocks of sizes \(s,t\) is a
partial bijection between a \(j\)-subset of the first block and a \(j\)-subset
of the second.  Let \(\mathcal M_{s,t}(j)\) denote this finite set.  The exact
signed-overlap cell factor is

\[
  g(j):=2^{\binom j2-1}.
\]

For fixed \(P\) and \(j=(j_e)\), define the aggregate physical weight

\[
  w(P,j)
  :=
  \frac1{(n)_J}
  \prod_{e\in P}
    |\mathcal M_{s_e,t_e}(j_e)|g(j_e).
\]

This definition has one global falling-factorial denominator.  It does not
replace that denominator by a product of independent ambient denominators.

## Exact theorem

### Theorem

For every fixed support \(P\) and admissible multiplicity vector \(j=m-h\):

1. the local fibre cardinality is
   
   \[
     |\mathcal M_{s,t}(j)|
     =\binom sj\binom tj j!
     =\frac{(s)_j(t)_j}{j!};
   \]

2. for endpoint sizes \(m,m+d\), the exact local weighted deficit ratio is
   
   \[
     \frac{
       |\mathcal M_{m,m+d}(m-h)|g(m-h)
     }{
       |\mathcal M_{m,m+d}(m)|g(m)
     }
     =R_{m,d}(h),
   \]
   
   where
   
   \[
     R_{m,d}(h)
     :=
     \frac{\binom mh}{(d+1)(d+2)\cdots(d+h)}
     2^{-hm+h(h+1)/2};
   \]

3. the full fixed-support ratio is the exact identity
   
   \[
     \boxed{
     \frac{w(P,m-h)}{w(P,m)}
     =(n-J)_H\prod_{e\in P}R_{m_e,d_e}(h_e).}
   \]

Consequently,

\[
  \frac{w(P,m-h)}{w(P,m)}
  \le
  \prod_{e\in P}n^{h_e}R_{m_e,d_e}(h_e).
\]

If the high-cell condition gives \(2h_e<m_e\) whenever \(h_e>0\), then

\[
  R_{m_e,d_e}(h_e)
  \le
  \left(
    \frac{m_e}{2^{\lfloor2m_e/3\rfloor}}
  \right)^{h_e}.
\]

Hence, with

\[
  \rho_n:=
  \max_m\frac{nm}{2^{\lfloor2m/3\rfloor}},
\]

one has

\[
  \frac{w(P,m-h)}{w(P,m)}
  \le
  \rho_n^H.
\]

### Proof

Choose the \(j\) left endpoints, choose the \(j\) right endpoints, and choose a
bijection between them.  This gives

\[
  |\mathcal M_{s,t}(j)|
  =\binom sj\binom tj j!
  =\frac{(s)_j(t)_j}{j!}.
\]

Assume \(s=m\) and \(t=m+d\).  The unweighted local ratio is

\[
\begin{aligned}
  \frac{|\mathcal M_{m,m+d}(m-h)|}
       {|\mathcal M_{m,m+d}(m)|}
  &=
  \frac{
    (m)_{m-h}(m+d)_{m-h}/(m-h)!
  }{
    (m)_m(m+d)_m/m!
  }\\
  &=
  \binom mh\frac{d!}{(d+h)!}\\
  &=
  \frac{\binom mh}{(d+1)(d+2)\cdots(d+h)}.
\end{aligned}
\]

The cell-factor ratio is

\[
  \frac{g(m-h)}{g(m)}
  =
  2^{\binom{m-h}{2}-\binom m2}
  =
  2^{-hm+h(h+1)/2}.
\]

Multiplying proves the exact local formula.

For the global ratio, note that the full multiplicity is

\[
  \sum_{e\in P}m_e=J+H.
\]

Therefore

\[
\begin{aligned}
  \frac{w(P,m-h)}{w(P,m)}
  &=
  \frac{(n)_{J+H}}{(n)_J}
  \prod_{e\in P}R_{m_e,d_e}(h_e)\\
  &=
  (n-J)_H
  \prod_{e\in P}R_{m_e,d_e}(h_e).
\end{aligned}
\]

This is the exact one-global-denominator identity.  Since
\((n-J)_H\le n^H=\prod_en^{h_e}\), the displayed upper bound follows.

Finally suppose \(h>0\) and \(2h<m\).  Since

\[
  \frac{\binom mh}{(d+1)\cdots(d+h)}\le m^h,
\]

it remains to control the power of two.  The inequality \(2h<m\) implies
\(h+1\le2m/3\) for \(m\ge3\), and hence

\[
  m-\frac{h+1}{2}
  \ge\frac{2m}{3}
  \ge\left\lfloor\frac{2m}{3}\right\rfloor.
\]

Thus

\[
  -hm+\frac{h(h+1)}2
  \le
  -h\left\lfloor\frac{2m}{3}\right\rfloor,
\]

which proves the geometric majorant.  Multiplying over \(e\in P\) and inserting
the factor \(n^H\) gives the final claim.  \(\square\)

## Why this improves the proof

The corrected Section VIII argument can now be written in three clean steps.

1. **Reindexing theorem:** identify every attained canonical high skeleton with
   one fixed-support physical fibre.  This is the remaining open seam.
2. **Exact ratio theorem:** apply the boxed identity above.
3. **Aggregate summation:** sum the geometric deficit factors and then apply
   the endpoint transport estimate.

The local factorial algebra and the global finite-population denominator no
longer need to be interleaved.  In particular, the proof cannot accidentally
introduce one ambient denominator per high cell.

## Executable finite audit

`625/scripts/verify_physical_fibre_exact_ratio.py` uses only exact integers and
`fractions.Fraction`.  It checks:

- 140 literal partial-matching enumerations for block sizes at most six;
- 1,296 exact local weighted-ratio identities;
- 580 multi-cell exact global-ratio identities with one global denominator;
- 14,160 instances of the high-deficit geometric bound;
- the direction of the replacement \((n-J)_H\le n^H\).

The script prints an explicit scope boundary:

```text
fixed-support physical-fibre identities checked;
global attained-skeleton reindexing not claimed
```

This distinction must remain in the PR description and any manuscript status
statement.