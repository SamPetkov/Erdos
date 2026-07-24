# PR #27: exact canonical high-cell exposure

**Status.** Candidate replacement text, audited against current `main` on 24 July 2026.  It is not a completed proof of the asymptotic theorem.

## Replacement block B: exact canonical exposure at the start of Section 8

Replace the prose following equation (8.3) with the following proposition.

### Proposition 8.0 (canonical high-cell exposure identity)

Let \(A,B\) be finite row and column index sets.  Fix degree lists
\((s_a)_{a\in A}\), \((t_b)_{b\in B}\) satisfying

\[
 0\le s_a\le U,\qquad 0\le t_b\le U,
 \qquad
 \sum_a s_a=\sum_b t_b=n.
 \tag{8.3a}
\]

Let \(r=(r_{ab})\) be a feasible overlap table with these margins, put
\(R_0=\lfloor U/2\rfloor\), and define

\[
 M(r)=\{(a,b):r_{ab}>R_0\}.
\]

Then the following hold.

1. **Matching property.**  The support \(M(r)\) is a partial matching.  If two
   selected cells shared a row, their total would be at least
   \(2(R_0+1)>U\), contradicting \(s_a\le U\); the column argument is the same.

2. **Canonical demand and residual table.**  For \(e=(a,b)\in M(r)\), set
   \(j_e=r_{ab}\), \(J=\sum_{e\in M(r)}j_e\), and

   \[
    d_a=\sum_{b:(a,b)\in M(r)}j_{ab},
    \qquad
    d_b'=\sum_{a:(a,b)\in M(r)}j_{ab}.
   \]

   Remove the selected paired stubs and define

   \[
    s_a'=s_a-d_a,
    \qquad
    t_b'=t_b-d_b',
    \qquad
    r'_{ab}=\begin{cases}
       0,&(a,b)\in M(r),\\
       r_{ab},&(a,b)\notin M(r).
    \end{cases}
   \]

   The table \(r'\) has margins \((s_a')\), \((t_b')\), both summing to
   \(n-J\); it vanishes on \(M(r)\) and satisfies \(r'_{ab}\le R_0\) off it.

3. **Exact finite reconstruction.**  Let \(\mathcal D(s,t,U)\) be the
   finite image of the canonical high-demand map.  For
   \(D=(M,j)\in\mathcal D(s,t,U)\), let \(\mathcal W(D)\) be the finite set of
   labelled prescribed-demand witnesses.  For a witness \(w\in\mathcal W(D)\),
   let \(\Omega_{\rm res}(w)\) be the residual matching space with the displayed
   residual margins, zero-on-\(M\), and cap-off-\(M\) conditions.  A full
   matching is recovered uniquely from \((D,w,\omega)\), and canonical
   extraction gives the inverse map.  Thus the exact finite decomposition is
   the dependent disjoint union

   \[
    \Omega(s,t)\ \cong\
    \bigsqcup_{D\in\mathcal D(s,t,U)}
      \bigsqcup_{w\in\mathcal W(D)}\Omega_{\rm res}(w).
    \tag{8.3b}
   \]

   The dependence on \(w\) is material: residual stub types are canonically
   relabelled for each witness before comparison with a standard residual
   configuration space.

4. **Exact mass cancellation.**  The aggregate normalized incidence obtained by
   summing all labelled witnesses for the demand \(D=(M,j)\) is

   \[
    \pi(M,j)=
    \frac{\prod_a(s_a)_{d_a}\prod_b(t_b)_{d_b'}}
         {(n)_J\prod_{e\in M}j_e!}.
    \tag{8.3c}
   \]

   After any fixed witness is standardized, the residual contingency-table mass
   is

   \[
    p_{\rm res}(r')=
    \frac{\prod_a(s_a-d_a)!\prod_b(t_b-d_b')!}
         {(n-J)!\prod_{a,b}r'_{ab}!}.
    \tag{8.3d}
   \]

   The residual table law is the same for all witnesses after unused-stub
   relabelling.  Since \((s)_d=s!/(s-d)!\) and
   \((n)_J=n!/(n-J)!\),

   \[
    \pi(M,j)p_{\rm res}(r')
    =\frac{\prod_a s_a!\prod_b t_b!}
           {n!\prod_{a,b}r_{ab}!}
    =p(r).
    \tag{8.3e}
   \]

Thus the canonical exposure is a genuine partition of the finite matching
space, not a union bound or a proportionality statement.  The cap assumptions
in (8.3a) are essential; without them the matching assertion is false.

### Definition 8.0A (bare canonical-skeleton weight)

For a feasible canonical skeleton \((M,j)\), set

\[
 \operatorname{Bare}(M,j)=\pi(M,j)\prod_{e\in M}g(j_e).
 \tag{8.3f}
\]

The residual cap/no-return event and its local/cycle factor remain in the
conditional residual law.  A later use of the full residual integrand as a
nonnegative majorant does not redefine \(\operatorname{Bare}\) and does not
cause that factor to be applied twice.

---
