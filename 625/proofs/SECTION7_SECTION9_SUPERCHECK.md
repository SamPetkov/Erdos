# Erdős 625: isolated Section 7 and Section 9 simplifications

**Status.** This note isolates two claims from draft PR #27 that survived a
second adversarial review and an independent exact finite test suite.  It is a
review note, not a replacement for the canonical manuscript and not a proof of
`Erdos625Statement`.

Throughout,

\[
 q=\ln 2,\qquad N=\ln n.
\]

## 1. An exact central-rate certificate

Use the notation of Lemma 7.1 of the canonical manuscript.  Let
\(p=(p_i)_{i=2}^5\) be a probability vector with mean

\[
 \sum_{i=2}^5 i p_i=T,
 \qquad
 \frac2q\le T\le1+\frac2q.
\]

For \(0\le z_i\le p_i\), put

\[
 R=\sum_i z_i,\qquad Y=1-R,\qquad I_r=\sum_i i z_i,
\]

and

\[
 \Phi_T(z)=R\ln R+\frac q2(I_r-TR).
\]

### Lemma 1.1

For \(1/64\le R\le1\),

\[
 \boxed{\Phi_T(z)\le-\frac{1-R}{100}.}
 \tag{1.1}
\]

### Proof

The support bounds give

\[
 I_r-TR\le(5-T)R,
 \tag{1.2}
\]

while, with \(y_i=p_i-z_i\),

\[
 I_r-TR=\sum_i(T-i)y_i\le(T-2)(1-R).
 \tag{1.3}
\]

For \(1/64\le R\le47/100\), use \(T\ge2/q\):

\[
 \Phi_T(z)\le R\ln R+(5q/2-1)R.
 \tag{1.4}
\]

The function

\[
 f(R)=R\ln R+(5q/2-1)R+\frac{1-R}{100}
\]

is convex.  Its endpoint values are strictly negative.  The accompanying
script certifies these signs using exact `Fraction` bounds obtained from

\[
 \ln x=2\,\operatorname{arctanh}\!\left(\frac{x-1}{x+1}\right).
\]

In particular, it proves rational upper bounds below zero for
\(f(1/64)\) and \(f(47/100)\).  Convexity then gives \(f\le0\) on the
whole interval.

For \(47/100\le R\le1\), use \(T\le1+2/q\):

\[
 \Phi_T(z)\le R\ln R+(1-q/2)(1-R).
 \tag{1.5}
\]

The function

\[
 h(R)=R\ln R+(1-q/2+1/100)(1-R)
\]

is convex, satisfies \(h(1)=0\), and has a rigorously certified negative
value at \(47/100\).  Hence \(h\le0\) on the second interval.  Combining
the two ranges proves (1.1).  \(\square\)

This improves the manuscript's displayed constant \(1/5000\) to
\(1/100\).  It does not change the asymptotic order, but gives substantially
more room when absorbing the entropy and Stirling errors in the central
partial-diagonal range.

## 2. Residual restriction replaces the cycle-to-walk argument

Start from equation (9.12) of the canonical manuscript.  Let \(M\) be the
exposed canonical high matching and let \(R\) be the finite potential residual
edge relation.  For an even edge set \(F\subseteq M\cup R\), the matching edges
have weight one and each residual edge \(e\) has a nonnegative weight \(q_e\).

### Lemma 2.1 (unique even completion)

The map

\[
 F\longmapsto F\setminus M
 \tag{2.1}
\]

is injective on the family of even edge sets contained in \(M\cup R\).

### Proof

If two even sets have the same restriction, their symmetric difference is an
even edge set contained in \(M\).  A nonempty subset of a matching has degree
one at every incident vertex, so it is not even.  The symmetric difference is
therefore empty.  \(\square\)

### Corollary 2.2 (weighted subset-product bound)

\[
 \sum_{F\text{ even}}\prod_{e\in F\setminus M}q_e
 \le
 \sum_{S\subseteq R\setminus M}\prod_{e\in S}q_e
 =
 \prod_{e\in R\setminus M}(1+q_e)
 \le
 \exp\!\left(\sum_{e\in R\setminus M}q_e\right).
 \tag{2.2}
\]

The first inequality follows from Lemma 2.1 by enlarging the image to the full
power set.  The equality is the finite subset generating-function identity,
and the final inequality uses \(1+x\le e^x\).

The finite injection already has a Lean counterpart in
`EvenMatchingRestriction.lean`, and the generic product-to-exponential algebra
has a counterpart in `Section9FiniteFamilyAlgebra.lean`.  This note does not
claim that the complete probability specialization is already formalized.

## 3. The improved large-residual envelope

Equation (9.12) and Corollary 2.2 give

\[
 \mathcal A(M,j)
 \le
 \exp\!\left(\Lambda_0+\sum_{e\in R\setminus M}q_e\right).
 \tag{3.1}
\]

For off-matching cells define

\[
 \widetilde\theta_{ab}=\frac{e\,d_a d_b'}{m_0}.
\]

Because \(q_e=0\) on \(M\), the correct identity and inequality are

\[
 \sum_{e\in R\setminus M}q_e
 =\frac12\sum_{(a,b)\notin M}\widetilde\theta_{ab}^{\,2}+\Lambda_0
 \le
 \frac12\sum_{a,b}\widetilde\theta_{ab}^{\,2}+\Lambda_0.
 \tag{3.2}
\]

Only the unrestricted square sum factorizes:

\[
 \sum_{a,b}\widetilde\theta_{ab}^{\,2}
 =\frac{e^2}{m_0^2}
   \left(\sum_a d_a^2\right)
   \left(\sum_b(d_b')^2\right).
 \tag{3.3}
\]

Every residual degree is at most \(U\), and both degree sums equal \(m_0\).
Thus

\[
 \sum_a d_a^2\le Um_0,
 \qquad
 \sum_b(d_b')^2\le Um_0,
 \tag{3.4}
\]

so

\[
 \sum_{a,b}\widetilde\theta_{ab}^{\,2}\le e^2U^2.
 \tag{3.5}
\]

Using the existing large-residual estimate

\[
 \Lambda_0\le C\frac{U^4}{m_0},
 \tag{3.6}
\]

we obtain

\[
 \boxed{
 \mathcal A(M,j)
 \le
 \exp\!\left\{C\left(U^2+\frac{U^4}{m_0}\right)\right\}.}
 \tag{3.7}
\]

When \(m_0\ge n/N^6\) and \(U=O(N)\),

\[
 \frac{U^4}{m_0}=O(N^{10}/n)=o(1),
\]

and therefore

\[
 \mathcal A(M,j)\le\exp(O(N^2))
 =\exp\{o(n/N^4)\}.
 \tag{3.8}
\]

This replaces the manuscript's \(\exp(O(N^8))\) large-residual envelope and
removes the simple-cycle decomposition, residual-walk enumeration, mixed
matching-cycle encoding, the parameter \(\tau\), and the term \(h\tau\).

## 4. Scope boundary

The arguments above depend on the canonical manuscript's threshold expansion
through (9.12) and its local increment estimate through (9.13).  They do not
prove the Section 8 global high-skeleton sum, the complete normalized second
moment, or `Erdos625Statement` by themselves.

The companion exact script exhausts all matchings, residual relations, and even
edge sets for \(K_{2,2}\), \(K_{2,3}\), and \(K_{3,3}\), checks two rational
weight systems, verifies the off-matching square-sum inequality on more than
six hundred thousand degree/matching instances, and certifies the Section 7
endpoint signs by rational logarithm bounds.  These are regression tests, not a
substitute for the displayed proofs.
