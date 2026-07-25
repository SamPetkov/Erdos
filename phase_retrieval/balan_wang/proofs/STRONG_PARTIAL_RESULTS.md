# Deterministic Balan–Wang instability at `N = 2M-1`

## Strong partial results, exact reductions, and the remaining TNS obstruction

**Status, 25 July 2026.** This note does not resolve the universal conjecture.
It records the strongest deterministic package obtained from two logically
independent cycles: a proof-first cycle and a counterexample-first cycle. The
cycles are merged only after each has produced a concrete theorem or a precise
obstruction.

The claims below are self-contained research claims pending external review.
The literature discussion is deliberately conservative and makes no novelty or
priority assertion.

---

## 1. Setup and conjecture

Let `M >= 2`, `N = 2M-1`, and let

\[
A\in\mathbb R^{N\times M}
\]

have rows `a_1^T,\ldots,a_N^T`. For `S\subseteq[N]`, let `A_S` denote the
row submatrix. Assume that `A` is **full spark**, meaning that every `M` rows
are linearly independent.

Define

\[
R(A)=\max_i\|a_i\|_2
\]

and, in the original complement convention,

\[
\omega(A)=
\min_{\substack{S\subseteq[N]\\
\operatorname{rank}(A_{S^c})<M}}
\sigma_{\min}(A_S).
\]

The Balan–Wang conjecture asks for universal constants `C>0` and `0<beta<1`
such that

\[
\omega(A)\le C R(A)\beta^M
\tag{BW}
\]

for every `M` and every full-spark `A` at the critical row count.

After normalizing `R(A)=1`, define

\[
\rho_M=\sup\{\omega(A):A\in\mathbb R^{(2M-1)\times M}
\text{ full spark},\ R(A)=1\}
\]

and

\[
\beta_*=\limsup_{M\to\infty}\rho_M^{1/M}.
\]

The conjecture is exactly `beta_* < 1`. The Gaussian result of Shmalo gives the
benchmark `beta_* >= 1/4`; it does not prove the deterministic upper bound.

---

# Part I. Mandatory exact reductions

## 2. Reduction to square row submatrices

### Proposition 2.1

For every full-spark `A\in\mathbb R^{(2M-1)\times M}`,

\[
\boxed{\omega(A)=\min_{\substack{S\subseteq[2M-1]\\|S|=M}}
\sigma_{\min}(A_S).}
\tag{2.1}
\]

### Proof

If `rank(A_{S^c})<M`, then `S^c` cannot contain `M` rows, since every `M`
rows are independent. Hence `|S^c|\le M-1`, so `|S|\ge M`.

Choose an `M`-subset `T\subseteq S`. Then

\[
A_S^TA_S=A_T^TA_T+A_{S\setminus T}^TA_{S\setminus T}
\succeq A_T^TA_T,
\]

and therefore

\[
\sigma_{\min}(A_S)\ge\sigma_{\min}(A_T).
\]

Conversely, every `M`-subset `T` is admissible in the original definition,
because `T^c` has only `M-1` rows. Taking minima proves (2.1). `\square`

This reduction preserves exact constants.

---

## 3. Projection order statistics

For `x\in S^{M-1}`, set

\[
z_i(x)=|\langle a_i,x\rangle|
\]

and order the values as

\[
z_{(1)}(x)\le\cdots\le z_{(2M-1)}(x).
\]

### Proposition 3.1

\[
\boxed{
\omega(A)=\min_{\|x\|_2=1}
\left(\sum_{j=1}^{M}z_{(j)}(x)^2\right)^{1/2}.}
\tag{3.1}
\]

### Proof

For a fixed `M`-subset `S`,

\[
\sigma_{\min}(A_S)^2
=\min_{\|x\|=1}\sum_{i\in S}|\langle a_i,x\rangle|^2.
\]

The family of subsets is finite, so the two minima may be interchanged. For a
fixed `x`, the minimizing set contains the indices of the `M` smallest
projections. `\square`

This formulation also preserves exact constants.

---

## 4. Negative second moment and incidence distance

For an invertible `M\times M` matrix `B` with rows `b_i^T`, define

\[
d_i(B)=\operatorname{dist}
\bigl(b_i,\operatorname{span}\{b_j:j\ne i\}\bigr).
\]

### Proposition 4.1 — negative second-moment identity

\[
\boxed{
\sum_{k=1}^{M}\sigma_k(B)^{-2}
=\sum_{i=1}^{M}d_i(B)^{-2}.}
\tag{4.1}
\]

### Proof

Put `y_i=B^{-1}e_i`. Then `By_i=e_i`, so `y_i` is orthogonal to every row
except `b_i`, and `\langle b_i,y_i\rangle=1`. Hence

\[
\|y_i\|_2=d_i(B)^{-1}.
\]

Therefore

\[
\sum_i d_i(B)^{-2}
=\sum_i\|B^{-1}e_i\|_2^2
=\|B^{-1}\|_F^2
=\sum_k\sigma_k(B)^{-2}.
\qquad\square
\]

It follows that

\[
\boxed{
\frac1{\sqrt M}\min_i d_i(B)
\le\sigma_{\min}(B)
\le\min_i d_i(B).}
\tag{4.2}
\]

For the full frame define

\[
D(A)=\min_{\substack{|T|=M-1\\i\notin T}}
\operatorname{dist}(a_i,\operatorname{span}A_T).
\]

Applying (4.2) to every square row submatrix gives

\[
\boxed{
\frac{D(A)}{\sqrt M}\le\omega(A)\le D(A).}
\tag{4.3}
\]

Thus the incidence formulation loses only a polynomial factor and is
exponentially equivalent to (BW).

---

# Part II. Normalization and Parseval reduction

## 5. Rowwise normalization is monotone

Assume `R(A)\le1` and write `r_i=\|a_i\|_2>0`. Define

\[
\widetilde a_i=a_i/r_i.
\]

For every subset `S`,

\[
\widetilde A_S^T\widetilde A_S-A_S^TA_S
=\sum_{i\in S}(r_i^{-2}-1)a_ia_i^T\succeq0.
\]

Consequently

\[
\omega(\widetilde A)\ge\omega(A).
\]

Hence

\[
\boxed{
\rho_M=\max\{\omega(A):A\text{ full spark and }\|a_i\|_2=1
\text{ for every }i\}.}
\tag{5.1}
\]

The maximum exists. The product of unit spheres is compact, `omega` is
continuous, and every non-full-spark configuration has `omega=0`, while
full-spark configurations with positive `omega` exist.

This proves that unit row norms may be imposed at an extremizer. It does not
prove tightness.

---

## 6. Parseval frames are exponentially equivalent to general frames

Define

\[
\rho_M^{\mathrm P}=
\sup\left\{
\frac{\omega(U)}{R(U)}:
U^TU=I_M,\ U\in\mathbb R^{(2M-1)\times M}
\text{ full spark}
\right\}.
\]

### Proposition 6.1

\[
\boxed{
\rho_M^{\mathrm P}\le\rho_M
\le\sqrt{2M-1}\,\rho_M^{\mathrm P}.}
\tag{6.1}
\]

In particular,

\[
\limsup_{M\to\infty}(\rho_M^{\mathrm P})^{1/M}=\beta_*.
\]

### Proof

The first inequality follows by rescaling a Parseval frame by `R(U)^{-1}`.

For the second, normalize `R(A)=1`, let

\[
G=A^TA,
\qquad
U=AG^{-1/2}.
\]

Then `U^TU=I_M` and `A_S=U_SG^{1/2}`. For every `S`,

\[
\sigma_{\min}(U_SG^{1/2})
\le\|G^{1/2}\|\,\sigma_{\min}(U_S).
\]

Therefore

\[
\omega(A)\le\sqrt{\lambda_{\max}(G)}\,\omega(U).
\]

A Parseval frame has `R(U)\le1`, because `UU^T` is an orthogonal projection.
Moreover,

\[
\lambda_{\max}(G)\le\operatorname{tr}G
=\sum_i\|a_i\|_2^2\le2M-1.
\]

Taking the supremum gives (6.1). `\square`

Thus an exponential theorem for all Parseval frames would settle the universal
problem with the same exponential base, up to a polynomial loss.

---

# Cycle A — proof-first

## 7. A universal polynomial bound

### Theorem 7.1 — `M+2`-row Gale bound

For every `M>=3`,

\[
\boxed{
\rho_M\le
\frac{2\sin(\pi/(M+2))}
{\sqrt{M+2-2\sin^2(\pi/(M+2))}}.}
\tag{7.1}
\]

Consequently,

\[
\boxed{\rho_M\le(2\pi+o(1))M^{-3/2}.}
\tag{7.2}
\]

This is a polynomial theorem and therefore does not resolve (BW).

### Proof

Choose any `n=M+2` rows of a unit-row critical frame and call the resulting
matrix `B`. Let

\[
U\in\mathbb R^{n\times2}
\]

have orthonormal columns spanning `ker(B^T)`. Every two rows of `U` are
independent. Indeed, if `T` is a two-set and `U_Tt=0` for nonzero `t`, then
`z=Ut` is nonzero, belongs to `ker(B^T)`, and is supported on `S=T^c`; hence
`B_S^Tz_S=0`, contradicting the full spark of the `M` rows in `S`.

Write the rows of `U` as

\[
u_i=r_iv_i,
\qquad r_i>0,
\qquad v_i\in S^1.
\]

Order their projective directions cyclically in an interval of length `pi`.
Let the successive gaps be `alpha_i>0`, with

\[
\sum_{i=1}^{n}\alpha_i=\pi.
\]

Put `m_i=min(r_i,r_{i+1})`. Since `U^TU=I_2`,

\[
\sum_i r_i^2=2,
\qquad
\sum_i m_i\le\sum_i r_i\le\sqrt{2n}.
\]

Concavity of sine gives

\[
\sum_i\sin\alpha_i\le n\sin(\pi/n).
\]

Cauchy–Schwarz implies

\[
\min_i m_i\sin\alpha_i
\le
\left(\frac1n\sum_i\sqrt{m_i\sin\alpha_i}\right)^2
\le
\frac{\sum_i m_i}{n}\frac{\sum_i\sin\alpha_i}{n}
\le
\sqrt{\frac2n}\sin\frac\pi n.
\]

Choose an adjacent pair `T` attaining this bound. Testing `U_T` on a unit
vector perpendicular to the larger of the two row directions gives

\[
\sigma_{\min}(U_T)
\le\delta_n,
\qquad
\delta_n:=\sqrt{\frac2n}\sin\frac\pi n.
\]

Choose `t\in S^1` with `\|U_Tt\|\le\delta_n`, and put `z=Ut`. Then
`z\in\ker(B^T)` and `\|z\|=1`. For `S=T^c`,

\[
B_S^Tz_S=-B_T^Tz_T.
\]

Since `\|z_S\|\ge\sqrt{1-\delta_n^2}` and
`\|B_T^T\|\le\sqrt2 R(B)=\sqrt2`,

\[
\sigma_{\min}(B_S)
\le
\frac{\sqrt2\,\delta_n}{\sqrt{1-\delta_n^2}}.
\]

Substituting `n=M+2` proves (7.1). `\square`

This excludes any counterexample family with normalized stability
asymptotically larger than order `M^{-3/2}`. It does not exclude polynomially
smaller families, which would still disprove the exponential conjecture.

---

## 8. A global weighted incidence identity

For `|T|=M-1`, put

\[
v_T^2=\det(A_TA_T^T)
\]

and let `u_T` be a unit normal to `span(A_T)`. Let `G=A^TA`.

For `i\notin T`,

\[
\det(A_{T\cup\{i\}})^2
=v_T^2|\langle a_i,u_T\rangle|^2.
\]

Double-counting incidences and applying Cauchy–Binet gives the exact identity

\[
\boxed{
M\det G
=\sum_{|T|=M-1}v_T^2\,u_T^TGu_T.}
\tag{8.1}
\]

Also,

\[
\sum_{|T|=M-1}v_T^2=e_{M-1}(G).
\]

Since every incidence distance is at least `D(A)`, and there are `M` rows
outside each `T`,

\[
u_T^TGu_T
=\sum_{i\notin T}|\langle a_i,u_T\rangle|^2
\ge M D(A)^2.
\]

Hence

\[
D(A)^2\le\frac{\det G}{e_{M-1}(G)}
=\frac1{\operatorname{tr}(G^{-1})}.
\]

Using

\[
\operatorname{tr}(G)\operatorname{tr}(G^{-1})\ge M^2
\]

and `tr(G)\le(2M-1)R(A)^2`, one obtains

\[
\boxed{
D(A)^2\le\frac{2M-1}{M^2}R(A)^2.}
\tag{8.2}
\]

This identity explains why a bare second-moment or Cauchy–Binet argument stops
at polynomial scale: it controls a weighted quadratic average rather than an
exponentially small extreme incidence.

---

## 9. Exponential decay for real moment-curve frames

### Theorem 9.1 — normalized Vandermonde frames

Let `t_1,\ldots,t_{2M-1}` be distinct points of `[-1,1]`, and define

\[
v(t)=(1,t,\ldots,t^{M-1}),
\qquad
a(t)=\frac{v(t)}{\|v(t)\|_2}.
\]

Let `A` have rows `a(t_i)^T`. Then `A` is full spark and

\[
\boxed{
\omega(A)
\le M\,2^{-2(M-1)^2/M}
\le16M\,4^{-M}.}
\tag{9.1}
\]

For arbitrary row scalings along the same projective directions,

\[
\boxed{\omega(A)\le16M R(A)4^{-M}.}
\tag{9.2}
\]

Thus this restricted class has upper exponential base at most `1/4`.

### Proof

One of the intervals `[-1,0)` and `[0,1]` contains at least `M` nodes. Choose
`s_1,\ldots,s_M` in that interval and define

\[
q(t)=\prod_{j=1}^{M}(t-s_j).
\]

For each `i`, let

\[
P_i(t)=\frac{q(t)}{t-s_i}
\]

and let `c_i` be its coefficient vector in the monomial basis. Since `P_i` is
monic, `\|c_i\|_2\ge1`. Put `x_i=c_i/\|c_i\|_2`. On the selected submatrix,
all but one coordinates of `A_Sx_i` vanish, and

\[
|\langle a(s_i),x_i\rangle|
=\frac{|q'(s_i)|}{\|v(s_i)\|_2\|c_i\|_2}
\le|q'(s_i)|.
\]

Therefore

\[
\sigma_{\min}(A_S)\le\min_i|q'(s_i)|.
\]

Let

\[
V=\prod_{i<j}|s_i-s_j|.
\]

Since `\prod_i|q'(s_i)|=V^2`,

\[
\min_i|q'(s_i)|\le V^{2/M}.
\]

Map the containing interval of length one affinely to `[-1,1]`, obtaining
points `y_i`. The Chebyshev evaluation determinant satisfies

\[
\left|\det(T_{j-1}(y_i))_{i,j=1}^{M}\right|
=2^{(M-1)(M-2)/2}\prod_{i<j}|y_i-y_j|.
\]

Every evaluation row has Euclidean norm at most `sqrt(M)`, so Hadamard's
inequality gives

\[
\prod_{i<j}|y_i-y_j|
\le M^{M/2}2^{-(M-1)(M-2)/2}.
\]

Undoing the affine scaling yields

\[
V\le M^{M/2}2^{-(M-1)^2}.
\]

Taking the `2/M` power proves the first inequality in (9.1). The second follows
from

\[
2^{-2(M-1)^2/M}=2^{-2M+4-2/M}<16\,4^{-M}.
\]

Row scalings of size at most `R(A)` add only the factor `R(A)`. `\square`

No claim of novelty is made for this restricted theorem without a dedicated
Chebyshev-system literature review.

---

## 10. Max-volume normal form and the TNS obstruction

Choose an `M`-row basis `B` maximizing `|det B|`. After permuting rows,

\[
A=\begin{bmatrix}I_M\\C\end{bmatrix}B,
\qquad
C\in\mathbb R^{(M-1)\times M}.
\tag{10.1}
\]

If `R` is a `k`-subset of the rows of `C` and `J` is a `k`-subset of its
columns, the corresponding mixed basis has determinant

\[
\pm\det(B)\det(C_{R,J}).
\]

It follows that

\[
\boxed{
C\text{ is totally nonsingular},
\qquad
|\det(C_{R,J})|\le1
\text{ for every square minor}.}
\tag{10.2}
\]

Define

\[
\eta(C)=
\min_{\substack{1\le k\le M-1\\|R|=|J|=k}}
\sigma_{\min}(C_{R,J})
\]

and

\[
F(C)=\begin{bmatrix}I_M\\C\end{bmatrix}.
\]

### Proposition 10.1

\[
\boxed{
\frac{\eta(C)}{M+4}
\le\omega(F(C))
\le\eta(C).}
\tag{10.3}
\]

### Proof

After row and column permutations, every mixed square row submatrix of `F(C)`
has the form

\[
H=\begin{bmatrix}I&0\\D&E\end{bmatrix},
\]

where `E` is a square submatrix of `C`. Testing `H` on a vector supported on
the `E` columns gives

\[
\sigma_{\min}(H)\le\sigma_{\min}(E),
\]

which proves the upper bound after choosing `E` attaining `eta(C)`.

Conversely,

\[
H^{-1}=\begin{bmatrix}I&0\\-E^{-1}D&E^{-1}\end{bmatrix}.
\]

Every entry of `C` has modulus at most one, so

\[
\|D\|\le\|D\|_F\le\sqrt{k(M-k)}\le M/2.
\]

Since `\|E^{-1}\|\le1/\eta(C)` and `eta(C)\le1`,

\[
\|H^{-1}\|
\le1+\frac{\|D\|+1}{\eta(C)}
\le\frac{M+4}{\eta(C)}.
\]

Thus every mixed basis has least singular value at least
`eta(C)/(M+4)`. The all-identity basis causes no problem. `\square`

For the original frame,

\[
\omega(A)
\le\|B\|\eta(C)
\le\sqrt M R(A)\eta(C).
\tag{10.4}
\]

### Exact remaining algebraic lemma

The universal conjecture is equivalent at exponential scale to the following
statement.

> **Quantitative TNS lemma.** There exist universal `c>0` and `p<infinity`
> such that every totally nonsingular
> \[
> C\in\mathbb R^{(M-1)\times M}
> \]
> whose square minors all have modulus at most one contains a square submatrix
> `E` satisfying
> \[
> \boxed{\sigma_{\min}(E)\le M^p e^{-cM}.}
> \tag{10.5}
> \]

Sufficiency follows from (10.4). Conversely, apply a hypothetical universal
frame theorem to `F(C)`. Since `R(F(C))\le\sqrt M`, Proposition 10.1 yields
(10.5) with only polynomial losses.

This is the precise deterministic obstruction isolated by Cycle A.

---

## 11. Why the remaining proof routes stop

### 11.1 Hyperplane-arrangement volume

The number of sign cells is exponential, so one cell has exponentially small
spherical volume. In dimension `M-1`, converting volume to a linear scale takes
an `(M-1)`st root. An `exp(-cM)` volume estimate therefore yields only a
constant-scale radius. Small volume also does not, by itself, imply small
inradius.

### 11.2 Plücker coordinates without conditioning control

Cauchy–Binet controls

\[
\sum_{|S|=M}\det(A_S)^2,
\]

but

\[
|\det(A_S)|=\prod_{j=1}^{M}\sigma_j(A_S).
\]

An exponentially small determinant may be distributed across all singular
values and give only constant-scale information after taking an `M`th root.
The max-volume/TNS reduction is the point at which the Plücker information is
converted into an explicit conditioning problem.

### 11.3 Gale/Naimark recursion

For a Parseval `U\in\mathbb R^{(2M-1)\times M}` and a Naimark complement
`V\in\mathbb R^{(2M-1)\times(M-1)}`, complementary square submatrices satisfy

\[
\sigma_{\min}(U_S)=\sigma_{\min}(V_{S^c}).
\]

However, `V` has `2M-1=2(M-1)+1` rows, two more than the lower-dimensional
critical count. This row-count mismatch blocks the direct induction.

### 11.4 Polynomial products

The polynomial method succeeds on the moment curve because Chebyshev
polynomials give coefficient control and a sharp Vandermonde-product estimate.
For arbitrary hyperplane normals, no comparable deterministic coefficient
bound was obtained.

---

# Cycle B — counterexample-first

## 12. Exact solution in dimension two

### Theorem 12.1

\[
\boxed{\rho_2=\frac1{\sqrt2}.}
\tag{12.1}
\]

Up to row permutations, row sign changes, and right multiplication by an
orthogonal matrix, the unique extremal projective configuration consists of
three equally spaced lines.

### Proof

By rowwise normalization, take the three rows to be unit vectors. For two
projective lines with acute angle `alpha`,

\[
\sigma_{\min}=\sqrt{1-|\cos\alpha|}
=\sqrt2\sin(\alpha/2).
\]

Three points on a projective circle of total length `pi` contain a pair at
projective distance at most `pi/3`. Therefore

\[
\omega(A)\le\sqrt2\sin(\pi/6)=1/\sqrt2.
\]

The lines at angles `0`, `pi/3`, and `2pi/3` attain equality. Equality in the
spacing argument forces all three gaps to be `pi/3`; decreasing any row norm
strictly decreases the least singular value of a pair containing that row.
`\square`

---

## 13. An exact algebraic lower construction for `rho_3`

Set

\[
h=\frac{48-\sqrt5}{121}.
\]

For `k=0,\ldots,4`, define

\[
a_k=
\left(
\sqrt{1-h}\cos\frac{4\pi k}{5},
\sqrt{1-h}\sin\frac{4\pi k}{5},
\sqrt h
\right).
\tag{13.1}
\]

All rows have norm one. Their two possible off-diagonal inner products are

\[
p=\frac{57-39\sqrt5}{242},
\qquad
 d=\frac{31+17\sqrt5}{121}.
\tag{13.2}
\]

There are two dihedral orbits of triples.

For triples with off-diagonal pattern `(p,p,d)`, the smallest Gram eigenvalue
is

\[
1-d=\frac{90-17\sqrt5}{121}.
\]

For triples with pattern `(p,d,d)`, the smallest Gram eigenvalue is

\[
1+\frac p2-\frac12\sqrt{p^2+8d^2}
=\frac{105-40\sqrt5}{121}.
\]

Both values are positive, so the frame is full spark. Consequently

\[
\boxed{
\rho_3\ge
\frac{\sqrt{105-40\sqrt5}}{11}
=0.358570173636\ldots.}
\tag{13.3}
\]

Exactly five of the ten triples are active. The exact identities and orbit
count are independently checked by the accompanying standard-library script.
Global optimality is not claimed.

---

## 14. A rigorous universal upper bound for `rho_3`

### Theorem 14.1

\[
\boxed{
\rho_3\le\sqrt{\frac{4-\sqrt6}{6}}
=0.5083486758\ldots.}
\tag{14.1}
\]

Hence

\[
\boxed{
0.3585701736\ldots
\le\rho_3
\le0.5083486758\ldots.}
\tag{14.2}
\]

### Proof

By rowwise normalization, let `A\in\mathbb R^{5\times3}` have unit rows. Put
`K=AA^T`. Its three positive eigenvalues `mu_1,mu_2,mu_3` satisfy

\[
\mu_1+\mu_2+\mu_3=\operatorname{tr}K=5.
\]

The characteristic polynomial is

\[
p_K(x)=x^2\prod_{j=1}^{3}(x-\mu_j).
\]

The principal-minor derivative identity gives

\[
\frac{p_K''(x)}2
=\sum_{|S|=3}\det(xI_3-K_S).
\tag{14.3}
\]

Let `r` be the smallest positive zero of `p_K''`. If every `K_S` had smallest
eigenvalue greater than `r`, then every determinant on the right-hand side of
(14.3) would be strictly negative, contradicting `p_K''(r)=0`. Therefore some
triple satisfies

\[
\lambda_{\min}(K_S)\le r.
\tag{14.4}
\]

Write `e_2,e_3` for the elementary symmetric polynomials of the positive
eigenvalues. Then

\[
q_{\mu}(x):=\frac{p_K''(x)}2
=10x^3-30x^2+3e_2x-e_3.
\tag{14.5}
\]

It remains to maximize the smallest positive root `r(\mu)` over
`mu_i>0`, `sum mu_i=5`. Strict interlacing places this root in
`(0,min_i mu_i)`, so it is simple and tends to zero at the boundary of the
simplex. Hence a maximum is attained in the interior and the root is a smooth
function there.

At an interior constrained extremum, implicit differentiation and Lagrange
multipliers give equality of the three partial derivatives of `q_mu` with
respect to `mu_i`. Subtracting the `i` and `j` equations yields

\[
(\mu_i-\mu_j)(3r-\mu_k)=0,
\qquad\{i,j,k\}=\{1,2,3\}.
\tag{14.6}
\]

If the three eigenvalues are distinct, (14.6) forces all three to equal `3r`,
a contradiction. If exactly two are equal, say `mu_1=mu_2=a` and `mu_3=b`,
then (14.6) gives `r=a/3`. Substituting `b=5-2a` and `r=a/3` into (14.5)
gives

\[
\frac{a^2(45-17a)}{27}=0,
\]

so `a=45/17` and `b=-5/17`, impossible. Thus the only interior extremum has

\[
\mu_1=\mu_2=\mu_3=5/3.
\]

At this point

\[
q_{\mu}(x)=\frac5{27}(3x-5)(18x^2-24x+5),
\]

whose smallest positive root is

\[
r=\frac{4-\sqrt6}{6}.
\]

Combining this with (14.4) and taking square roots proves (14.1). `\square`

The bracket remains too wide to determine `rho_3` exactly.

---

## 15. Equal-norm Parseval frames are not universal extremizers

### Proposition 15.1 — exact dimension-three Parseval value

Among full-spark equal-norm Parseval frames
`U\in\mathbb R^{5\times3}`,

\[
\boxed{
\sup\frac{\omega(U)}{R(U)}
=\frac2{\sqrt3}\sin\frac\pi{10}
=\frac{\sqrt5-1}{2\sqrt3}
=0.3568220898\ldots.}
\tag{15.1}
\]

### Proof

Let `V\in\mathbb R^{5\times2}` be a Naimark complement. Then

\[
\|u_i\|^2=3/5,
\qquad
\|v_i\|^2=2/5.
\]

For complementary sets `|S|=3`, `|T|=2`, the cosine-sine decomposition gives

\[
\sigma_{\min}(U_S)=\sigma_{\min}(V_T).
\]

Five projective lines in `R^2` contain a pair at projective distance at most
`pi/5`. Thus

\[
\min_{|T|=2}\sigma_{\min}(V_T)
\le\sqrt{\frac25}\,\sqrt2\sin\frac\pi{10}.
\]

Dividing by `R(U)=sqrt(3/5)` proves the upper bound. Five equally spaced
projective lines form an equal-norm Parseval frame in `R^2`; their Naimark
complement attains equality. `\square`

The squared gap between the cyclic construction and the Parseval optimum is

\[
\frac{105-40\sqrt5}{121}-\frac{3-\sqrt5}{6}
=\frac{267-119\sqrt5}{726}>0,
\]

because

\[
267^2-5\cdot119^2=484>0.
\]

Therefore

\[
\boxed{
\text{no global maximizer for }\rho_3
\text{ can be an equal-norm tight frame}.}
\tag{15.2}
\]

This is a concrete refutation of a blanket tight-frame extremizer reduction.

---

## 16. Counterexample mechanisms that fail

### 16.1 Near-block perturbations

Suppose an `M`-row submatrix of `A_0` is singular and every corresponding row
is perturbed by Euclidean norm at most `epsilon`. Testing on a unit null vector
of the unperturbed submatrix gives

\[
\boxed{\sigma_{\min}(A_S)\le\sqrt M\,\epsilon.}
\tag{16.1}
\]

Thus the small generic coupling used to make a block construction full spark
immediately creates a bad mixed subset.

### 16.2 Highly nonuniform row norms

For every row `a_i`, choose an `M`-subset containing it. Since
`\sigma_{\min}(B)=\sigma_{\min}(B^T)`, testing `B^T` on the coordinate vector
corresponding to this row gives

\[
\boxed{\omega(A)\le\min_i\|a_i\|_2.}
\tag{16.2}
\]

Tiny rows cannot be shielded by the remaining rows.

### 16.3 Plücker-flat constructions

Comparable maximal minors control products of singular values, not individual
least singular values. Without an independent upper bound on the other
singular values, determinant flatness is not a conditioning certificate.

### Cycle-B conclusion

No explicit infinite family satisfying

\[
\omega(A_M)/R(A_M)\ge e^{-o(M)}
\]

was found. The cyclic `M=3` construction is a finite-dimensional lower bound,
not an asymptotic counterexample.

---

# Part III. Merge of the cycles

## 17. Common bottleneck

Cycle A shows that the conjecture would follow from the quantitative TNS lemma,
or equivalently at exponential scale from the Parseval case.

Cycle B shows that the most immediate escape mechanisms—equal-norm tight
extremizers, tiny-row shielding, near-block perturbations, and Plücker-flat
bases—do not provide a counterexample.

The central missing deterministic statement can be expressed in three
polynomially equivalent forms.

### Incidence form

There are universal `c>0` and `p<infinity` such that every critical full-spark
frame satisfies

\[
D(A)\le M^p R(A)e^{-cM}.
\tag{17.1}
\]

### Parseval form

Every critical full-spark Parseval frame satisfies

\[
\omega(U)\le M^p e^{-cM}.
\tag{17.2}
\]

### Max-volume TNS form

Every max-volume-normalized totally nonsingular
`C\in\mathbb R^{(M-1)\times M}` contains a square submatrix with

\[
\sigma_{\min}(E)\le M^p e^{-cM}.
\tag{17.3}
\]

The unresolved issue is not merely that the approximately `4^M` candidate
hyperplanes may be correlated. One needs a quantitative theorem proving that
either the normals are spread enough to create an exponentially close
incidence, or their clustering itself creates a smaller ill-conditioned square
minor.

---

## 18. Approach registry

| Route | Concrete result | Status |
|---|---|---|
| Exact square-submatrix reduction | Equation (2.1) | proved |
| Projection order statistics | Equation (3.1) | proved |
| Negative second moment | Equations (4.1)–(4.3) | proved |
| Row normalization | Unit-row extremizer reduction | proved |
| Whitening | Parseval equivalence up to `sqrt(2M-1)` | proved |
| Gale geometry | Explicit `O(M^(-3/2))` theorem | proved; polynomial only |
| Global incidence moments | Exact weighted identity (8.1) | proved; polynomial only |
| Polynomial/Vandermonde route | Base at most `1/4` for moment-curve frames | proved restricted theorem |
| Plücker/max-volume route | Quantitative TNS normal form | viable; central obstruction isolated |
| Arrangement volume | Exponential volume loses scale under an `(M-1)`st root | blocked |
| Gale/Naimark recursion | Complement relation, wrong lower-dimensional row count | blocked |
| `rho_2` | Exact value and extremizers | proved |
| `rho_3` | Exact algebraic lower bound and rigorous upper bound | proved partial |
| Equal-norm Parseval, `M=3` | Exact optimum; non-extremality globally | proved |
| Near-block families | Bound (16.1) | refuted mechanism |
| Nonuniform norms | Bound (16.2) | refuted mechanism |
| Infinite counterexample certification | No subexponential family | open |

---

## 19. Adversarial audit checklist

The following points were checked explicitly in the derivations above.

- The matrix convention is row-oriented.
- The critical count is exactly `N=2M-1`.
- Full spark means every `M` rows are independent.
- The complement rank convention is used in the correct direction.
- Adding rows increases the Gram matrix in positive-semidefinite order.
- `sigma_min` is not confused with its square.
- `R(A)` is the maximum row norm.
- Only row permutations, row signs, orthogonal right actions, and global scaling
  are treated as symmetries.
- General `GL(M)` whitening is used only with explicit distortion control.
- Determinant bounds are not promoted to least-singular-value bounds without a
  separate conditioning argument.
- Polynomial factors are kept separate from exponential bases.
- The Gaussian theorem is used only as a benchmark and lower bound on the
  universal extremal base.
- The base `1/4` is not assumed to be the universal deterministic base.
- The `M=3` algebraic construction is not described as a global optimizer.
- The TNS lemma is stated as an unresolved quantitative theorem, not as a
  consequence of qualitative total nonsingularity.

---

## 20. Final status

The strongest proved restricted class in this dossier is the normalized real
moment curve, with exponential base at most `1/4` and a polynomial prefactor.
The next decisive unresolved class is the class of all full-spark Parseval
frames.

The small-dimensional information is

\[
\rho_2=1/\sqrt2
\]

and

\[
\frac{\sqrt{105-40\sqrt5}}{11}
\le\rho_3
\le\sqrt{\frac{4-\sqrt6}{6}}.
\]

The universal polynomial estimate gives

\[
\rho_M\le(2\pi+o(1))M^{-3/2},
\]

while the Gaussian construction gives

\[
\beta_*\ge1/4.
\]

Therefore the rigorous universal exponential bracket remains

\[
\boxed{\frac14\le\beta_*\le1.}
\]

The statement `beta_*<1` remains open in this note.

---

## References

1. R. Balan and Y. Wang, *Invertibility and Robustness of Phaseless
   Reconstruction*, arXiv:1308.4718 (2013).
2. Y. Liu and Y. Wang, *On the decay of the smallest singular value of
   submatrices of rectangular matrices*, Asian-European Journal of Mathematics
   9 (2016), 1650075, DOI: 10.1142/S1793557116500753.
3. Y. Shmalo, *Extreme least singular values of Gaussian row submatrices and a
   phase retrieval stability problem*, arXiv:2607.06249 (2026).
4. D. Li, *Robustness of Frames and Totally Nonsingular Matrices*, SIAM Journal
   on Matrix Analysis and Applications 47 (2026), 412–428,
   DOI: 10.1137/25M1766310.
5. B. Alexeev, J. Cahill, and D. G. Mixon, *Full spark frames*, Journal of
   Fourier Analysis and Applications 18 (2012), 1167–1194.

A targeted search through 25 July 2026 found no later deterministic resolution
of the universal conjecture. This sentence records search scope only and is not
an exhaustive priority claim.