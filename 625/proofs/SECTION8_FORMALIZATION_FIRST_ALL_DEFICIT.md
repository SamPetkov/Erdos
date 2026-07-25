# Formalization-first all-high-deficit bound

The sharper review estimate uses the binary exponent budget

\[
em-\frac{e(e+1)}2
\ge e\left\lfloor\frac{3m-1}{4}\right\rfloor
\qquad(2e<m).
\]

That bound is correct and is checked exhaustively in
`sections8_9_simplification_check.py`.  It is, however, stronger than the proof
needs and introduces quarter floors and parity bookkeeping.  A weaker bound is
substantially easier to formalize and still has ample asymptotic room.

## Kernel-checked exponent budget

PR #38 proves in Lean:

\[
\boxed{
 e\left\lfloor\frac{2m}{3}\right\rfloor
 \le em-\frac{e(e+1)}2
 \qquad\text{whenever }2e<m.}
\tag{F8.1}
\]

The proof is pure natural-number arithmetic.  Its key observation is that for
`e>0`, the condition `2e<m` gives

\[
3(e+1)\le2m.
\]

Together with

\[
2\left\lfloor\frac{e(e+1)}2\right\rfloor\le e(e+1),
\]

this yields

\[
3\left\lfloor\frac{e(e+1)}2\right\rfloor\le em,
\]

which is equivalent to retaining at least two thirds of the endpoint exponent.
The declaration is
`highDeficit_twoThird_exponent_budget`.

## One geometric series for the entire high range

For the exact local ratio

\[
A_{m,d}(e)
=n^e\frac{\binom me}{(d+1)\cdots(d+e)}
 2^{-em+e(e+1)/2},
\]

use \(\binom me\le m^e\), the denominator lower bound by one, and (F8.1):

\[
A_{m,d}(e)
\le
\left(\frac{nm}{2^{\lfloor2m/3\rfloor}}\right)^e.
\tag{F8.2}
\]

All four endpoint sizes satisfy \(a-3\le m\le a\).  Set

\[
b_*:=\left\lfloor\frac{2(a-3)}3\right\rfloor,
\qquad
\rho_n:=\frac{na}{2^{b_*}}.
\]

Then every allowed high deficit is bounded by \(\rho_n^e\).  From
\(2^a=\Theta(n^2/(\ln n)^2)\),

\[
\rho_n
=O\!\left(\frac{(\ln n)^{7/3}}{n^{1/3}}\right)
=o(1).
\tag{F8.3}
\]

Consequently the complete deficit sum of one endpoint cell is at most
\(2\rho_n\) eventually.  Since an endpoint high skeleton contains at most
\(k_{\mathrm{co}}=O(n/\ln n)\) cells, all high deficits cost

\[
\exp\{O(k_{\mathrm{co}}\rho_n)\}
=
\exp\{O(n^{2/3}(\ln n)^{4/3})\}
=
\exp\!\left\{o\!\left(\frac n{(\ln n)^4}\right)\right\}.
\tag{F8.4}
\]

## Recommendation for the paper

Use (F8.1)--(F8.4) in the canonical manuscript unless a sharper exponent is
needed later.  The two-thirds budget is weaker numerically than the
three-quarters budget, but it has four practical advantages:

1. it is already kernel-checked at the integer-arithmetic level;
2. it has no parity-sensitive quarter floor;
3. it covers the full high range in one statement;
4. it still removes the complete middle-strip residual argument with a large
   asymptotic margin.

The resulting Section 8 proof becomes: endpoint transport, termwise AM--GM,
one multinomial expansion, and one all-deficit geometric series.  No
near/middle partition or residual configuration model is needed in Section 8.
