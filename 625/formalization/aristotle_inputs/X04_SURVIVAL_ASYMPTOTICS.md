# X04 -- Concrete survival and logarithmic length

Status: send now.  Kind: deterministic asymptotics.  No dependency on
Sections VIII--IX.

## Definitions and target

Set

\[
 u_0(n)=\lceil n^{1/4}\rceil,
 \quad s_0(n)=\lceil n^{1/3}\rceil,
 \quad t(n)=\left\lfloor\frac{\ln n}{13\ln4}\right\rfloor.
\]

Prove eventually along all natural `n` that `2 <= u_0(n)`, that for every
`j < t(n)`

\[
 u_0(n)\le 4^{-j}s_0(n)-\frac13,
\]

and that

\[
 \frac{\ln n}{26\ln4}\le t(n).
\]

The exact declaration `quarterChain_survival_and_length_eventually` is at
`.aristotle/pending-next/x04_survival_asymptotics/QuarterChainAsymptotics/Main.lean`.

## Required proof content

The proof must control both natural floor/ceiling rounding errors and the
uniform quantifier over all `j < t(n)`.  It must be an `atTop` statement on
the full natural sequence, not a subsequence argument or informal exponent
comparison.

## Downstream use

X03 and X04 yield an independent set of at least a fixed positive multiple of
`ln n` in every set of size at least `ceil(n^(1/3))` on the common density
event.
