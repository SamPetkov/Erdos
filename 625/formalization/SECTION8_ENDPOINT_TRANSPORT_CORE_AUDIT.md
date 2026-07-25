# Audit: Section VIII square-root-free endpoint transport core

## Purpose

`Erdos625/Section8EndpointTransportCore.lean` isolates the finite algebraic core
of manuscript Lemma 8.1.  The manuscript states a geometric-mean inequality
with square roots and quotient factors.  The new module first proves a
cross-multiplied squared form, where every factor is finite and no cancellation
of a possibly zero descending factorial is required.

## New declarations

- `fourEndpointLocalTransportDen`:
  the exact local factor
  `(t)_d 2^(d s + choose(d,2))`;
- `fourEndpointLocalChooseSquare`:
  the squared binomial choice `choose(t,d)^2`;
- `fourEndpointLocalCellFactor_sq_mul_transportDen`:
  the exact one-cell identity;
- `fourEndpointLocalProduct_sq_mul_transportDenProduct`:
  multiplication of the local identities over an arbitrary four-type table;
- `fourEndpoint_global_transport_ennreal`:
  the accepted global falling-factorial transport cast to `ENNReal`;
- `fourEndpoint_squareFree_transport`:
  the combined denominator-free squared endpoint transportation inequality.

## Relation to manuscript (8.8)

For sizes `s <= t=s+d`, the local identity is

\[
  \bigl(s!g(s)\binom td\bigr)^2
  \bigl((t)_d2^{ds+\binom d2}\bigr)
  =
  \bigl(s!g(s)\bigr)\bigl(t!g(t)\bigr)\binom td^2.
\]

After multiplication over cells, the diagonal factors collect according to the
row and column margins.  The accepted falling-factorial theorem supplies

\[
 (n)_{m_r}(n)_{m_c}
 \le (n)_{J(L)}^2(n+1)^{\sum |i-j|\ell_{ij}}.
\]

Their combination is precisely the load-bearing algebra below the square-root
form of (8.8).  A later theorem may divide by the positive factorial factors
and take square roots on the feasible domain.

## Trust and validation

The focused workflow:

- rejects placeholders and project-defined axioms/constants;
- builds the pinned Lean 4.31/mathlib project with `--wfail`;
- compiles the module directly with warnings fatal.

The module prints the axioms of each public theorem.  The ordinary repository
Lean workflow also runs.

## Scope boundary

This PR does not yet prove the complete Lemma 8.1 as printed.  It deliberately
does not:

- cancel the cell-factorial or descending-factorial denominators;
- introduce the real square roots in the geometric-mean statement;
- prove the asymptotic bound `Q_ij <= eta_n^d/d!`;
- perform the Cauchy--multinomial margin summation of Lemma 8.2;
- address near or middle high cells from Lemma 8.3.

It closes the exact endpoint-transport algebra on which those later steps rely.
