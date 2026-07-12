# Erdős Problem 625 — confirmed research brief

Confirmed by the user on 2026-07-11.

## Target theorem

For `G_n ~ G(n,1/2)`, determine whether

`for every M in N, P(chi(G_n) - zeta(G_n) >= M) -> 1`.

A positive proof must cover every sufficiently large integer `n`. A negative
proof must give fixed `M`, fixed `delta > 0`, and infinitely many explicit
`n_j` for which `P(chi(G_{n_j}) - zeta(G_{n_j}) <= M) >= delta`.

## Conventions

- `whp` means convergence in probability unless a coupling is explicitly set.
- `log_2` is base two; `ln` is natural logarithm.
- Proof, numerical evidence, and heuristic claims are kept separate.
- A first-moment threshold is not treated as an actual threshold without a
  matching existence/concentration argument.

## Acceptance and fallback

The primary acceptance condition is a complete positive or negative proof,
with source dependencies and independent adversarial audits. If that is not
obtained, the fallback is an auditable dossier that precisely identifies the
best proved statements and the remaining lemma; it is not called a resolution.

## Runtime constraints

Four agents can be active concurrently. Research therefore proceeds in repeated
four-agent waves. No paid external PhysicsIntern provider run is authorized by
default.
