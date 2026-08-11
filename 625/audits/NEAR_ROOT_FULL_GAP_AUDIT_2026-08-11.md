# Erdős 625: one-part-buffer profile and full root-gap retention

Date: 2026-08-11  
Status: candidate theorem-facing strengthening; not welded  
Base: `agent/625-fused-kernel-quarter-refinement` at
`8d04a88889932fd7c7182ad7a73c8f14040f1ac9`

## Question

The previous theorem-facing manuscript placed the signed four-size profile at

```text
ceil((r_4^co+r_+)/2),
```

so it retained one half of the leading separation between the signed and
ordinary first-moment roots. The midpoint was chosen to make the signed first
moment exponentially large on the scale `n/log n`.

The load-bearing question is smaller:

> How large must the signed first moment actually be for the complete
> partial-diagonal and global second-moment arguments?

The answer is that a margin of order `(log n)^2` is sufficient. This permits
placement only one integer part above the signed root and retains the complete
leading root separation.

## Result 1: minimal phase-uniform integer displacement

Define

```text
k_co = ceil(r_4^co)+1,
d_n  = k_co-r_4^co.
```

Then exactly

```text
1 <= d_n < 2.
```

The signed root and `k_co` are both `Theta(n/log n)`, so every intermediate
`k` satisfies

```text
|n/k-n/r_4^co| = O((log n)^2/n)
               = o(log log n/log n).
```

Thus the entire segment remains in the uniform derivative corridor. Since

```text
d Phi_n/dk = (2/log 2)(log n)^2+O(log n log log n),
```

integration over a displacement in `[1,2)` gives

```text
Phi_n(k_co) = Theta((log n)^2).
```

After the existing exact tangent correction and Stirling extraction,

```text
log E Z_k^sgn = Theta((log n)^2)
```

uniformly in the complete phase.

## Result 2: the partial-diagonal proof does not need the midpoint margin

There are only two consumers of the signed first-moment size.

### Central range

The affine extraction uses

```text
-(1/k_co) log E Z
  = sum_i p_i log p_i - 1 + E_bar + o(1).
```

For the one-part profile,

```text
(log E Z)/k_co
  = O((log n)^3/n)
  = o(1).
```

Hence the same uniform upper bound on `E_bar` follows.

### Full corner

The reverse recurrence gives `B(h)<=1`, and therefore

```text
D(k-h) <= 1/E Z <= exp(-c(log n)^2).
```

The four-size profile has at most `(k_co+1)^4` residual subprofiles, so

```text
sum_full D(k-h)
  <= (k_co+1)^4 exp(-c(log n)^2)
  = o(1).
```

The logarithm of the profile count is only `O(log n)`. No other part of
Sections 7--9 uses a macroscopic distance from the signed root.

## Result 3: full leading location gap

The ordinary chromatic lower threshold satisfies

```text
k_chi^- = r_+ + O(log n),
```

whereas the new signed profile satisfies

```text
k_co = r_4^co + O(1).
```

Since `log n=o(n/(log n)^3)`, the deterministic gap is

```text
k_chi^- - k_co
  = [(log 2)^2 A_4(delta_n)/4+o(1)] n/(log n)^3.
```

The midpoint factor `1/2` disappears.

## Result 4: explicit amplification loss from PR #59

The fused-kernel and fixed-buffer critical-quarter estimates give

```text
E[Z^2]/E[Z]^2
  <= exp(C_sharp sqrt(n)(log n)^(3/2)).
```

Thus the seed exponent may be taken as

```text
Lambda_n^sharp=C_sharp sqrt(n)(log n)^(3/2).
```

In the arbitrary-seed amplifier, choose `r_n=log n`. The added number of
parts is

```text
O(sqrt(n Lambda_n^sharp)/log n)
  = O(n^(3/4)(log n)^(-1/4)).
```

The remaining terms are smaller. Moreover,

```text
n^(3/4)(log n)^(-1/4)
  / (n/(log n)^3)
  = (log n)^(11/4)/n^(1/4)
  -> 0.
```

Hence amplification consumes none of the leading root coefficient.

## Quantitative strengthening

The exact four-support certificate remains

```text
A_4(delta)>log(20000/12777)
          =log(1000/639)+log(12780/12777).
```

The candidate uniform coefficient is therefore

```text
((log 2)^2/4) log(1000/639)
  = 0.053792819616758...
```

The stronger pre-slack coefficient is

```text
((log 2)^2/4) log(20000/12777)
  = 0.053821018526027...
```

The previous midpoint coefficient was exactly one half of the first number.

## Formal simplification

The new interface removes the need to formalize a midpoint selector and a
separate theorem saying that exactly half the root separation is retained. The
new formal spine is:

1. `1 <= ceil(x)+1-x < 2`;
2. bounded class-count displacement stays in the root corridor;
3. integrate the existing slope estimate over `[1,2)`;
4. reuse finite optimizer positivity and tangent rounding;
5. use `exp(-c(log n)^2)` in the full corner;
6. consume the already sharpened seed exponent in the final amplifier.

## Verification boundary

This is a candidate strengthening, not a proof-closure declaration. Before it
can replace the current theorem statement, it still requires:

1. independent line-by-line review of the near-root first-moment argument;
2. exact Lean statements with the same ceiling convention and quantifier order;
3. replay of the revised full corner against the exact complementary identity;
4. integrated replay of the fused skeleton and attachment bounds at the same
   integer profile;
5. final warning-fatal build and axiom audit;
6. synchronization of the displayed coefficient with the final replayed theorem.

The publication switch remains false.
