# Section VIII: direct half-deficit assembly

## 1. What is being simplified

After the exact physical-fibre and pointwise weight identity in PR #53, the
remaining proof should not pass through another bespoke hierarchy of

```text
exact high deficit subtype
-> optional deficit choice
-> local product expansion.
```

The analytic theorem already uses an optional choice in every distinguishable
block cell.  The clean route is therefore to encode attained demands directly
into that same type.

The second simplification is a harmless enlargement.  An attained high cell
has full endpoint multiplicity `m`, actual multiplicity `j`, and deficit

```text
h = m-j.
```

The canonical high condition implies

```text
2h < m.
```

For an upper bound there is no need to preserve the more complicated exact
window

```text
h <= m - (U/2+1).
```

We may sum every positive deficit satisfying `2h<m`.  The extra terms are
nonnegative, and the sharper three-quarter exponent estimate is stated exactly
under this simpler hypothesis.

## 2. Direct data type

For an abstract block matching `P`, define

```text
allowed_P(e) = {h >= 1 : 2h < m_e}.
```

A support/choice datum is

```text
(P, omega),
```

where `omega(e)` is either

- `none`, representing `h_e=0` and full containment; or
- `some h`, with `h in allowed_P(e)`.

This is precisely `NearSkeletonChoice`.  Decoding gives

```text
j_e = m_e                       if omega(e)=none,
j_e = m_e-h_e                   if omega(e)=some h_e.
```

The attained-demand encoding from PR #48 maps into this type by sending zero
deficit to `none`.  The decoded table is unchanged, so injectivity follows from
the already checked injectivity of the abstract demand table.

## 3. One generic global theorem

Let `R(P)` be any nonnegative reference weight on block supports, and let

```text
q(P,e,h)
```

be the charged local deficit ratio.  The charged weight of `(P,omega)` is

```text
R(P) * product_e q(P,e,omega(e)),
```

with the convention that `none` contributes one.

The new finite assembly theorem gives exactly

```text
sum_(P,omega) chargedWeight(P,omega)
=
sum_P R(P) * product_e
  (1 + sum_(h in allowed_P(e)) q(P,e,h)).
```

If each attained demand weight is bounded pointwise by its encoded charged
weight, injectivity gives the same right-hand side as an upper bound for the
entire attained family.  There is no extra factor for:

- the number of deficit vectors;
- identical endpoint types;
- a choice of physical full completion;
- conversion between two deficit representations.

## 4. Why the enlargement helps formalization

The old exact cutoff depends simultaneously on the global largest endpoint
`U` and the local endpoint `m_e`.  The half-deficit envelope depends only on
`m_e`.  This removes from the global analytic assembly:

1. `allHighDeficitCut` arithmetic;
2. reconstruction of the strict global high inequality after every local
   choice;
3. the theorem that all four endpoint sizes lie above `U/2`;
4. a conversion from a dependent `Fin (m_e+1)` subtype to
   `NearSkeletonChoice`;
5. a separate proof that the analytic product sums exactly the same data as the
   combinatorial encoding.

All that remains is the local inequality

```text
2h < m_e,
```

which is already proved for attained demands and is exactly the premise of the
three-quarter exponent budget.

## 5. Resulting proof architecture

The remaining Section VIII proof can now be organized as follows.

### Finite pointwise step

For one attained demand with encoded support `P` and choice `omega`, prove

```text
profileHighSkeletonWeight(demand)
  <= R(P) * nearSkeletonChoiceWeight(omega).
```

PR #53 supplies the exact left-hand aggregate formula.  The only new algebra is
therefore:

- compare the partial local factors with their full local factors;
- apply the single global falling-factorial loss once.

### Exact finite summation

Apply the direct support/choice theorem.  This automatically produces

```text
sum_P R(P) * product_e (1 + local positive-deficit mass).
```

### Local analytic bound

For

```text
rho_e = n*m_e / 2^floor((3m_e-1)/4),
```

PR #49 gives

```text
q(P,e,h) <= rho_e^h.
```

When `rho_e<=1/2`,

```text
sum_(h>=1, 2h<m_e) q(P,e,h) <= 2*rho_e.
```

### Endpoint reference sum

The zero-deficit support weight `R(P)` is the aggregate full-containment weight
of that block support.  Grouping supports only at this final step by their
four-by-four type table gives the existing endpoint weight `W(L)`.  Endpoint
transport then bounds

```text
sum_P R(P).
```

This is the only place where endpoint table multiplicities are needed.

## 6. Minimal remaining formal statements

After this PR, the useful remaining theorem list is reduced to three items.

1. **Pointwise charged comparison**

   ```text
   profileHighSkeletonWeight(demand)
     <= fullSupportReference(P) * choiceCharge(omega).
   ```

2. **Reference grouping**

   ```text
   sum_P fullSupportReference(P) = sum_L W(L).
   ```

   The required finite cardinalities and the identity with `W(L)` are already
   separately kernel-checked.

3. **Phase adapter**

   ```text
   local positive-deficit mass <= 2*rho_n,
   rho_n = O((log n)^(5/2)/sqrt n).
   ```

The first is the only genuinely new algebraic theorem.  The second is a
Fubini/grouping statement over existing exact fibres.  The third is a routine
specialization of checked one-cell arithmetic.

## 7. Audit boundary

This simplification does not itself prove the bare-skeleton estimate.  It
removes data-conversion and summation bookkeeping from the remaining proof.
The theorem remains conditional until the pointwise charged comparison,
reference grouping, and phase specialization are integrated and built on one
branch.
