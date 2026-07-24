# XI02 -- Concrete manuscript threshold instantiation

Status: blocked upstream; do not submit as a monolithic Aristotle request.
Kind: deterministic sequence instantiation plus final probability assembly.

## Highest-value target after sequence definitions exist

For the actual manuscript sequences `kChiConcrete`, `kCoConcrete`, and
`amplificationErrorConcrete`, prove

```text
eventuallyConcreteGapSeparation :
  forall eventually n,
    gapScale n <=
      ((kChiConcrete n + 1 : Nat) : Real) -
        ((kCoConcrete n : Real) + amplificationErrorConcrete n)
```

The `+1` is mandatory because the chromatic event is strict.  This target
should instantiate the accepted theorem `eventually_explicit_gap_threshold`,
not reprove its abstract analysis.

## Exact remaining inputs

1. Define `kChiConcrete` and connect the Sections IV--V first-moment output to
   the at-most probability tending to zero; XI01 then gives the strict-lower
   event probability tending to one.
2. Define `kCoConcrete`, `LambdaConcrete`, and the phase/root error `rho` from
   the Sections VIII--IX output.  Prove the signed seed transports to the
   cocolourability seed and prove `LambdaConcrete = o(n/(ln n)^4)`.
3. Apply X07 with the concrete seed and accepted scale facts to obtain the
   cochromatic-upper event probability tending to one.
4. Prove the concrete root-separation hypothesis and `rho n -> 0` required by
   `eventually_explicit_gap_threshold`.
5. Feed the two event tails and the displayed eventual separation to the
   already accepted conditional assembly theorem.

## Dependency boundary

The chromatic input is from Sections IV--V.  The cochromatic seed and concrete
root profile are from Sections VIII--IX, and the amplified upper tail is X07.
Until both branches are available, a direct request for `Erdos625Statement`
would hide, rather than solve, the remaining theorem obligations.
