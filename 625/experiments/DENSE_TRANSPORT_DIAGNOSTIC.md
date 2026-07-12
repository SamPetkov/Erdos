# Dense four-type transport diagnostic

`dense_transport_scan.py` evaluates the exact factorial weight `W(L)` from
`RESIDUAL_ATTACHMENT.md`, equation (4.11), for the four class sizes
`alpha-2,...,alpha-5`.  It keeps the global falling factorial `(n)_J`
through `lgamma`; it does not replace dense cells by independent one-cell
probabilities.

Run:

```powershell
python research\experiments\dense_transport_scan.py
```

The retained run used `n=10^5,10^6,10^7`.  At each size it checked diagonal
common subprofiles at masses `0.01,0.1,0.5,0.9,1` and four families of
off-type two-cycle perturbations.  Every dense weight tested had negative
logarithm of order at least `n/log n` near the full endpoint and order `n`
in the fixed-mass interior.  Some off-type swaps **increase** an interior
diagonal term by `O(n/log n)`, so pointwise diagonal maximality is false and
must not be used.  The increase remains lower order than the observed
`-Theta(n)` interior exponent.  At the full diagonal, every tested off-type
cycle decreased the weight.

A separate 100,000-sample random scan of diagonal subprofile vectors for
`n=10^5` and `10^6` found no positive nontrivial diagonal exponent.  These
finite computations motivated the geometric-mean transport comparison in
`DENSE_FOUR_TYPE_MATCHING.md`; they are diagnostics, not an asymptotic proof.
