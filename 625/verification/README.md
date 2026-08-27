# Independent finite checks

This directory contains three independently runnable Python checkers and a
recorded output file. They test exact finite identities, small instances, the
partial-diagonal rational certificate used in the manuscript, and a stronger
auxiliary entropy certificate.

Run it from the repository root with Python 3.9 or newer:

```text
python 625/verification/erdos625_independent_checks.py
python 625/verification/check_partial_diagonal_rate_v3.py
python 625/verification/check_constant_ledger_v3.py
```

Do not use Python's `-O` or `-OO` flags: assertions implement seven checks in
the finite checker. All three scripts use only the standard library. The two
ledger scripts use exact `Fraction` arithmetic. In the finite checker, four
groups use exact integer or `Fraction` arithmetic and one transport group uses
floating-point square roots with tolerance `1e-11`.

The final theorem does not depend on the stronger constant ledger: its stated
constant follows directly from the uniform entropy gap proved in the
manuscript. These finite diagnostics are supporting tests. They are not an
asymptotic proof, peer review, or a substitute for the Lean formalization in
`../formalization/`.
