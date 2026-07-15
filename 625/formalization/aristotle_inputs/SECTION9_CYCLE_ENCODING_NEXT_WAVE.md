# Section IX cycle-encoding next wave

This note records the dependency boundary for the remaining weighted
cycle-to-walk argument in (9.17)--(9.18).  It is a proposal and scheduling
artifact, not an accepted Lean module.  The five isolated request projects
listed below are quarantined under the Git-ignored `.aristotle/pending-next/`
directory.  Each project is pinned to Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, contains exactly one intentional
target hole, and was locally elaborated against that revision.

No target below assumes a cycle-to-walk encoding, weight preservation, or an
aggregate cycle inequality.  The central combinatorial construction appears
explicitly as leaf L8.

## Dependency order

| ID | Target | Depends on | Exact role |
|---|---|---|---|
| L1 | endpoint-mass row-sum identity | finite sums only | Reconciles endpoint-resolved kernel powers with the existing scalar walk-mass recursion. |
| L2 | positive endpoint-kernel row bound | L1 | Proves `sum_w S(v,w) <= tau*(1-tau)^-1` for the finite positive-length kernel. |
| L3 | residual `q` degree-square summation | accepted pointwise endpoint estimate | Converts `q_ab <= kappa d_a^2 d'_b^2/m^2`, degree caps, and exact degree sums into both row and column bounds `<= kappa U^3/m`. |
| L4 | explicit path occurs in endpoint mass | endpoint kernel definition | Shows the product along one specified finite path is one nonnegative endpoint-kernel summand. |
| L5 | bounded positive path occurs in `S` | L4 | Uses `1 <= ell <= L` to select the `ell-1` term of the positive kernel. |
| L6 | explicit block-state chain occurs in row walk mass | scalar walk recursion | Shows one specified sequence of block states is one summand of the relaxed traversal mass. |
| L7 | minimal nonempty even set has a covering cycle walk | `IsSimpleBipartiteCycle` only | Constructs an actual `SimpleGraph.Walk.IsCycle`, proves exact edge coverage and length bounds. |
| L8 | exact marked mixed-cycle block code | L7 and matching uniqueness | Marks/orients one matching edge, cuts at every matching edge, proves all residual segments nonempty, reconstructs the original cycle, and proves no edge occurrence is duplicated. |
| L9 | block-code weight preservation | L8 | Uses exact reconstruction/injectivity to prove the product of residual segment weights equals `prod_{e in C\\M} q_e`. |
| L10 | canonical chosen code is injective | L8 | Chooses one code for each mixed cycle; exact reconstruction proves the chosen encoding injective, without any ordering assumption. |

The operator leaves L1--L6 and the combinatorial leaves L7--L10 are then
assembled into the two full bridge targets below.

## Locally checked isolated targets

### R1: endpoint-refined positive kernel (L1--L2)

- Project: `.aristotle/pending-next/R1-endpoint-positive-kernel`
- Source: `EndpointPositiveKernel/Main.lean`
- Target:

```lean
theorem finitePositiveWalkKernel_rowSum_le_geometric
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ v, ∑ w, K v w ≤ tau) (L : ℕ) :
    (∀ ell v,
        (∑ w, finiteKernelEndpointMass K ell v w) =
          finiteKernelWalkMass K ell v) ∧
      ∀ v, ∑ w, finitePositiveWalkKernel K L v w ≤
        tau * (1 - tau)⁻¹
```

### R2: covering cycle traversal (L7)

- Project: `.aristotle/pending-next/R2-minimal-even-cycle-tour`
- Source: `MinimalEvenCycleTour/Main.lean`
- Target:

```lean
theorem exists_covering_cycleWalk_of_minimal_even
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C : Finset (A × B)) (hC : IsSimpleBipartiteCycle C) :
    ∃ (v : A ⊕ B) (p : (cellGraph C).Walk v v),
      p.IsCycle ∧
      p.edges.toFinset = C.image cellSym2 ∧
      p.length = C.card ∧
      p.length ≤ Fintype.card (A ⊕ B)
```

### R3: exact mixed-cycle block code (L8)

- Project: `.aristotle/pending-next/R3-mixed-cycle-block-code`
- Source: `MixedCycleBlockCode/Main.lean`
- Target:

```lean
theorem exists_exact_mixedCycleBlockCode
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (C M : Finset (A × B))
    (hC : IsSimpleBipartiteCycle C)
    (hM : IsBipartiteMatching M)
    (hMeet : ¬ Disjoint C M) :
    ∃ code : MixedCycleBlockCode M,
      codeEdgeSet code = C ∧
      Function.Injective (codeResidualEdge code) ∧
      Function.Injective (codeMatchingEdge code) ∧
      (∀ i, (code.residual i).cells.length ≤ Fintype.card (A ⊕ B))
```

The `MixedCycleBlockCode` structure itself records the marked oriented edge,
all matching traversals, the nonempty residual walks, and cyclic endpoint
compatibility.  Thus this target does not conceal those obligations in a
hypothesis.

### R4: explicit path and chain terms (L4--L6)

- Project: `.aristotle/pending-next/R4-explicit-path-kernel-term`
- Source: `ExplicitPathKernelTerm/Main.lean`
- Target: `explicit_terms_le_kernel_masses`

Its three conjuncts prove respectively: an explicit path is an endpoint-mass
term; a positive path of length at most `L` is a term of `S`; and an explicit
state chain is a term of the scalar row walk mass.

### R5: actual degree algebra for `q` (L3)

- Project: `.aristotle/pending-next/R5-q-row-column-degree-bound`
- Source: `QRowColumnDegreeBound/Main.lean`
- Target:

```lean
theorem q_row_column_le_of_pointwise_degree_square
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (q : A → B → ℝ≥0∞)
    (U m : ℕ) (kappa : ℝ≥0∞)
    (hm : 0 < m)
    (hrowTotal : ∑ a, row a = m)
    (hcolTotal : ∑ b, col b = m)
    (hrowCap : ∀ a, row a ≤ U)
    (hcolCap : ∀ b, col b ≤ U)
    (hq : ∀ a b,
      q a b ≤
        kappa * (row a : ℝ≥0∞) ^ 2 * (col b : ℝ≥0∞) ^ 2 /
          (m : ℝ≥0∞) ^ 2) :
    (∀ a, ∑ b, q a b ≤ kappa * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) ∧
    (∀ b, ∑ a, q a b ≤ kappa * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞))
```

## Next small targets after R1--R5

L9 should state weight preservation for the concrete `MixedCycleBlockCode`:

```lean
theorem mixedCycleBlockCode_residualWeight_eq
    (q : A → B → ℝ≥0∞) (C M : Finset (A × B))
    (code : MixedCycleBlockCode M)
    (hreconstruct : codeEdgeSet code = C)
    (hResidualInj : Function.Injective (codeResidualEdge code))
    (hMatchingInj : Function.Injective (codeMatchingEdge code)) :
    codeResidualWeight q code = edgeWeightOutsideENN q M C
```

Here `codeResidualWeight` is the product over the dependent residual-edge
occurrence type and `edgeWeightOutsideENN` is the product over `C \ M`.
Membership in `M` for matching occurrences and avoidance of `M` for residual
segments are already fields of the code.

L10 should choose codes using L8 and derive injectivity solely from exact
reconstruction:

```lean
theorem exists_injective_mixedCycleEncoder
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    ∃ encode : MixedSimpleCycle M → MixedCycleBlockCode M,
      Function.Injective encode ∧
      ∀ C, codeEdgeSet (encode C) = C.1
```

`MixedSimpleCycle M` must be the subtype of the existing finite simple-cycle
family satisfying `¬ Disjoint C M`; it must not carry a pre-existing tour or
encoding certificate.

## Full bridge targets

### FB1: abstract mixed-cycle weighted enumeration

After L1--L10, prove the original assumption-free target:

```lean
theorem matchingCycle_weighted_walk_enumeration
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ℝ≥0∞) (M : Finset (A × B))
    (hM : IsBipartiteMatching M)
    (tau : ℝ≥0∞) (htau : tau < (1 / 3 : ℝ≥0∞))
    (hRow : ∀ a, ∑ b, q a b ≤ tau)
    (hColumn : ∀ b, ∑ a, q a b ≤ tau) :
    let b : ℝ≥0∞ := tau * (1 - tau)⁻¹
    b < 1 ∧
      (∑ C ∈ simpleCyclesMeeting A B M, edgeWeightOutsideENN q M C) ≤
        (((2 * M.card : ℕ) : ℝ≥0∞) * (b * (1 - b)⁻¹))
```

The one factor `2 * M.card` is the oriented marked start.  Later matching
traversals are accounted for by the existing norm-one partial-permutation
kernel, never by another free choice of a matching edge.

### FB2: literal residual-`q` specialization

Instantiate FB1 with
`residualQ M R row col`, using the accepted finite endpoint estimate, its
real-to-`ENNReal` identification, L3, and the positive endpoint kernel from
L1--L2.  The conclusion must use the literal `residualQ`, literal configuration
degrees, and the explicit value of `tau`; it must not quantify an abstract
kernel or assume the final attachment inequality.

## Submission order

Submit R1, R4, and R5 first because they are independent algebraic leaves.
Submit R2 in parallel.  Submit R3 independently as the main combinatorial
leaf; if it fails, split it only at the honest milestones "covering cycle
walk", "rotation to a selected oriented matching edge", and "cut/reconstruct".
After accepted local ports of those returns, package L9 and L10, then retry FB1
and finally FB2.
