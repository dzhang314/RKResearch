# Coordinate-trace certificates for algebraic Runge–Kutta tableaux

The reviewed rooted-tree verifier now has an integer coordinate version for algebraic coefficients. It preserves the reviewed HasOrder predicate and makes **no new stage-bound claim**. The exact positive and negative controls compile with Lean 4.36.0.

## Interface and soundness

The [Lean engine](../../lean/RKCert/ReviewedNative/CoordinateRootedTreeGram.lean) takes a finite integer multiplication table, an initial feature, integer branch matrices, and an integer output matrix for each order. The energy theorem is an equivalence: the integer trace at a grade is zero if and only if every reviewed tree of that grade has zero output coordinates. The dense and sparse evaluator forms are proved equal, so zero structure constants need not be used in the arithmetic replay.

To identify those tests with actual tableau order, the model supplies:
- An additive decoder of the augmented features into \(K^s\times K\), and an **injective** additive decoder of the integer output coordinates into \(K\).
- Compatibility of that decoder with the multiplication table, branch actions, initial feature, and output. These are model obligations, not properties asserted for arbitrary arrays.
- A commutative \(\mathbb Q\)-algebra \(K\), with units \(d,e\) and identities \(M=dA,\ \boldsymbol w=e\boldsymbol b\).

Thus an independent integral multiplication basis of a number field is suitable; neither an ordering of \(K\) nor a real embedding is needed. Injectivity is used to deduce failure from nonzero energy and obtain the equivalence. For any characteristic-zero field, nonzero integer normalization factors are units.

For a rooted tree \(t\), \(\boldsymbol\Phi_t(A)\) is its Butcher weight vector. The archived rational normalization multiplies \(\boldsymbol\Phi_t(M)\) by the forest factorial, and carries the extra scalar \(d^{|t|-1}\). Here an extra factor \(\sigma(t)\) scales this pair: a split of a tree of size \(n\) with right branch of size \(k\) contributes \(\binom{n-1}{k}\). The Lean normalization theorem verifies
\[
 \sigma(t)\cdot t! = n!,
\]
where \(t!\) is the *tree* factorial and \(n!\) is the ordinary size factorial. The branch acts by \(kM\) on the stages and \(d\) on the extra scalar. At order \(n\), the output applies \(n\boldsymbol w^{\mathsf T}\) and subtracts \(e\) times the extra scalar. The decoded value is the ordinary residual multiplied by \(n!e d^{n-1}\).

The covariance is a sum of outer products over the reviewed plane representatives. Bilinearity separates the two subtree choices. Applying the output to both axes and taking the ordinary coordinate trace gives a sum of nonnegative integer squares. This is not an algebraic field trace, and it does not square residuals in \(K\).

## Kernel-checked controls

The [quadratic models and certificates](../../lean/RKCert/ReviewedNative/CoordinateRootedTreeGramControls.lean) prove the multiplication and readout semantics against Mathlib's quadratic algebra with two independent integer coordinates.

| Case | Integer scale | Augmented dimension | Energies, starting at order 1 | Reviewed conclusion |
|---|---:|---:|---|---|
| Two-stage Gauss over \(\mathbb Q(\sqrt 3)\) | 12 | 5 | \(0,0,0,0,116955021312\) | Exact order four |
| Two-stage explicit control over \(\mathbb Q(i)\) | 30 | 5 | \(0,0,1458000000\) | Exact order two |

For the second control the two order-three residuals are \(-1/6\) and \(i/6\). The Lean theorem Imaginary.field_squares_cancel checks that both are nonzero yet their ordinary squares in the coefficient algebra sum to zero. A field-valued sum of squares would therefore silently accept the wrong order. The coordinate energy detects the failure.

## Independent dimension-29 replay

Run **python3 replay.py** for both controls. Pass the repository checkout path as its optional argument to include the **already-established** seven-stage order-six Laguerre–Gauss SDIRK construction. The standard-library replay reads the literal coefficients in LaguerreGauss76Data.lean without executing any Lean. It uses the basis \(1,\sqrt2,\sqrt{15},\sqrt{30}\), denominator \(418653415113746400\), and augmented dimension \(7\cdot4+1=29\). Energies are zero through order six and strictly positive at order seven. A separate raw plane-tree replay using integer Butcher weights and tree factorials agrees at every grade. This larger replay is exact arithmetic, **not** a new dimension-29 Lean check; its reviewed order already has the archived Lean proof.
