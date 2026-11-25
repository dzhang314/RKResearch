# An order-thirteen explicit method requires at least twenty stages

Let $K$ be a field of characteristic zero. A strictly lower triangular $s\times s$ matrix $A$ and weights $\mathbf b$ over $K$ cannot satisfy the reviewed Runge–Kutta order conditions through order thirteen unless $s\ge20$. The proof below joins the mathematical branch arguments to the already checked Lean results. It is not an end-to-end Lean certificate.

The [checked initial bound](../../lean/RKCert/ReviewedNative/ERK13NativePaidFrame.lean) gives $s\ge19$. Thus it suffices to rule out a tableau of width nineteen. Write $\boldsymbol\ell$ for the coordinate vector of the last stage and $E_7$ for the span of the Butcher weight vectors of trees of order at most eight, called `treeSpace A 7` in the proof. The vector used to split the proof is the first reflected seed,
$$
\mathbf r_0\coloneqq A^{\mathsf T}\mathbf b-\mathbf b\odot(\mathbf 1-A\mathbf 1).
$$
The three branches are exhaustive:

1. If $\mathbf r_0
e\mathbf 0$, [the checked ordinary theorem](../../lean/RKCert/ReviewedNative/ERK13OrdinaryWidth19.lean) rules out width nineteen.
2. If $\mathbf r_0=\mathbf 0$ and $\boldsymbol\ell\in E_7$, [the early marked proof](early-marked/README.md) rules out width nineteen over $K$. The proof splits by the paid first polynomial degree, uses reproducible modular checks to dispatch the low-degree factor alternatives, and excludes the remaining physical class configuration by the final-three argument.
3. If $\mathbf r_0=\mathbf 0$ and $\boldsymbol\ell\notin E_7$, [the late marked proof](late-marked/README.md) rules out width nineteen over $K$. The marked chart retains the actual final coordinate even if it is absent from the unmarked grade-ten space. Its physical fold gives the three reflected equations for the same final-three argument.

In the marked cases, the generic exclusion is now [independently kernel-replayed in Lean](../../lean/RKCert/ReviewedNative/NativeFinalThreeCausal.lean). It works on a strictly causal finite matrix and uses its last three supported class rows, not the last three raw tableau stages. The last two rows determine the affine transpose profile and the normalized weighted responses; the third must share a response and a clock with a later row, contrary to the distinct-ratio property established by the branch proofs. The full interface allows a weighted row to lie outside the support of the annihilator; the extra two moments exclude such a row from the final three.

The [marked rank staircase](../../lean/RKCert/ReviewedNative/ERK13NativeMarkedStaircase.lean), final-three leaf, and ordinary branch are Lean-checked. The marked chart producers, their physical folded-row adapters and the modular certificates are not yet composed into a Lean proof of the final inequality. No comparison of real signs or positivity of the weights enters the twenty-stage lower bound.
