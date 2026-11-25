# An explicit Runge–Kutta method of order sixteen requires at least 25 stages

The bound holds over every ordered field. It concerns the algebraic order conditions on a strictly lower triangular matrix and its output weights; the weights need not be positive.

[Stage padding](../../lean/RKCert/ReviewedNative/StagePadding.lean) reduces the claim to the impossibility of a 24-stage tableau. The [native head dispatch](../../lean/RKCert/ReviewedNative/ERKOrder16NativeHeadDispatch.lean) gives three exhaustive cases:

1. The strong chart is excluded by the [checked strong endpoint theorem](../../lean/RKCert/ReviewedNative/ERKOrder16StrongCenteredEndpoint.lean).
2. The five-site weak chart yields the actual scalar moment packet excluded in the [weak-five proof](weak-five-complete/PROOF.md).
3. The four-site weak chart pays both forward and reverse stopped moments on four distinct physical labels. The [weak-four proof](weak-four-complete/PROOF.md) rules out the cubic and quartic alternatives. For each possible order of the polynomial roots and labelled clocks, the two first-stop moments cannot both vanish throughout the certified parameter interval.

The last step uses the forward moments from the original tableau, not from a separate abstract three-test packet. The two new scalar exclusions are mathematical proofs with exact rational checkers; the resulting lower bound is not yet checked end to end in Lean.
