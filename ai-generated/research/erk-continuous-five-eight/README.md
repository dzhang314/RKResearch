# An exact eight-stage continuous order-five ingredient

This independently checks the eight-stage rational explicit
Owren–Zennaro matrix from the
[exact source implementation](https://github.com/SciML/OrdinaryDiffEq.jl/blob/cb87b90b628a5fe0edabcc38d6a37160a54c7e80/lib/OrdinaryDiffEqLowOrderRK/src/low_order_rk_tableaus.jl#L421-L460);
see also the [authors' paper](https://doi.org/10.1137/0913084).
The project contribution here is the exact rooted-profile decoder
and its residual shape, not a new claim about the underlying method.
No order-ten tableau follows from this ingredient alone.

The literal \(A\) and the independently computed \(5\)-by-\(8\)
decoder \(\Pi\) are in [prefix.json](prefix.json). For each of the
17 trees through size five, the audit checks
\[
 \Pi\boldsymbol{\Phi}_u(A)=|u|X^{|u|-1}/u!
\]
as a coefficient identity, and checks that the 17 profile rows
have rank eight, making that decoder unique. This directly checks
dense order five, without assuming the implementation's name
implies it. Integrating the decoder from zero to one gives exactly
the eighth stage row padded at its final zero coefficient. Its
stage profile is exact through rooted size six. This is literal
row equality, not merely equal row sums.

The size-six residuals
\(\rho_u=|u|X^{|u|-1}/u!-\Pi\boldsymbol{\Phi}_u(A)\)
span \(X(X-1)\mathcal P_3\) over \(\mathbb Q\). Size seven has
rank five and need not vanish at one. Rescaling all prefix
clocks by a nonzero \(\xi\) sends the size-six subspace to
\(X(X-\xi)\mathcal P_3\). The coefficient denominators of the
matrix and decoder both involve extra primes, so this fixed
ingredient is not asserted over the factorial localization.

    python3 -B audit.py
    sha256sum -c sha256.txt

Supply `--pinned-source /path/to/low_order_rk_tableaus.jl` to
also cross-check every matrix entry against the pinned primary
implementation. Both the source commit and the downloaded
byte hash are recorded in the fixture.
