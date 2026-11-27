# Directed and exact finite replay

Use Python 3. No network, symbolic package, or nonstandard library is required.

    sha256sum -c sources.sha256
    python3 -B cert.py --emit /tmp/erk149-seven-clock-fixture.json
    cmp fixture.json /tmp/erk149-seven-clock-fixture.json
    python3 -B check_core_boxes.py
    lean ../../../lean/RKCert/Research/ERK149SevenClockBracket.lean

The checker verifies the exact rational prefix values and three full-row merge identities, and expands the three cleared scalar quadrature identities over rational polynomials. All interval operations use outward integer rounding at 272 dyadic bits. The cubic root enclosures are disjoint and uniformly simple, and the directly evaluated compatibility function has strict signs (roughly \(-1.18\times10^{-38}\) and \(+3.12\times10^{-38}\)) at the two rational endpoints. Its derivative is strictly positive near \(0.00430053\). The replay verifies positive weights, strictness of all 14 literal rows, pairwise row distinction, and all 486 independent interval evaluations through size nine. All interval absolute bounds lie below \(1.22\times10^{-16}\); equality is provided by the exact proof, not by this numerical enclosure. The tenth tall defect is enclosed in \((-4,-3)\).

The fixture records closed lower and upper integer bounds for each strict tap and output weight, divided by \(2^{272}\). Its entries are enclosures around the actual algebraic tableau, **not** a rational coefficient table claimed to have order nine. The exact coefficients are specified by the unique bracketed scalar solution and the literal array formulas.
