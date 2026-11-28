# Sixteen-stage exact ERK10 at primes 11, 13, 19 and 23

Four additional literal strictly explicit tableaux attain exact
order ten in sixteen stages. Their coefficient fields are
\(\mathbb F_{11},\mathbb F_{13},\mathbb F_{19},\mathbb F_{23}\).
These tableaux are separate from the
[prime-17 witness and Lean certificate](../erk10-sixteen-f17/README.md).
There is no assertion of minimality, a rational full tableau,
or one tableau over the factorial localization.

Each of these four witnesses lifts compatibly to **every**
power of its prime, by the explicit guarded pressure equations
below. In particular, for each listed prime \(p\), sixteen
stages suffice over any nontrivial commutative ring in which
\(p\) is nilpotent, and over \(\mathbb Z_p\) and \(\mathbb Q_p\).
The lift proof is mathematical and has independent literal
replays; the four new prime-field and prime-power results
are not asserted as Lean theorems.

Together with the [17-power witness](../erk10-sixteen-17-power-lift/README.md),
they give sixteen stages over **every nontrivial ring where
some positive integer supported on \(\{11,13,17,19,23\}\)
annihilates 1**. Indeed apply the integer Chinese remainder
theorem to the per-prime-power tableaux and then map the
combined coefficients into the target ring. The single
eleven-bush normalized defect is a unit on every
component, hence remains a unit in the target. This is
not a stage bound over rings of arbitrary finite
characteristic.

## Literal sources and guarded lift

| Prime \(p\) | Base literal | Exact eleven-bush defect mod \(p\) | Pressure Jacobian determinant mod \(p\) |
| --- | --- | ---: | ---: |
| 11 | [f11.json](f11.json) | 10 | 5 |
| 13 | [f13.json](f13.json) | 5 | 9 |
| 19 | [f19.json](f19.json) | 11 | 3 |
| 23 | [f23.json](f23.json) | 15 | 9 |

All four use the **same**
[paid rational doubled-clock dense prefix](../erk10-canonical-dense-rank3/rational-prefix.json).
Its canonical pure endpoint is \(\theta=5/2\); its size-six
residuals lie in the three recorded rows with paid coefficients.
Use the raw cofactor with \(\boldsymbol U\) killing
\(X,\ldots,X^7\), \(\boldsymbol G,\boldsymbol H\) in the
span of \(\boldsymbol U,\boldsymbol x\odot\boldsymbol U\),
and terminal responses \(\boldsymbol k\), \(K(\boldsymbol x\odot\boldsymbol U)\)
annihilating the three rescaled source tests. The actual
physical merger is the same fully equal first high row
and pure prefix endpoint as in the prime-17 proof.

The input parameter order is \(\theta,x_1,\ldots,x_8\);
\(x_0=1\) is the separate reverse origin, and \(x_8\) is
the merged forward endpoint. Only \((\theta,x_3,x_5)\)
vary. The first pressure equation is now \(2\theta-5=0\).
The second is the fourth reverse read's discrepancy on
the third nonorigin row. The third is the residual in
the sole unselected terminal equation. The five solved
terminal taps, in order, are
\((5,4),(6,4),(6,5),(7,4),(7,5)\).
All other extra taps are zero.

The six terminal rows are ordered as the three tests on
\(\boldsymbol k\) followed by those on \(K(\boldsymbol x\odot\boldsymbol U)\).
The nonsingular five row choices are
\((0,1,2,3,5)\) for 11 and 13, and \((0,1,2,3,4)\) for 19
and 23. The initial node differences, all Gaussian pivot
residues including row swaps, and the full three-dimensional
Jacobians are in [lift-audit.txt](lift-audit.txt).
The mass at \(x=9\) is **zero** in the base F11 rule, but
only the first raw three masses and the checked matrices
must be units; no division by the mass at \(x=9\) occurs.

Vanishing pressures and the paid source subspace give the
ordinary rooted conditions by the
[marked source proof](../erk10-sixteen-17-power-lift/README.md#why-the-equations-imply-the-ordinary-order-conditions)
which uses no positivity or invertibility of the later masses.
The unit Jacobians, checked by exact finite differences
modulo \(p^2\), then give the same Newton step for
every exponent. All denominators stay units in the same
residue class, and the lifted bush defects keep the
nonzero base residues in the table.

## Reproduction

    python3 -B audit.py
    python3 -B build.py
    python3 -B verify_lifts.py
    sha256sum -c literal-sha256.txt
    sha256sum -c source-sha256.txt

The first script checks the four untouched base literals
against all 1,205 ordinary rooted conditions and their
next-order failures. The builder exactly regenerates the
base literals and the displayed prime-square and prime-cube
literals. The last script replays the higher-power literals
independently of the construction, verifying every rooted
condition, compatible reduction, and the unit defects.
