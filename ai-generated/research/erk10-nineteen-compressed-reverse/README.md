# Universal order ten in nineteen explicit stages

The [literal tableau](tableau.json) is strictly explicit, has 19
distinct physical stages, and has **exact order ten over
\(\mathbb Z[1/210]\)**. It therefore works over any nontrivial
commutative ring where \(10!\) is a unit. This improves the
previous general-ring upper bounds
[21](../erk-ten-moment-splice/README.md) and
[20](../erk10-twenty-compressed-reverse/README.md).
It is an upper bound, not a claim of minimality.

Its common denominator is
\(2371261713408000=2^{13}3^9 5^3 7^6\), dividing \((10!)^6\).
Let \(s\) be the six-vertex bush, \(u=[s]\), \(v=[\bullet,u]\),
and \(t=[\bullet,v]\), with brackets listing the child trees of
a new root. Then \(|t|=11\), its tree factorial is
\(11\cdot9\cdot7\cdot6=4158\), its raw output is \(1/2688\),
and its factorial-scaled defect from one is \(35/64\).
That defect is a unit over the same coefficient ring. The two
simpler eleventh-order discrepancies serialized in the tableau
also have coprime numerators, but are not needed for exactness.

## What changed

Keep the entire raw weighted reverse construction of the
[twenty-stage method](../erk10-twenty-compressed-reverse/README.md).
Replace its older ten-row seed by the previously certified
[nine-stage universal ERK7 tableau](../erk-seven-factorial/README.md).
Append its actual endpoint, giving ten opening rows. Build
the same degree-four decoder \(\Pi\) from the five actual
readouts \(E_0,E_1,I_1,I_1^x,I_1^{x^2}\), now using the new seed
weights and its row-sum clocks in the three moment rows.

The earlier proof uses only the ordinary order-seven conditions
of this seed and its actual endpoint. In particular all
\(\rho_t=g_t-\Pi\boldsymbol\Phi_t(A_{\rm old})\) vanish through
size five. At sizes six, seven and eight the endpoint values
are zero. At size six the integral and first moment are zero,
and at size seven the integral is zero. The reduction uses
attachment of root leaves, and the endpoint's primitive of
each preceding derivative profile. These exact properties are
unchanged by replacing the seed. Hence the weighted reverse
payments (including the divided half-mass and the terminal
three-action payment on the same two source polynomials) are
unchanged. Only the cross block \((EJ-BE)\Pi\) changes.

As before, the final reverse clock-one label corresponds to a
forward row identical to the literal opening endpoint. The
two rows merge with their weights transferred, so the physical
count is \(10+10-1=19\).

## Exact replay

The constructor regenerates every literal coefficient. A separate
integer evaluator reads the literal matrix and weights, checks
all 1,205 non-plane ordinary rooted equations through order
ten, and checks the single unit eleven-vertex defect described
above. Float computations are not used.

    python3 -B audit_tableau.py
    python3 -B build19short.py /tmp/erk10-nineteen-rebuilt.json
    cmp tableau.json /tmp/erk10-nineteen-rebuilt.json
    sha256sum -c arithmetic-sha256.txt
