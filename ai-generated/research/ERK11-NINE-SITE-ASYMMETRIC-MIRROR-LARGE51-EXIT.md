# Mirrored variable edge: exclude the final large width component

**Scope.** Continue the distinct nine-site
[mirrored variable edge](ERK11-NINE-SITE-ASYMMETRIC-MIRRORED-FINITE.md):
left extras $\{t,s\}$, right extras $\{h,t\}$, with genuine dormant
at physical 8 followed by $e,s$. The affine slope is live and
the mixed determinant is nonzero by the preceding rank-drop exits.
The [paid compatibility split](ERK11-NINE-SITE-ASYMMETRIC-MIRROR-SMALL9-EXIT.md)
left one irreducible width component of bidegree $(51,54)$ in $(b,a)$.
This rules out that entire component over characteristic zero.
Together with those preceding exits, it excludes this physical
inner order and its actual reflection.

## The width equations and a slope-free port norm

Use the previously verified $D,K$ compatibility polynomials,
their width component $C_{51}$, and the exact normalized
width polynomials $W_{DQ},W_{DE}$ from the previous split.
The inputs use only the physical row-8 dormant contact, degree-five
mixed inverse Gram, actual right projected mark at physical 9,
and shifted ordinary quadrature.

There is also an actual left dormant-contact equation before
using the affine slope. In the genuine two-site shifted Cramer
data $\Delta,\Sigma,\Pi$ put $Y=\Delta t$ for the shared extra.
The true quadratic is $Y^2-\Sigma Y+\Delta\Pi=0$. The right
derivative row is, up to its live scale,
$$
 R_0=(h-d)(Y-d\Delta),\qquad
 R_1=-(1-h)(\Delta-Y).
$$
Thus the dormant port
$R_0K_0(z)+R_1K_1(z)=uY+v=0$ gives the normalized
quadratic norm of $v^2+\Sigma uv+\Delta\Pi u^2=0$.
Call this polynomial $N_{\mathrm{port}}$. This uses the
same physical port as the affine-dropout proof, regardless
of whether the affine coefficients survive reduction.
Neither a direct half mark at physical 10 nor a reverse
ordinary order-eleven square is used.

## Exact leading-unit and residue exit

Use primitive integral representatives for $C_{51},W_{DQ}$.
The two projections
$$
 R_a=\operatorname{Res}_b(C_{51},W_{DQ}),\qquad
 R_b=\operatorname{Res}_a(C_{51},W_{DQ})
$$
vanish at every actual width pair. Their degrees modulo 103
are 7620 and 7609. The integer-scaled Sylvester matrices
give exact degree upper bound 7656 in both directions.
After reversal at infinity the verified row eliminations give
successive nullities
$$
 (12,12,4,4,4)\quad\hbox{and}\quad (23,23,1).
$$
Thus the exact degrees match the modular degrees and both
leading coefficients are 103-adic units. Both widths are
algebraic and integral at any embedding of their joint field
into an algebraic closure of $\mathbb Q_{103}$: a negative
valuation would make the leading term of the relevant equation
the unique term of smallest valuation.

Use three auxiliary residue width polynomials, the raw
$z$-resultants of $D$ with the actual first contact $F$, the
actual dormant weighted right port $P$, and $N_{\mathrm{port}}$.
For these three computations the individual generic $z$
degrees of the integral inputs are retained modulo 103.
Their residues therefore come from true integral resultants;
there is no dependence on $z$ already being integral or on
a residue affine pivot. Their further $b$-projections with
the reduction of $C_{51}$ have residue $a$-degrees
12624, 12189, 13914. Starting from the reduction of $R_a$,
the running gcd degrees are 25, 3, 1, with final gcd exactly
$a-1$ up to a unit.

Now specialize those three raw width equations, $C_{51}$,
$W_{DQ},W_{DE}$, and the **unmodified** reduction of $R_b$
at the only possible residue $a=1$. Their common $b$ gcd is
the unit. In particular one does not remove an accidental
$b^2$ factor from the reduction of $R_b$ or discard any
possible width simply for coinciding with a forbidden
clock after reduction. Since both widths are already
proved integral, that unit gcd is a contradiction over the
algebraic closure of the residue field.

The standalone Python replay checks the exact leading bounds
and all finite-field arithmetic. It uses SymPy, python-flint,
NumPy and SciPy; SciPy only proposes integer scalings which
are verified exactly. The complete mixed-tableau and
finite-place arguments are mathematical rather than a fully
native Lean proof.

The [standalone exact files and independent replay](erk11-nine-site-asymmetric-mirror-large51-exit/) are included. The independent replay verifies the unmodified residue equations.
