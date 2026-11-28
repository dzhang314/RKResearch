# Canonical asymmetric half-at-9: the last width component is impossible

**Scope.** Continue the maximal two-carrier, genuinely distinct
nine-site, six-pair asymmetric chart with left extras $\{e,t\}$, right
extras $\{t,s\}$, and physical $c_8=z,c_9=h,c_{10}=s$, where $z$
is the dormant singleton. This excludes the exact bidegree-$(31,35)$
width component over characteristic zero. With the [small component](ERK11-NINE-SITE-ASYMMETRIC-H9-SMALL3-EXIT.md),
[degree-nine component](ERK11-NINE-SITE-ASYMMETRIC-H9-DEGREE9-EXIT.md),
and [zero affine](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-PIVOTS.md)
exclusions, it excludes this entire physical inner order and its
actual reflection. It does not exclude the distinct right-choosing
edge or the opposite central order.

## Three affine-independent equations

Use the exact normalized dormant polynomials $F,G,R,L,Q,S,M,K$
from those preceding notes. The affine slope is genuinely live
in characteristic zero, but it can vanish after reduction.
The following independent descriptions of the first contact and
dormant support do not use that affine slope.

Let $Y=\Delta t$, for the actual two-free-site Cramer data
$\Delta,\Sigma,\Pi,\Omega$. Its true quadratic is
$Y^2-\Sigma Y+\Delta\Pi=0$. Before using the affine formula, the
first inverse-Gram contact at physical rows 7 and 11 is
$g_1t+g_0=0$. Its left derivative row uses
$L_0=(a-e)(a-t), L_1=-et$, and the right derivative row uses
$$
 R_0=d^2\Delta-d\Sigma+\Pi,\qquad R_1=-\Delta+\Sigma-\Pi .
$$
Thus $g_1Y+\Delta g_0=0$ without a $g_1$ pivot. The
[actual dormant support](ERK11-NINE-SITE-ASYMMETRIC-DORMANT-SUPPORT.md)
gives $uY+v=0$, where
$$
 \begin{aligned}
 p&=I_2-hI_1,\quad q=hI_0-I_1,\\
 u&=-(z-e)(p+qz),\\
 v&=(z-e)(pz\Delta+qz\Sigma-q\Pi)-\Omega z(1-z)(z-a)(z-d).
 \end{aligned}
$$
These yield the first-contact norm, affine compatibility, and
support norm:
$$
 \Delta g_0^2+\Sigma g_0g_1+\Pi g_1^2=0,\quad
 g_1v-u\Delta g_0=0,\quad
 v^2+\Sigma uv+\Delta\Pi u^2=0 .
$$
The first cancels only the live $\Delta$ from the usual quadratic
norm. These are the same physical, affine-independent equations
used in the [dropout proof](ERK11-NINE-SITE-ASYMMETRIC-EDGE-H9-PIVOTS.md),
not additional mixed payment. The replay removes only their listed
live characteristic-zero factors.

## An integral-place contradiction with both widths controlled

Let $C_{31}$ be the irreducible bidegree-$(31,35)$ factor of the
marked width polynomial $W_{MG}$. Using primitive integral
representatives, both
$$
 R_a=\operatorname{Res}_b(C_{31},W_{MQ}),\qquad
 R_b=\operatorname{Res}_a(C_{31},W_{MQ})
$$
vanish at any actual widths. At the prime 103 their residue degrees
are 3874 and 3850. In each projection the verified integral
Sylvester scaling gives degree bound 3882. Reverse the matrix at
infinity: the exact constant pivot and row divisions give
nullities $(4,2,2)$ and $(16,16)$ respectively. Thus the actual
degrees are the residue degrees, with 103-adic leading units.
At the finite point $b=0$ the second matrix has successive
nullities $(4,4,4,4)$. Thus $b^{16}$ divides $R_b$ exactly. The
residue has order exactly 16, so $R_b/b^{16}$ has nonzero constant
residue. Use the actual $b\ne0$ to impose this quotient.

If a characteristic-zero solution exists, both widths are
algebraic by these nonzero univariate eliminants. Embed their joint
field into an algebraic closure of $\mathbb Q_{103}$. Both are
integral there due to the leading units; at negative valuation
the leading term could not cancel. Thus we can take finite
residues of both widths even if every $b$ pivot drops at a
particular $a$. The quotient $R_b/b^{16}$ also forces the residue
of $b$ to be nonzero.

The four residue projections into $a$ from $W_{MQ},W_{MF}$ and
the two raw $z$-resultants of $(G,Q)$ and $(G,F)$ have degrees
$3874,5054,5862,7460$. Their gcd has degree 419. The raw filters
retain the individual $z$ degrees after reduction, so reduce
actual characteristic-zero resultants even before integrality
of $z$ has been shown. No residue-only factor is divided away.
For every irreducible $a$ factor specialize $C_{31}$,
$W_{MQ},W_{MF},W_{MS}$, the raw width resultants, and
$R_b/b^{16}$. Check every factor of the resulting $b$ gcd,
including one quadratic over a prime-field $a$.

At all twenty retained residue width pairs the actual dormant
polynomial $G$ retains degree five in $z$. Thus $z$ is algebraic;
after extending the embedding its leading unit forces $z$
integral. The gcd of the actual reduced $z$ equations, including
the three affine-independent ones, is the unit in each field.
This contradicts existence over the algebraic closure of the
residue field. There is no ignored finite-degree drop, unbounded
width at the selected place, or assumed live residue guard.

Run the standalone Python replay with SymPy, python-flint, NumPy
and SciPy. SciPy proposes integral Sylvester scalings; the receipt
checks them and the row operations exactly. This is a mathematical
tableau proof plus a standalone exact arithmetic replay, not a
full native Lean proof.

The [standalone exact source and independent replay log](erk11-nine-site-asymmetric-edge-h9-exit/) are included.
