# Paid RK clock profiles and the exact cost of nuisance masking

Work over a field $K$. Take the [weighted residue functionals](README.md)
$\Lambda_Q,\Lambda_D$ for monic hulls $Q,D$ of positive, not necessarily
equal, degrees. Assume $P$ is invertible modulo $QD$ and
$Q+PR=\sigma D$. For $J\in\{Q,D\}$, take $P^{-1}$ modulo $J$ and set
$$
\Lambda_J(F)\coloneqq[X^{\deg J-1}]\operatorname{rem}_J(P^{-1}F).
$$
The [all-degree identity](COMMUTATIVE-RINGS.md) gives
$$
\Lambda_D(F)-\sigma\Lambda_Q(F)=-[X^{-1}]\,FR/(QD),
$$
with the coefficient taken at infinity.

## Actual payment and the fitted profile

Suppose the actual tableau satisfies
[RKResearch.HasOrder](../../../RKResearch/OrderConditions.lean) $p\,A\,b$.
Write $c=A\mathbf1$. Let $v$ belong to
[`zeroSpace`](../../lean/RKCert/ReviewedNative/GradedDefects.lean) $A\,g$,
the span of differences of equal-order normalized elementary columns of
orders at most $g+1$. Set
$$
\mu_v(F)\coloneqq\sum_i b_i v_i F(c_i).
$$
The reviewed `probe_zeroSpace` lemma gives $\mu_v(F)=0$ for every
$F$ with $g+\deg F+1\le p$: expand in monomials and apply the literal
rooted-tree payment to each. No assumption about the signs or nonvanishing
of the individual $b_i$ is needed.

The separate hypothesis is a **verified equality of actual functionals**:
for some gain $\theta\ne0$ and a finite set $Z$ of nuisance sites,
$$
\mu_v(F)=\theta\bigl(\Lambda_D(F)-\sigma\Lambda_Q(F)\bigr)
           +\sum_{z\in Z}\rho_z F(z).
$$
The nuisance weights $\rho_z$ may be unknown. The fit includes the gain
ratio across the two grids and the assertion that there is no other
unaccounted-for mass. In particular, masks on stages cannot be declared
members of `zeroSpace` just because their support has the desired shape.

## Exact masking cost and converse

Define
$$
T\coloneqq QD,\qquad
N\coloneqq\deg T,\qquad
H\coloneqq\prod_{z\in Z}(X-z),\qquad
h\coloneqq\deg H,\qquad
R_Z\coloneqq\operatorname{rem}_{T}(HR).
$$
Every probe vanishing on $Z$ is $H G$ for a polynomial $G$. The fit and the
error identity give
$$
\mu_v(HG)=-\theta[X^{-1}]\,G R_Z/T.
$$
The polynomial quotient from replacing $HR$ by its remainder contributes
no negative power. If $R_Z=0$, no masked probe detects the fitted term.
Otherwise define
$$
k_*\coloneqq N-\deg R_Z-1,\qquad F_*\coloneqq H X^{k_*}.
$$
Here $k_*\ge0$ because $R_Z$ is a nonzero remainder, and
$\deg F_*=h+k_*$. If $\deg G<k_*$ the Laurent expansion has highest power
at most $X^{-2}$; for $G=X^{k_*}$ its $X^{-1}$ coefficient is exactly
$\operatorname{lc}(R_Z)$. Thus $F_*$ is a least-degree masked witness,
with $\mu_v(F_*)=-\theta\operatorname{lc}(R_Z)\ne0$. The verified profile
is impossible if $g+h+k_*+1\le p$.

For comparison, let
$$
R_0\coloneqq\operatorname{rem}_{T}R .
$$
If $R_0\ne0$, the unmasked first degree is
$$
m\coloneqq N-\deg R_0-1 .
$$
If $h\le m$, then $R_Z=H R_0$ because $\deg(H R_0)\le N-1$.
Hence $k_*=m-h$, and $F_*$ still costs degree $m$: up to $m$ distinct
nuisance sites can be erased without increasing the probe degree.

**Converse for unrestricted nuisance weights.** Fix a degree budget
$\ell\ge0$. Evaluation at $Z$ on polynomials of degree at most $\ell$
has as kernel those divisible by $H$. The fitted
functional can be canceled throughout that space by some choice of
$\rho_z$ if and only if it vanishes on this kernel. For sufficiency it
factors through the image of evaluation; negate that functional and
extend it linearly to $K^Z$. Thus cancellation is possible precisely
below degree $h+k_*$ when $R_Z\ne0$, and in every degree when $R_Z=0$.
This is a converse about scalar moments, not about realizing the nuisance
weights by a tableau.

## How to check the physical fit

For simple grids, the template at $u$ is the sum of the applicable
weights $1/(P(u)D'(u))$ and $-\sigma/(P(u)Q'(u))$. Compare $\theta$
times this template with the actual coalesced mass
$\sum_{i:c_i=u} b_i v_i$ at every distinct physical or fitted clock
outside $Z$. Equivalently, multiply the difference by $H(u)$ and test
the powers $1,X,\ldots,X^{s-1}$ on those $s$ distinct labels; their
Vandermonde matrix is invertible. For an unknown $v$, a basis of
`zeroSpace` $A\,g$ gives a finite column-span check: coalesce each basis
column against the actual $b$ and restrict outside $Z$. A nonzero gain
can be scaled to $1$. These are finite checks on an actual tableau, not
new consequences of the already paid global zeros.

A useful separate check on a simple grid with $n$ sites is that its mass
is proportional to $1/(P(u)H_{\mathrm{grid}}'(u))$ exactly when its
$P$-tilted moments through degree $n-2$ vanish. The Vandermonde kernel
is one-dimensional, with the barycentric vector as a basis. This can
be proved from paid probes **if those probes really isolate that grid**.
A polynomial selector that erases other sites costs its degree and
also contributes its own factor to the tilt. The two proportionality
constants and their required relation must still be verified.

Repeated physical stages at one clock give one point evaluation, not
derivatives. For a confluent fit, reduce its proper fraction $R_0/T$.
An uncanceled pole of order $j>1$ at $u$ contributes a Hasse jet since
$[X^{-1}]F/(X-u)^j=[t^{j-1}]F(u+t)$; it cannot be absorbed into any
coalesced point mass. The actual point-evaluation fit is therefore
checked by requiring all such higher-order terms to cancel and comparing
the surviving simple-pole coefficients. Physical nuisance sites enter
$H$ once each. If genuine, unrestricted nuisance Hasse jets of orders
$0$ through $r_z-1$ are supplied at each $z$ instead, their kernel uses
multiplicity $r_z$ for $(X-z)$ and the same
masking proof applies. Repetition of RK stages does not supply those jets.

This argument uses neither triangularity nor a common diagonal. An ERK
or SDIRK application requires a proof that its particular tableau model
produces the stated actual defect and two-grid fit. It gives no
unconditional stage bound or order-specific exclusion.
