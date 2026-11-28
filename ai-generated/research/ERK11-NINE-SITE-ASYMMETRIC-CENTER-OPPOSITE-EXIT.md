# Asymmetric opposite central order: complete exact exclusion

**Scope.** Continue the genuine nine-site six-pair chart of the
[asymmetric central atlas](ERK11-NINE-SITE-ASYMMETRIC-CENTER-ATLAS.md),
with four distinct calibrations, left extras $\{e,t\}$, right extras
$\{t,s\}$, and $s,z,h$ at physical 8,9,10, with genuine dormant $z$.
The live affine slope $S_D$ was separately earned there. This excludes
the entire opposite central order and its actual reflection over
characteristic zero after these tableau premises. Together with the
matched and zero-affine exits in the atlas, it rules out the asymmetric
central location. No claim about other carrier counts or an ordinary
stage lower bound follows from this alone.

## Exact projection

Use the six true width conditions from the preceding atlas:
$Q_G,R_{LR},R_{LG},R_{RG},Q_L,Q_R$. Take the exact
$b$-resultants of $Q_G$ against $R_{LR}$ and $R_{LG}$, using
primitive integral representatives. Their degrees in $a$ are 3808
and 3812. The common gcd, up to units, is
$$
 a^{456}(a-2)^{138} F_{132}^2
 (14a^2-12a+3)^8(12a^2-9a+2)^8 F_{15}^{42}F_6^{42}.
$$
The subscripted polynomials are the exact irreducible rational
factors of the indicated degrees. The replay recomputes the
integer resultants by 318 degree-preserving prime residues: the
explicit factorial-times-coefficient-norm Sylvester bound and
a CRT product greater than twice that bound give exact integer
coefficients. The factor checkpoint retains the full coefficient
lists. Both $a=0$ and $a=2$ are actual calibration violations;
at $a=2$ the left half clock is the forbidden active endpoint.

## Complete finite-width lifts

For a remaining irreducible $F_d$, work over
$\mathbb Q[a]/F_d$. Choose a prime above 107 at which one exact
specialized $b$-degree is retained and the appropriate residual
gcd is a unit. One good place suffices, because any algebraic
common $b$ root would extend the chosen embedding to the algebraic
closure of $\mathbb Q_{107}$. A unit leading coefficient forces
that root integral; reduction would give a common root in the
algebraic closure of the residue field. We use actual specialized
characteristic-zero degrees, not the generic widths: the two
quadratic factors do undergo degree drops.

For $F_{132}$ a degree-one subresultant of the unshifted
three-site Hankel determinant $\Omega$ and the shifted two-site
pivot $D_2$ supplies a root $b_0=-\eta/\lambda$.
The exact checks in $\mathbb Q[a]/F_{132}$ are
$D_2(b_0)=D_0(b_0)=(D_2-D_1+D_0)(b_0)=0$, and hence
$D_i(b_0)=0$ for $i=0,1,2$. Here $D_2,D_1,D_0$
are the signed Cramer data of the actual $t,z$ pair after the
third site $s=S_N/S_D$ has been removed. The actual $D_2$ is
live, so this root is forbidden.

To check that we may divide all six width polynomials by
$b-b_0$, write the unreduced first contact as
$g_0+g_1t+g_2t^2$. Its reduced coefficients are
$U_G=D_2g_1+D_1g_2$ and $V_G=D_2g_0-D_0g_2$.
The two marked rows have constants $V_L,V_R$ in the ideal of
$D_2,D_1,D_0$. All raw compatibilities and both marked norms
therefore vanish at $b_0$. The only other normalization besides
powers of $a,b$ is one exact $D_2$ factor in $Q_G$. Its
cleared quotient is exactly
$$
 \frac{D_2V_G^2+D_1U_GV_G+D_0U_G^2}{D_2}
   =V_G^2+U_G(D_1g_0+D_0g_1),
$$
because $D_1V_G+D_0U_G=D_2(D_1g_0+D_0g_1)$.
The right side vanishes at $b_0$ regardless of the multiplicity
of $D_2$. Thus the exact forbidden linear factor really divides
every normalized polynomial. No large homogeneous width
evaluation is needed.

For $F_{15}$ and $F_6$, the degree-one subresultant of
$S_D,S_N$ similarly supplies a forbidden width $b_0$ with
$S_D(b_0)=S_N(b_0)=0$, checked exactly. At this root all
$D_i$ have multiplicity at least two. Before the two-node
reduction, the first contact has order at least one, the
left mark at least two, and right mark at least three:
the right derivative row is linear in the affine coefficients,
and the right kernel mark is homogeneous cubic in them.
Thus the linear reduced coefficients satisfy
$$
 \operatorname{ord}(U_G,V_G)\ge3,\quad
 \operatorname{ord}U_L\ge2,\quad \operatorname{ord}V_L\ge4,\quad
 \operatorname{ord}U_R\ge3,\quad \operatorname{ord}V_R\ge5 .
$$
The three raw compatibilities and both marked norms vanish to
order at least six, and the displayed quotient identity likewise
gives order at least six for normalized $Q_G$. The replay
checks that outside this one $D_2$ removal only calibration
monomials $a,b$ were removed, and that $a$ and $b_0$ are units at
the selected place. Therefore the sixth powers of $b-b_0$ are
exact common divisors, not modular-only factors.

After those exact forbidden-factor divisions, the residue gcd
is the unit at 107, in an $F_{132}$ residue field of degree 15,
an $F_{15}$ residue field of degree 15, and an $F_6$ residue
field of degree one. For both quadratic fields a degree-one
place at 107 gives unit gcd directly, with no factor division.
For each retained factor at least one actual specialized
leading coefficient is a unit. Thus no finite actual $b$
lies above any remaining $a$.

## Replay

The default standalone Python replay recomputes the exact CRT
projections and their gcd (the long part), confirms the complete
factor checkpoint, and checks the local lifts. The optional flag
--fiber-only uses the archived exact projection checkpoint and
replays all remaining exact guards and local lifts. Dependencies:
SymPy and python-flint. This is an exact arithmetic replay plus
a mathematical tableau and finite-place proof, not a full native
Lean theorem. The earlier scalar Lean identities are unchanged.

The [standalone exact files and independent replay](erk11-nine-site-asymmetric-center-opposite-exit/) are included. The independent fibre replay uses the checked exact width checkpoint.
