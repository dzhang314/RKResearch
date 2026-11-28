# DIRK12/15: no repeated terminal clock in the nine-site early-return chart

Consider the real ordinary fifteen-stage order-twelve \(C(2),f_5=3\) frame with weighted-invisible forward cubic, exactly four distinct genuinely cubic-dirty ghosts, and the [actual nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md). The sole repeated pair among nonterminal live nodes is already at the nonzero reflected \(d\)-site in the early reverse prefix.

Assume the literal ordinary terminal clock \(1\) occurs at some other live row. It must occur at one of the first five distinct nonzero ordinary live clocks \(a,b,c,e,f\): the remaining three distinct live labels apart from the ordinary origin are \(1-d,1-v,1-u\) with \(d,v,u\ne0\). The first three cases are [excluded independently](../dirk12-fifteen-rank3-invisible-nine-site-early-repeated-endpoint/README.md); the fifth case \(w=1-f=0\) has separate [first-root](../dirk12-fifteen-rank3-invisible-nine-site-first-root-zero-exclusion/README.md) and [nonroot](../dirk12-fifteen-rank3-invisible-nine-site-nonroot-zero-exclusion/README.md) exclusions. We give the remaining exact **\(e=1\)** proof in both ordinary Legendre branches. Thus the nine-site early return cannot have any repeated literal terminal clock.

This does **not** exclude the nine-site early return with unique terminal, the delayed return, or the ten-site earliest-extra-zero chart. The real DIRK12 stage interval remains **15–16**.

## True fourth endpoint gates and normalization

The [fourth-diagonal theorem](../dirk12-fifteen-rank3-invisible-nonzero-fourth-exclusion/README.md) forces actual \(A_{ee}=0\). Put \(T=X/a,\ x=b/a,\ y=c/a,\ t=e/a=1/a\), and
\[
  P_0=T(T-1)(T-x)(T-y),\qquad L=L_6',\qquad D=2xy-x-3y^2+2y .
\]
Here \(a\ne0,1\), \(x\ne0,1,t\), \(y\ne0,1,x,t\), and \(D\ne0\) by the literal source hypotheses. The actual ordinary live-only reads of \(P_0,TP_0\) at \(t\) are zero: every earlier live input vanishes and \(t\)'s own tap is zero. The two scalar polynomials \(\mathcal A(P_0),\mathcal A(TP_0)\) are known from the three previous physical reads and the paid two-mode formula. Each is divisible by monic \(P_0\). Later replays evaluate the exact two quotient expressions at the known \(t\), not a guessed stage relation.

Use \(J\) for integration from zero in \(T\), and \(I_i=J(T^iP_0)(1)\). At a first nonroot put \(D_i=J(T^iP_0)(x)-\rho I_i\), \(\rho=x^4(2x^2-6x+5)/(2x-1)\). Solving the two true fourth equations for the \(R(t)\) mode gives
\[
  R(t)(I_0D_1-I_1D_0)=JP_0(t)D_1-J(TP_0)(t)D_0,\quad
  I_0D_1-I_1D_0=x^3(x-1)^3D/360.
\]
At the physical endpoint \(R(t)=42/[a L(a)]\). Therefore the actual fourth equations imply
\[
 360a L(a)\bigl[JP_0(t)D_1-J(TP_0)(t)D_0\bigr]
                         -42x^3(x-1)^3D=0. \tag{N}
\]
After clearing denominators, the factors \(a-1,x^3,(x-1)^3\) are excluded by actual clock guards; the residual polynomial has degree two in \(y\).

At a first Legendre root the analogous second-mode solve has determinant \(-(5x^2-5x+1)D/10800\). Its other actual read at the endpoint is \(k(t)=-1260x^2(x-1)^3/[a(5x^2-5x+1)L(ax)]\). Thus the true equations imply
\[
 60a L(ax)\bigl[I_0J(TP_0)(t)-I_1JP_0(t)\bigr]
                             -7x^2(x-1)^3D=0. \tag{L}
\]
Its \(y\)-degree is again two. These are necessary fourth-row equations; all retained residue fields also check the **other** literal fourth read, with its exact two-mode interpolation.

## First-root exclusion over the rational and quartic coefficient fields

By \(L(a)=42(2a-1)(66a^4-132a^3+84a^2-18a+1)=0\), use \(a=1/2\) or the displayed irreducible quartic coefficient field. The genuine [third normalized gate](../dirk12-fifteen-rank3-invisible-all-ordinary-prefixes/README.md), stripped by monic \((y-1)(y-x)\), has degree five in \(y\). Its \(y\)-resultant with (L) has degree 47 in \(x\) in both fields. The exact factor replay discards only:

1. factors of the known guards \((5x^2-5x+1)(x-1)(x-t)L(ax)\); and
2. one degree-five factor where the true linear \(y\)-subresultant has nonzero leading coefficient and gives **\(y=t\)** exactly.

The only remaining \(x\)-factor has degree 20, with a linear subresultant determining \(y\). For the rational first clock choose \(p=17\): the degree-20 polynomial reduces to six factors of degrees \(2,2,4,4,4,4\). For the quartic clock choose \(p=19\): its coefficient polynomial is irreducible of degree four, and the degree-20 \(x\)-polynomial reduces to factors of degrees \(2,18\) over that field. In each of the eight exact fields the \(y\)-linear coefficient and all original scalar pivots are units, and the physical fourth gate at \(t=1/a\) is nonzero. The two monic lifts give integral \(a,x\); \(y\) is integral by the linear unit and \(t=1/a\) by the base guard. These exact residues therefore exclude every real first-root case.

## Nonroot exclusion by two exact resultants and literal collision strips

Let \(G_2(a,x)\) be the normalized second gate with its known \(x-1\) factor removed. Its leading coefficient in \(x\) is \(11088a^5\). Let \(G_3(a,x,y)\) be the monic Euclidean quotient of the true third gate by \((y-1)(y-x)\). Its entire remainder is an exact multiple of \(G_2\); thus the actual point lies on the quotient. Its leading coefficient in \(y\) is nonzero under the usual \(a\) and \(2x-1\) guards. The first resultant of \(G_3\) with the cleared residual of (N) in \(y\) is a nonzero scalar times \(a H(a,x)\), where \(H\) has bidegree \((49,22)\). The second resultant of \(G_2,H\), in \(x\), has degree 302 in \(a\).

After removing powers of \(a\) and the excluded \(L(a)\) factors, the relevant factors in \(a\) have degrees \(5,30,105,6\). In the first two low collision coordinates \(x=1\) (degree five) or \(x=t\) (degree six), the exact \(G_2\) is divisible by the respective linear factor over its characteristic-zero \(a\)-algebra. At \(p=19\) the stripped \(G_2\) is coprime to \(H\) on **every** residue field. Thus the only characteristic-zero common \(x\) could be the corresponding prohibited clock. This is not an inference that a modular collision is a literal collision.

For the degree-30 algebra the carried linear clock expression \(x_0=-V/U\) from the [earlier \(c=1\) packet](../dirk12-fifteen-rank3-invisible-nine-site-early-repeated-endpoint/README.md) is exact. Verify \(G_2(a,x_0)=0,\ G_3(a,x_0,t)=0\) in that rational coefficient algebra. The prime-\(19\) receipt checks unit denominators and \(\gcd(G_2/(x-x_0),H)=1\) in its degree-11 and degree-19 fields, forcing literal \(x=x_0\). In the same fields \(\gcd(G_3/(y-t),\text{residual of (N)})=1\), forcing literal \(y=t\), which is prohibited. The divisions are therefore performed before, not inferred after, reduction.

The final degree-105 base factor is preserved modulo \(17\) and splits into degrees \(93,12\). Both base fields have unit \(G_2\) leading coefficient; their common \(x\)-gcd of \(G_2,H\) is linear. That suffices to identify the reduction of the integral \(x\), without presuming it has that same linear formula in characteristic zero. The degree-five \(G_3\) has unit leading coefficient there, hence \(y\) is integral; the common \(y\)-gcd with the cleared (N) residual is again linear. The two actual normalized ordinary fourth quotients evaluated at \(t\) have at least one nonzero value in each residue field. The certificate checks their literal distinctness/Legendre/three-mode pivots before evaluation. This excludes the degree-105 branch also.

All local arguments reduce finite scalar coefficient algebras with explicit degree preservation and unit guards. No reduction of an unknown real tableau, positivity of weights, degree-twelve scalar quadrature assumption, or generic leading-degree shortcut is made.

## Replay

    python3 -B rebuild-first-root.py  # SymPy
    python3 -B rebuild-nonroot.py     # SymPy + python-flint; earlier sibling c=1 data
    python3 -B verify.py              # independent Python standard library

The field replay checks both first-root towers, all nonroot residue factors and unit-leading collision strips, and the literal fourth gate where appropriate. No full native rooted-order theorem is asserted for this subchart.
