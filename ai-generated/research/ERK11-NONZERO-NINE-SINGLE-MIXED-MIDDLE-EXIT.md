# Nine active labels: single mixed overlap with a middle triple member is impossible

**Scope.** Continue the [nonzero-first-pool nine-label chart](ERK11-NONZERO-FIRST-POOL-NINE-LABEL-OVERLAPS.md)
with thirteen active noncarriers and exactly two repeated active
labels, both plateau triples. Take the single mixed overlap
$a=e$, so $d=2a-1$ and the foreign $a$ read is physical 15.
This excludes the foreign $d$ read at **physical 8 or 9**
over characteristic zero under the inherited tableau premises.
The corresponding reflected cases use the same actual mixed
payment. The $d$ read at physical 6 or 7 is not excluded.
No ordinary stage interval changes.

## 1. Exact widths and the two left extras

As before, $F$ is the physical grade-three pure response and
$K$ is the cubic pooled profile with $F_i=K(c_i)$ on every
singleton active label. Let $h=a/2$. With the plateau triples
at $a,d$ and the other $d$ in the middle, all three left
nonplateau calibrated hits, at physical 3,6,7, are singleton
active labels. The two right extras, at physical 12,11, are
also active singleton labels. The left plateau, right plateau,
and all seven singleton clocks are distinct as active labels.

The earlier true endpoint mask gives
$$
 (X-a)(X-d)K(X)\in\operatorname{span}\{R_4,R_5\},\qquad O_8(a)=0 ,
$$
where $O_8$ is the exact octic of the preceding note.
Set
$$
 R_0(X)=R_5(a)R_4(X)-R_4(a)R_5(X),\qquad
 K_0(X)=R_0(X)/((X-a)(X-d)).
$$
The division is exact by the octic determinant. All width
guards in this proof are verified at the same finite place:
$O_8$ retains degree eight and is irreducible modulo 19,
$R_4(a),R_5(a),a,b=1-d$ are units there, and $R_0$ retains
degree five and is squarefree. These observations also prove
the corresponding characteristic-zero guarantees. In particular
$R_0$ spans the actual one-dimensional pencil solution,
$K_0$ is cubic, and its roots are disjoint from $a,d$.

Let
$$
 L(X)=X^2(a-X)/a,\qquad
 L^\star(X)=(1-X)^2(X-d)/b .
$$
The singleton $h$ gives $K(h)=a^2/8$. Thus
$K=a^2K_0/(8K_0(h))$, with live denominator checked at the
same place. The actual left extra clocks are the two roots
of the monic quadratic $A_L$ proportional to
$(K-L)/(X-h)$. The quotient is exact by its calibration
at $h$, and its degree-two leading coefficient is live.

## 2. One quadratic for the right extras

Write $Z$ and $M$ for the sum and product of the two right
extra clocks. The two true derivative rows of the first
inverse-Gram contact have coefficients
$$
 L_0=A_L(a),\quad L_1=-A_L(0),\qquad
 R_0=M-dZ+d^2,\quad R_1=-(1-Z+M).
$$
With the checked Gram polynomials $T_4,U_{4,4}$, set
$$
 A=L_0+T_4(a)L_1,\qquad
 B=T_4(b)L_0+U_{4,4}(a,b)L_1 .
$$
The actual contact gives $AR_0+BR_1=0$. The normalization
$A-B$ is a unit at the chosen prime, so
$$
 M=v_0+v_1Z,\quad
 v_0=(B-Ad^2)/(A-B),\qquad v_1=(Ad-B)/(A-B).
$$
The reflected nonplateau profile is $L^\star=\kappa K$
on the two right extra clocks, for the nonzero ratio
$\kappa$ of physical response scales. Reduce $L^\star$
and $K$ modulo the monic $X^2-ZX+M$, giving scalar
rows $(r_0,r_1)$ and $(q_0,q_1)$. Their determinant
$G(Z)=r_0q_1-r_1q_0$ vanishes at an actual $Z$; neither
row is divided by.

For any two cubics, this residue determinant has total
degree at most two in the pair $(Z,M)$. Indeed the two
coordinates for coefficients $c_i$ are
$c_0-c_2M-c_3 Z M$ and $c_1+c_2Z+c_3(Z^2-M)$,
and the degree-three and degree-four terms cancel
coefficientwise. The adjacent Lean gate gives the reduced
explicit expression. After the affine substitution for
$M$ the actual degree is at most two. The reduction
modulo 19 has degree two, so its leading coefficient
is a unit. This earns integrality of the actual algebraic
$Z$ after extending the width embedding; it is not
assumed merely because the equations are modular.

## 3. The ghost-root equations use only ordinary scalar payment

Let $D$ be the nine-label active hull and let the first
response pool at a label $x$ be $k/D'(x)$, with $k\ne0$.
Set $R=(X-a)(X-d)K$, proportional to $R_0$, and
$w=X(1-X)$. Because $R$ is squarefree of degree five
and orthogonal to degrees through three for $w$,
formal Lagrange weights $\lambda_\rho$ on its roots
give exact weight-$w$ moments through degree eight
in its splitting field. This step uses no order or
positivity. It just divides a scalar polynomial by $R$
and integrates the degree-below-five remainder.

For a plateau label $\xi$ with other plateau $q$,
the literal vector $w(C)(C-q)T$ is of grade six and
supported only on the actual plateau group at $\xi$,
where $T=K(C)-F-K(\theta)s$. Its model integral is
$\int wR/(X-\xi)=R'(\xi)\lambda_\xi$. Therefore the
actual ordinary scalar pool $B_\xi$ at that group
satisfies
$$
 w(\xi)B_\xi=\lambda_\xi+
        \frac{k\,w(\xi)}{D'(\xi)K(\xi)} .
$$
This used $K(\xi)\ne0$, which follows by squarefreeness
of $R$. At a singleton $x$, its ordinary weight is
instead precisely $k/(D'(x)K(x))$. The carrier
ordinary weights cancel at their common clock;
the endpoints are killed by $w$.

For any polynomial $f$ of degree at most eight, compare
the actual $w(C)f(C)$ moment with the degree-eight
Lagrange rule of $R$. Subtract the two plateau terms.
The remaining active sum
$k\sum_{x:D(x)=0}w(x)f(x)/(D'(x)K(x))$
equals the sum over the three roots $\rho$ of $K$
with weights $\lambda_\rho$.
These two node sets are disjoint: singleton $F$ is
nonzero and $K(a),K(d)$ are live. The elementary
barycentric identity on $DK$ gives that active sum
as the negative of the corresponding sum at the
roots of $K$ (numerator degree at most ten, total
hull degree twelve). Isolate any such root by a
quadratic Lagrange test on the three roots of $K$.
This gives the exact necessary equations
$$
 D_1(\rho) M_R(\rho)=-\widehat k\, w(\rho),\qquad
 M_R(x)=\int w(Y)\frac{R_0(Y)-R_0(x)}{Y-x}\,dY,\qquad
 D_1=D/((X-a)(X-d)).
$$
Here $\widehat k$ absorbs the independently live scale
between $K$ and $K_0$. Equivalently these are a single
remainder equation modulo $K_0$. There is no division
by a ghost weight. The root simplicity used above is
certified at the chosen prime with full degrees.

## 4. Paid middle elimination and exact finite-place replay

Let $S,Q$ denote the sum and product of the two
singleton middle clocks (besides the foreign $d$).
Then
$$
 D_1=(X-h)A_L(X)(X^2-ZX+M)(X^2-SX+Q).
$$
The ghost remainder equation is a linear system of
three coefficients for $S,Q,\widehat k$. If
$H=(X-h)A_L(X)(X^2-ZX+M)M_R(X)\bmod K_0$,
its columns are the residues of $-XH,H,w$ and its
right-hand side is the residue of $-X^2H$.
Let $\delta,S_0,Q_0$ be the determinant and the
two Cramer numerators. The reduction of $\delta$
is coprime to $G$ at 19, so it is a unit at every
actual residue root of $G$. Thus $S=S_0/\delta$,
$Q=Q_0/\delta$, with integrality and live pivot earned.

Use the actual mixed middle equation
$A_0xy+B_0x+C_0y+D_0=0$ on **physical 8 and 10**,
from the four paid square-clock and primitive products.
These products have actual grades at most ten, and
are independent of nonzero first pooling. If $d$
is at physical 8, the physical-10 singleton root
satisfies
$$
 u=B_{\rm slope}=A_0d+C_0,\quad v=B_0d+D_0,\quad ux+v=0 .
$$
Its true quadratic gives the normalized necessary polynomial
$\delta v^2+S_0uv+Q_0u^2=0$, with no division by $u$.
If $d$ is at physical 9, the two outer singleton clocks
are the two roots of the same quadratic. With
$u=B_0-C_0$ and $v=A_0Q_0+C_0S_0+D_0\delta$,
the outer equation has $\delta u x+v=0$ at the first
root. Its necessary norm is
$v^2+S_0uv+\delta Q_0u^2=0$, canceling only the
earned live $\delta$. This treats both outer orders.

The standalone exact replay uses the complete field
$\mathbb F_{19^8}$. It verifies every rational pivot above,
the full degree of $G$, and unit gcds of $G$ with
$\delta$ and with each of the two final norms. If an actual
characteristic-zero solution existed, first embed the
algebraic width in $\overline{\mathbb Q}_{19}$. Then
extend to the algebraic $Z$. The width is integral by
the octic leading unit and $Z$ by the quadratic leading
unit. Every listed pivot is separately live at its
residue. Its existence would therefore force a common
root in the algebraic closure of the residue field,
contrary to those gcds. No tableau or unearned guard
is reduced, and no $Z$ degree drop or vanished Cramer
pivot is omitted.

The exact arithmetic uses python-flint. The adjacent
portable Lean file checks the cubic-remainder determinant
and the two denominator-free scalar norm formulas;
the actual rooted support and finite-place argument
are the mathematical proof.

The [kernel logs and exact replay](erk11-nine-single-mixed-middle-audit/)
document the scalar checks. The [portable norm identities](../lean/RKCert/ReviewedNative/ERK11CubicRemainderNormGate.lean)
pass on all four requested core Lean versions; the physical chart proof is mathematical.
