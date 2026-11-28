# Exact fifteen-stage ERK10 over every power of 17

The [characteristic-17 literal](../erk10-fifteen-f17/README.md) has
a compatible family of exact, strictly explicit 15-stage lifts
over \(\mathbb Z/17^k\) for **every** \(k\ge1\), and over
\(\mathbb Z_{17}\) and \(\mathbb Q_{17}\). By coefficient transfer
this gives the same upper bound over every nonzero commutative
ring of characteristic \(17^k\). The eleventh-bush defect reduces
to the unit \(8\) modulo 17 throughout.

This is an all-power **mathematical reconstruction and Hensel
proof**, not an inference from a long finite digit list. The
[literal checks through \(17^9\)](exact-audit.txt) independently
test all 1,205 ordinary rooted equations at each displayed
power. No char-zero rational tableau, single factorial-localized
tableau, or global field-independent upper bound is claimed.

## Geometry and exact scalar equations

Use reverse ordinate \(Y=1-X\) and physical high reverse order
\[
                       0,a,a,b,b,c,d,e,f,g,\qquad b=2a.
\]
The old origin contributes its \(Y=1\) mass; only it is weighted
in the [five-opening cubic-kernel construction](../erk10-five-opening-nonsplit-kernel/README.md).
Here \(a,\ldots,g\) all denote scalar ordinates. All nine distinct
quadrature sites are
\[
                       \mathcal X=\{0,1,a,b,c,d,e,f,g\}.
\]
Let \(I\) be the formal integral from 0 to 1, with
\(I(Y^j)=1/(j+1)\), and \(J_Y\) the formal primitive from 0.
Set
\[
 S(Y)=\prod_{z\in\mathcal X}(Y-z),\qquad
 \mu_z=I(S(Y)/(Y-z)).
\]
The formal quotient has no evaluation singularity. Use scalar
masses \(W_z=\mu_z/S'(z)\); these pay through degree eight by
Lagrange interpolation. Paying \(I(S)=0\) provides degree nine.

Set
\[
\begin{aligned}
 G(Y)&=Y(Y-a)(Y-b)(Y-c),&
 Q(Y)&=Y^5/20-bY^4/8+b^2Y^3/12,\\
 E_4(Y)&=(Y-1)(Y-e)(Y-f)(Y-g),&
 E_3(Y)&=(1-Y)(Y-f)(Y-g),\\
 Z_d^*&=(d-b)\big(-a^2\mu_a d-\mu_d d^2(d-b)\big).
\end{aligned}
\]
The **five polynomial equations** in \(a,c,d,e,f,g\) are
\[
\begin{aligned}
 I(S)&=0,\\
 c(c-b)\mu_c+a^2\mu_a&=0,\\
 I(E_4 J_YG)&=0,\\
 I(E_4 Q)&=0,\\
 Z_d^* I(E_3 J_YG)+4\mu_d G(d) I(E_3 Q)&=0.
\end{aligned}
\]
These are polys over \(\mathbb Z_{(17)}\); only fixed integers
prime to 17 are divided out in their definitions.

## The actual six-read reverse head

Split each of the masses at \(a,b\) equally between its two
physical rows. All mass divisions below are guarded by the
mod-17 receipts. Set the first reflected defect
\(\boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2\)
to \(u=-a^2/2,+a^2/2\) on the two \(a\)'s and zero elsewhere.
It is weighted-opposed. Prescribe
\(\boldsymbol h=L\boldsymbol u\) with group values
\[
                  h_z=-a^2\mu_a z/(4\mu_z)
                  \quad (z\ne0,1).
\]
Thus \(\mu_z h_z/z=-a^2\mu_a/4\) is the seven-site cofactor
line; its weighted moments on the forward powers
\(X,\ldots,X^6\) vanish. Indeed multiplying the group weights
by \(1-z\) gives a constant multiple of the leading
interpolation cofactor on the seven interiors. At the \(a\)
copies the physical \(h\)-values are \(0,-a^3/2\),
and at the \(b\)'s set \(a^3,\,2h_b-a^3\). At the initial
endpoint \(h=0\).

Enforce the following six literal reverse reads:
\[
\begin{aligned}
 L\boldsymbol1&=\boldsymbol y,\\
 L\boldsymbol y&=\boldsymbol y^{\odot2}/2+\boldsymbol u,\\
 L\boldsymbol y^{\odot2}
   &=\boldsymbol y^{\odot3}/3+(2a\boldsymbol u-2\boldsymbol h)/3,\\
 L\boldsymbol u&=\boldsymbol h,\\
 L\boldsymbol y^{\odot3}
   &=\boldsymbol y^{\odot4}/4+(a^2/2)\boldsymbol u
                                -\boldsymbol y\odot\boldsymbol h,\\
 L\boldsymbol h&=(a\boldsymbol1-\boldsymbol y)\odot\boldsymbol h .
\end{aligned}
\]
The first four physical rows have, respectively, empty incoming
row, tap \(a\) on the endpoint, tap \(a\) on the first \(a\), and
tap \(b\) on the second \(a\). Their six reads hold directly.
The second \(b\) uses the first four incoming features
\(1,Y,Y^2,u\). Its two remaining reads follow by substitution
from \(b=2a\): on its predecessors,
\(Y^3=(a+b)Y^2-abY\) and
\(h=-a^2 Y+(3a/4)Y^2-(a/2)u\).
These give the last two targets for any prescribed
\(h_{b,2}=2h_b-a^3\).
The row at \(c\) uses the first five predecessors and the
five features \(1,Y,Y^2,u,h\).
Its sixth read, the cubic primitive, is equivalent to
\(h_c=c^2(c-b)/4\) by the same support identity for \(Y^3\).
The second geometry equation gives exactly this value.
For all subsequent rows use the first six predecessors
to pay the full six reads; extra taps on later predecessors
are allowed if compensated by their six feature values.
The required read pivots are unit at the initial residue.

## Why precisely three terminal tests suffice

The six reads give all reverse words of grade at most four
on their full test spaces. More explicitly the defect directions
are \(\boldsymbol u\) at grade two, then
\(\boldsymbol u,\boldsymbol h\) at grade three, and
\(\boldsymbol u,\boldsymbol h,\boldsymbol y\odot\boldsymbol h\)
at grade four. Multiplication by a clock is just a mark.
At grade five the only new directions, aside from the marks
already paid by opposition and the \(X,\ldots,X^6\) cofactor,
are
\[
 \boldsymbol m=L\boldsymbol y^{\odot4}
                        -\boldsymbol y^{\odot5}/5,\qquad
 \boldsymbol R=L(\boldsymbol y\odot\boldsymbol h).
\]
For example \(L\) on the actual cubic defect is
\((a^2/2)\boldsymbol h-\boldsymbol R\), and \(L\) on
\(L\boldsymbol h\) is \(aL\boldsymbol h-\boldsymbol R\).
So the complete grade-five check is that
\(\boldsymbol m,\boldsymbol R\) annihilate \(X,\ldots,X^4\).

The two tests can use the donor vectors
\(G(\boldsymbol y)\) and
\[
 \boldsymbol Z=(\boldsymbol y-b)\odot\boldsymbol h
       -\tfrac14\boldsymbol y^{\odot2}
                         \odot(\boldsymbol y-b)^{\odot2}
       -\tfrac{a^2}{2}\boldsymbol u.
\]
Both vanish **at all first six physical reverse rows**:
\(G\) by the labels, \(\boldsymbol Z\) by the two opposite
\(a\) values, the factor at \(b\), and the literal \(h_c\).
The identities are actual at each copy, not just averaged.
Substitute the six reads into \(L G\) and \(L\boldsymbol Z\).
Modulo the already paid directions
\(\boldsymbol u,\boldsymbol h,\boldsymbol y\odot\boldsymbol h\),
one obtains
\[
  \boldsymbol m=L G(\boldsymbol y)-(J_Y G)(\boldsymbol y),
  \qquad
  \boldsymbol R-\boldsymbol m/4=L\boldsymbol Z+Q(\boldsymbol y).
\]
For the first identity use the monic quartic \(G\) to express the
cubic and lower nominal contributions. For the second, expand
\((\boldsymbol y-b)\odot\boldsymbol h\) using the definition of
\(\boldsymbol Z\); the scalar contributions are exactly
\(\boldsymbol y^{\odot5}/20-b\boldsymbol y^{\odot4}/8+
b^2\boldsymbol y^{\odot3}/12\).
Thus the weighted output tests require
\(L G\) to act as \(J_Y G\) and \(L\boldsymbol Z\) to
act as \(-Q\), tested on \(X,\ldots,X^4\).

Here is a direct causal solve of these actions. The first
additional donor \(d\) has zero row action on those two inputs
(no earlier nonzero values). Extra output responses can start
only at \(e,f,g\). The polynomial \(E_4\) kills all three, so
its two tests are exactly the two displayed blind integrals.
The other polynomial \(E_3\) kills \(f,g\), leaving only
the tap from the physical \(d\) donor into \(e\). Its target
two-response vector is
\((I(E_3 J_YG),-I(E_3 Q))\), which must be a multiple of
\((G(d),Z_d)\). The \(W_e E_3(e)\) multiplier is a unit.
Since \(Z_d^*=4\mu_d Z_d\), the last geometry equation is exactly
this compatibility. The \(G(d)\) entry is a unit, hence this
sets the tap into \(e\).

After paying \(E_3,E_4\), the two remaining test functionals
on \(X\mathcal P_3\) factor through the values at rows \(f,g\).
These two evaluation coordinates are independent by their
distinct nonzero forward clocks; the tests on \(X,X^2\)
solve their weighted responses. At each of these two physical
rows use two taps onto the earlier \(d,e\), whose
two-response determinant is a unit. In the last row no tap
onto \(f\) is needed. Compensate each extra tap by the unique
six-read response of the first six donors; this does not
alter either terminal response because those donors kill
both \(G,\boldsymbol Z\). The resulting \(L\) is strict and
matches the ordinary solved mod-17 literal. Thus the five
equations are sufficient, not merely necessary pressures.

## From the reverse chart to a literal tableau

Take \(B\) as the weighted transpose in forward order using
the ten physical nonzero unit weights. The eight grade-four
observer rows are the five weighted clock powers
\(\boldsymbol w X^0,\ldots,\boldsymbol w X^4\) and
\(\boldsymbol w\odot\boldsymbol u,\boldsymbol w\odot\boldsymbol h,
\boldsymbol w\odot\boldsymbol y\odot\boldsymbol h\).
The first five are actual clock-marked reads; the others are
actual word differences. Pair them with \(T_F=BEF-EJF\) for
\(\deg F\le4,\ F(0)=0\). The two nominal integrals agree using
the true word tests at grades at most five. All pairings vanish.

Append the first two *forward* row coordinate reads to the
eight observers. The resulting ten-by-ten matrix has unit
determinant (residue \(8\) in the replay). Consequently these
first two residual coordinates determine \(T_F\) on the
observer annihilator over the local coefficient ring,
not just over a field. Solve for a monic cubic
\(P=X^3+u_0 X^2+v_0 X\) with both residual coordinates zero;
the two-by-two determinant on \(X,X^2\) has residue \(7\).
This proves the literal full \(BEP=EJP\) equation. In the
base residue \(P=X^3+6X^2-X\), with nonsplit quadratic
factor (discriminant \(6\) is not a square in \(\mathbb F_{17}\)).

Use \(s=1,q=2\) and the rough opening clock \(1\) in the
five-row model-kernel chart, with
\(p=s v_0/(3s^2+2s u_0+2v_0)\).
All its row and decoder pivots are units in the base
residue, where \(p=13\) and \(P(s)=6\).
Use the literal high-to-old block \((EJ-BE)\Pi\).
Its root-product induction from the linked construction
works verbatim over the local rings: only units are
divided out. The clock quadrature and the paid short
reverse words imply actual ordinary order ten rather than
only a formal reverse statement.

## Hensel proof and native status

At \((a,c,d,e,f,g)=(16,2,8,9,4,6)\bmod17\)
the five equations vanish. The five-by-five Jacobian in
\((a,c,e,f,g)\), with \(d=8\) fixed, has determinant
\(10\bmod17\). The [geometry replay](geometry-audit.txt)
computes the entire matrix by finite differences modulo
\(17^2\), which are the formal derivatives modulo 17.
Thus every approximate solution with this residue can be
corrected uniquely in these five variables by adding
\(17^k\) times a digit, for **every** \(k\ge1\).
These are polynomial identities with bounded denominators
all prime to 17, so the usual first-order Taylor relation
holds modulo \(17^{k+1}\). The limit solves the equations
over \(\mathbb Z_{17}\).

The [reconstruction audit](reconstruction-audit.txt)
checks all relevant initial residue guards. In particular
the first-five and first-six read determinants are \(1,10\),
the two-response \(d,e\) determinant is \(8\), and the
dormant \(h\)-split difference is \(9\). Distinctness,
nonzero cardinal integrals, the two observer determinants
and the opening pivots all persist under lifting. Every
constructed literal reduces coefficientwise to the same
published mod-17 tableau at the base, and the eleventh
bush defect is therefore a unit. The native F17 endpoint
is a separate kernel certificate. This all-power extension
uses the mathematical geometry and reconstruction proof,
not a native HasOrder theorem on symbolic lifts.

## Reproduce

    python3 -B geometry.py
    python3 -B reconstruct.py 9
    python3 -B verify.py
    sha256sum -c sha256.txt

The last Python program independently reads only the serialized
coefficients and recursively enumerates the actual rooted trees.
It checks strict triangular row lengths, every weight and
coefficient residue, compatibility of consecutive lifts, and
the explicit order-eleven defect. The two builders use only
standard-library exact integer and modular arithmetic.
