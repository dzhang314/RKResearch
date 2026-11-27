# The unpaid three-helper chart is genuinely cubic-dirty

> **Follow-up:** The [exact primitive-field calculation](../strict-sdirk7-dirty-number-field/README.md) identifies the two isolated points as embeddings of a single degree-324 field. This original construction did not determine the field or its other embedding.

A strict nine-stage order-seven tableau can have three initial zero
weights, six nonzero weights at distinct clocks, and a vanishing
third quadratic defect **without** having a paid third helper. It can
have an actual cubic defect on the six active stages. The checked
example here is over \(\mathbb F_{19}\); a separate five-variable
Hensel construction proves that the phenomenon persists over every
\(\mathbb Z/19^k\), \(\mathbb Z_{19}\), and \(\mathbb Q_{19}\), and
over a finite extension of \(\mathbb Q\) embedded in
\(\mathbb Q_{19}\). This supplies neither a rational tableau, a real
embedding of that extension, nor a nine-stage lower bound over
\(\mathbb Q_{19}\).

## What happens over the rationals

Let \(A\) be lower triangular with constant nonzero diagonal
\(\gamma\), let \(c=A1\), and put \(C=\operatorname{diag}(c)\).
Let \(F_j\) be the actual homogeneous defect space through rooted
size \(j+1\), and \(T_j\) the corresponding elementary stage-column
space. Assume order seven, nine stages, zero first three weights,
and six distinct nonzero-weight tail clocks.

**Unconditional quadratic purity.** For \(v\in F_2\), the six-site
row \(bv\) kills clock degrees through four. If nonzero, interpolation
forces all six of its entries nonzero. Also \(bv^2\) kills degrees
through two, by the square of the same defect. Interpolate \(v\) by a
quadratic at three sites. The difference multiplied by \(bv\) is
supported on just the other three sites and has zero moments through
degree two, hence vanishes. Now \(v\) on the tail is a quadratic.
Its three zero tests against \(b,bC,bC^2\), together with the order
seven bush moments, give the nonsingular Hilbert system of size
three. Thus \(v\) vanishes on the tail. This argument needs neither
triangularity nor positivity of the weights.

**The only unpaid head is the zero-third-seed branch.** Put
\(g=2Ac-c^2\), the actual quadratic seed. The first two clocks differ:
otherwise \(A_{21}=0\), the first two implicit stage series agree,
and folding them yields an eight-stage rational tableau with a zero
weight, already ruled out. Their seeds are nonzero:
\(g_1=\gamma^2\), \(g_2/\gamma^2=2-(A_{21}/\gamma-1)^2\), and
two is not a rational square. If \(g_3\ne0\) and the helpers have
distinct clocks, \(g,Cg,C^2g\) pay all three head axes in grade four.
If \(c_3=c_i\) for \(i=1,2\), then
\(g_3-g_i=2A_{21}A_{32}\). The zero-tap case folds again.
Otherwise \(g,Cg,g^2\) separate the tied pair and pay all the head
axes by grade four. If \(g_3=0\), \(g,Cg\) still pay the first two
axes already in grade three.

If a rational method in that last case were cubic-clean on its
tail, the third axis would also be paid in grade three. Indeed there
is a cubic defect nonzero at stage three: otherwise the third
normalized clock would satisfy \(w^3-9w^2+18w-6=0\), which has no
projective point mod 5. Subtract that defect's first two components
using the two paid axes. By the presumed tail cleanliness, the
result pays the third axis. Thus an actually unpaid rational head
must have a cubic-dirty tail.

**A necessary two-branch terminal chart.** If the tail sees any
cubic defect, the two head axes and that defect give
\(\dim T_3\ge 4+3=7\), using the degree-three Hilbert separation.
The nonsingular grade step from \(T_3\) to \(T_5\) gives two more
dimensions, so \(\dim T_3=7\), \(T_5=K^9\).
On the six tail sites, \(T_3\) has dimension five. If multiplying
by the clock did not leave that five-dimensional space, it would
contain all clock powers, because it already contains \(1\).
Thus \(T_4\) projects onto all six tail coordinates. Its dimension
is eight: it contains the two head axes, and the nonsingular step
from \(T_4\) to \(T_6\) leaves at most eight.

The first adjoint error kills \(T_5\) and therefore vanishes:
\(bA=b(1-c)\). Consequently the last clock is \(c_9=1-\gamma\).
The second adjoint error
\[
 D=(bC)A-b(1-c^2)/2
\]
kills \(T_4\); \(D_9=-b_9\gamma^2/2\ne0\). Because \(T_4\)
surjects onto the six tail coordinates, \(D\) must be nonzero at
the third ghost axis. The two rows \(D,DC\) span \(\operatorname{Ann}(T_3)\).
Both annihilate, and the last two positions certify independence:
the normalized penultimate ratio is \(D_8/b_8=L_2(u)\ne0\) by
triangularity and the first adjoint equality, where \(L_2(u)=u^2/2-2u+1\)
has no rational root. The two terminal clocks differ.

Now divide \(A,c\) by \(\gamma\), write \(z=1/\gamma\), and
reflect the normalized clocks as \(y=z-c/\gamma\). The last
reflected clock is \(1\), the penultimate is \(u\), and write \(v\)
for the antepenultimate. Use \(D\) for the second error divided by
\(\gamma^2\), and let \(Y=\operatorname{diag}(y)\). Since rows
\(DA/\gamma\) and the third reverse error kill \(T_3\), terminal
triangularity determines their coordinates in \(\langle D,DY\rangle\):
\[
 (bY^2)(A/\gamma)= bY^3/3+f(Y)D,\qquad
 D(A/\gamma)=\bigl(1+\theta(1-Y)\bigr)D,
 \quad \theta=\frac1{2L_2(u)},\quad
 f(y)=-\frac43+\frac{2\theta-2}{3}(y-1).
\]
Here and below left versus right multiplication by a diagonal matrix
means componentwise multiplication of a row. The preceding reverse
row has two taps to the last two physical sites. If \(d=D_7/b_7\)
and \(p\) is its weighted tap to \(u\), the other weighted tap is
\(r=v-1-p\), and the remaining reads are
\[
 d=v^2/2-v-pu-r,\qquad
 v^2+pu^2+r-v^3/3=f(v)d,\qquad
 pL_2(u)-r/2=\theta(1-v)d.
\]
Eliminating \(p,d\) after clearing only \(u-1\), \(L_2(u)\),
and small integer denominators gives
\((u-v)(v-1)(u+v-4)(2u-v-1)=0\).
Since the three sites differ, \(v=4-u\) or \(v=2u-1\).
The exact scalar script and [native scalar theorem](../../lean/RKCert/Research/SDIRKSevenSixActiveTerminalScalar.lean)
check the elimination without dividing by any additional Cramer
determinant. The rank and tableau-to-scalar bridge are mathematical
reductions, not claims of a fully native global rational obstruction.

## A native finite witness and five-equation lift

The literal [Lean witness](../../lean/RKCert/Research/SDIRKSevenSixActiveDirtyF19.lean)
checks every rooted condition through seven for a new strict
nine-stage tableau of diagonal \(12\) over \(\mathbb F_{19}\).
Its weight vector is \((0,0,0,7,16,17,1,2,15)\), its last six
physical clocks are \((7,11,12,10,1,8)\), its third quadratic seed
is zero and \((A g)_4=2\ne0\). The third coordinate axis is not
paid through grade four, because \((bC A)_3=15\ne0\). The eighth
bush has factorial-scaled value \(6\); i.e. its residual from one
is \(5\). The [deterministic search](check-dirty-chart.py) constructs
the literal [JSON](f19-dirty-nine.json) and independently checks all
85 trees. This witness uses the reflection branch: \(u=0,v=4\).

For a lift, keep \(u=0\), \(v=4\), and the first strict normalized
tap \(t=1/2\). Write the six reflected tail clocks as
\((a,b_*,c_*,4,0,1)\). Let \(h\) be the reflected third helper
clock, so its forward clock is \(w=z-h\). There are five unknowns
\((z,a,b_*,c_*,h)\). The solution mod 19 is \((8,9,15,7,5)\).

Let \(P(X)=\prod_i(X-y_i)\), \(s_i=1/P'(y_i)\), and
\(K_i=I(P(X)/(X-y_i))\), where \(I(X^j)=z^j/(j+1)\).
Take \(\beta_i=s_i K_i\). The first equation is \(I(P)=0\);
it makes the quadrature exact through degree six. The same uniform
functional may be used in normalized forward clocks \(x_i=z-y_i\).

Define the affine \(W\) by \(W(0)=-hK_0\), where \(K_0\) here
denotes the site at zero, and \(W(1)=-(1-h)K_1/2\) at the site
one. Write
\[
 D_i=\frac{s_i W(y_i)}{y_i-h},\qquad
 D_3=-\sum_iD_i,\qquad v_i=\frac{(y_i-h)D_i}{\beta_i},\qquad
 v_3=-\frac{\sum_iD_i v_i}{D_3}.
\]
The full \(D\) and \(v\) have zero first two entries. Weights at
the three helpers are zero; tail indices \(i\) in this display are
all six active sites. Because \(W\) is affine and \(s\) kills
degrees through four, \(D\) kills moments through degree four,
and \(b v\) kills moments through degree three. The second and
third equations are
\[
 W(4)=(4-h)K_4,\qquad
 2(c_*+3)\frac{D_{c_*}}{\beta_{c_*}}+c_*^3-9c_*^2+18c_*-6=0.
\]
The fourth is \(\sum_i\beta_i v_i^2=0\). By construction
\(Dv=0\), and the fourth equation says \(D(Y-h)v=0\).

The second helper has forward clock \(x_2=1+t\) and seed
\(g_2=1+2t-t^2\). The three head seeds are \((1,g_2,0)\).
Let
\[
 \eta=\frac{(x_2-w)x_2-g_2(1-w)}{(x_2-w)-g_2(1-w)},\qquad
 q(X)=(X-w)(X-\eta).
\]
On the three head clocks \((1,x_2,w)\), \(q\) is proportional
to the seed. Write \(J\) for the zero-origin polynomial primitive.
The fifth equation is
\[
 q(z-a)-Jq(z-a)+Jq(w)v_a/v_3=0 .
\]

## Why the five equations suffice over a unit-pivot ring

Denote the normalized six-by-six lower-triangular tail block by
\(B\), with diagonal one. Let
\[
 R=\begin{pmatrix}\beta\\\beta Y\\\beta Y^2\\D_{\rm tail}\end{pmatrix},
 \quad \rho(y)=1+(1-y)/2,\quad f(y)=-1-y/3 .
\]
Each column of \(B\) is required to obey the four reverse reads
\[
 RB=\begin{pmatrix}
 \beta Y\\
 \beta Y^2/2-D_{\rm tail}\\
 \beta Y^3/3+f(Y)D_{\rm tail}\\
 \rho(Y)D_{\rm tail}
 \end{pmatrix}.
\]
The last, penultimate and antepenultimate normalized weighted
reverse taps are respectively absent, \((-1)\), and \((0,3)\);
the four reads reduce to direct evaluations using
\(D_y/\beta_y=-1/2,1,1\) at the sites \(1,0,4\), respectively.
At the fourth reversed row, the first three reads are a unit
Vandermonde solve on \(4,0,1\). Interpolating the ratios \(D/\beta\)
on those three sites by \(L_2\), the fourth read is precisely the
third equation above, divided by six. The last four columns of
\(R\) form a unit minor. Thus the remaining two physical columns
of \(B\) solve uniquely from the four reverse reads after choosing
the tap from the first physical tail row to the second.

The required forward read is
\[
 B q(x) = Jq(x)-Jq(w)v_{\rm tail}/v_3 .
\]
The fifth equation is exactly its first coordinate. Its second
coordinate sets the free tap using the unit \(q(z-a)\). Both sides
are read identically by \(R\): for the first three rows this is the
quadrature integral of the primitive by parts and vanishing defect
moments (each extra \(D\)-test is proportional to \(q(w)=0\)).
For the fourth row use
\(D_{\rm tail}Jq(x)=-D_3Jq(w)\) and
\(D_{\rm tail}v_{\rm tail}=-D_3v_3\).
The unit last-four minor of \(R\) forces equality at the remaining
four physical coordinates.

Set the three normalized head rows to
\((1,0,0),(t,1,0),(w-1-k,k,1)\), where
\(k=(w^2-4w+2)/(2t)\). Feed from the helpers into every tail row
by solving its three reads against \(1,x,g\): require
\(A'1=x\), \(A'x=x^2/2\) on the tail, and \(A'g\) on the tail
to be \((A'g)_3 v_{\rm tail}/v_3\). Here \(A'\) denotes the full
normalized tableau \(zA\). The 3-by-3 head test matrix is a unit
minor. Because \(q(x)\) is proportional to \(g\) on the head and
the forward tail read holds, \(A'x^2-x^3/3\) on the last seven
coordinates is also proportional to \(v\), with its actual third
coordinate fixing the multiple.

Extend the four reverse reads from the tail block to the full
matrix \(A'\), with the same right-hand formulas (now \(b,D,Y\)
are all length nine). The errors are already zero on their tail
coordinates. Test each error on \(1,x,g\): for \(1,x\) the reads
match by integration by parts and \(D\)'s pure moments; for \(g\)
the equations follow from \(A'g\) being a linear combination of the
first two axes and \(v\), with \(bY^jv=0\) for \(j\le3\),
\(Dv=DYv=0\), and \(Dg=0\). The unit head test matrix then kills the
remaining three coordinates of every reverse read error.

For completeness, take a candidate graded defect flag as follows:
grades 0 and 1 are zero; grade 2 is the span of \(g\); grade 3
the span of the first two ghost axes and \(v\); grade 4 the
simultaneous kernel of \(b,bY,bY^2,D\); grade 5 the simultaneous
kernel of \(b,bY\); and grade 6 the kernel of \(b\). The four
reverse reads just established show \(A'\) sends grades 3, 4, 5 to
their successors. Multiplication by the clock has the same property.
The explicit cubic relations give the grade-2 moves. Products of
grade \(2\) with grades \(2,3,4\) have support in the first two
ghosts. Products of two grade-3 defects have zero \(b\)-read by
\(\sum_i\beta_i v_i^2=0\). Thus products go to their paid sum grades.
The pure monomial primitive errors
\((j+1)A'x^j-x^{j+1}\) lie in grade \(j+1\) for \(j\le5\):
\(j=0,1,2\) by the construction, and \(j=3,4,5\) by the reverse
reads and integration by parts within the stated clock budgets.
This proves by root attachment and multiplication that every
normalized elementary tree column differs from its exact clock
power by a paid defect. The quadrature rule then proves order seven
for the physical matrix \(A=A'/z\). This verification is symbolic over
the unit-pivot ring; it does not extrapolate from checking a finite
list of residue powers.

## Hensel certificate, exact scope, and replay

In the variable order \((z,a,b_*,c_*,h)\), the Jacobian of the
five equations, each written with left side minus right side, at
the indicated mod-19 point is
\[
 \begin{pmatrix}
6&11&7&4&0\\
4&2&5&3&5\\
9&1&16&9&10\\
10&7&0&15&9\\
15&17&2&7&4
 \end{pmatrix}
 \quad\text{with determinant }8\bmod19 .
\]
The five equations vanish there. All rational-function denominators
are units: the nodes differ and are distinct from \(h\);
\(z=8\), \(D_3=10\), \(v_3=5\), \(\eta\)'s denominator is \(2\),
\(q(z-a)=16\), the head test determinant is \(17\), and the last
four columns of \(R\) have determinant \(10\), modulo 19.
The six weights and the small integer denominators are nonzero
modulo 19. Each remaining reverse Vandermonde block is on distinct
sites with unit weights.

For a solution modulo \(19^m\), replacing the vector of parameters
by \(X+19^m d\) changes the residual modulo \(19^{m+1}\) by
\(19^m Jd\). This follows from ordinary polynomial first-order
expansion and the inverse expansion for a unit. The displayed
invertible Jacobian chooses the unique next digit, and induction
gives all powers and their inverse limit in \(\mathbb Z_{19}\).
The reconstructed tableau specializes to the literal native one
modulo 19, so the order-eight bush residual is a unit in every lift.
The unpaid third axis and the visible cubic defect also persist by
the same nonzero residues. This gives a nine-stage upper in
\(\mathbb Q_{19}\); the existing finite lower combines with it
only over rings admitting the residue-field map, such as each
\(\mathbb Z/19^k\) and \(\mathbb Z_{19}\).

Clearing only denominators that are units at the lifted point gives
five polynomial equations over \(\mathbb Q\) whose Jacobian is
still invertible there: each row was only multiplied by a nonzero
factor at a zero. Let \(L\) be the subfield of \(\mathbb Q_{19}\)
generated by the five lifted coordinates. Applying any
\(\mathbb Q\)-derivation of \(L\) to these equations gives a linear
system with that invertible Jacobian, so all five derivatives
vanish. If \(L\) had positive transcendence degree, a coordinate
derivation on a transcendence basis would extend to \(L\), because
the remaining finite algebraic extension in characteristic zero
is separable. This is a contradiction. Thus \(L/\mathbb Q\) is
a finite algebraic extension, and the rational reconstruction
formulas for the tableau are defined over \(L\).
Neither its degree nor the existence of a real place is asserted.

Use Python 3 to replay:

    python3 check-dirty-chart.py
    python3 lift-dirty-chart.py --power 4
    python3 lift-dirty-chart.py --power 12
    python3 check-terminal-elimination.py

The first three commands use the standard library only; the last
uses SymPy for the optional symbolic resultant. The fixed-power
JSON records are diagnostics; the all-power claim uses the
unit-Hensel and assembly proof above. Four Lean modules certify
[unconditional quadratic purity](../../lean/RKCert/Research/SDIRKSevenSixActiveQuadratic.lean),
the [exact rational head gate](../../lean/RKCert/Research/SDIRKSevenSixActiveHead.lean),
the terminal scalar elimination, and the literal mod-19 witness.
They were checked on stock Lean 4.36.0; [proof-audit.lean](proof-audit.lean)
checks their signatures and standard axiom dependencies. The
multivariate Hensel lift and unit-pivot assembly are mathematical
proofs with exact replay, not an all-k Lean theorem.
