# Arbitrary sharp ERK11 prefixes: terminal pencil, Jacobi atoms, and invariant core

This note continues the literal first-eleven
[dense cutoff](ERK11-RANK-FREE-FIRST-ELEVEN-CUTOFF.md) and the
[positive moment rank obstruction](ERK11-SHARP-PREFIX-MOMENT-OBSTRUCTION.md).
For a hypothetical 17-row ordinary order-eleven strictly explicit method,
let \(C=\operatorname{diag}(A\mathbf 1)\), \(Y=I-C\), and let \(E_g,F_g\)
be the full numerical rooted and pure spaces through degree \(g=|t|-1\).
A rooted pair \((u,P)\) has actual vector \(u\) and exact polynomial model
\(P\). Operations \(A,C\) act on the model by the lower primitive \(J\)
and multiplication by \(X\), and root products multiply both entries.
Write \(\ell_m(P)=\int_0^1(1-X)^mP(X)\,dX/m!\).
Superscript “pre” means the literal first eleven; “late” means
zero through coordinate 11. Set
\[
 H_g=E_g+\eta K e_{17},\quad \eta=[c_{17}=1],\quad
 \epsilon=[bA-bY\ne0],\quad
 \alpha=\dim\mathcal A_6^{\rm pre},\quad
 r_+=\operatorname{rank}((\ell_1,\ldots,\ell_4)|_{\mathcal A_6^{\rm pre}}).
\]
The prefix is separated through degree five, \(E_5^{\rm pre}=K^{11}\),
and its exact model map is \(\Pi\). The prefix ambiguity
\(\mathcal A_6^{\rm pre}\) is the space of degree-six models paired
with numerical zero in this prefix, not a guessed polynomial family.

**Results.** In rank one, coordinate 11 supplies a true fifth-degree
numerical pivot, and its clock has at most two choices given the
late moment vector. At maximal \(\alpha=2+r_+\), several branches
force an actual endpoint atom represented by the fixed Jacobi
polynomial. This determines the full polynomial ambiguity in
all grades 6 through 10. In the nonendpoint maximal rank-one branch
the atom is supported on rows 13–16; a four-slot argument determines
the charged moments when \(bA\) also ends at a nonendpoint. A
clock-invariant \(F_5^{\rm pre}\) forces a rigid arbitrary-chart
classification, including a dense first eight through degree four.
None of these statements excludes every possible extension, so
the ordinary order-eleven interval remains 17–18.

## 1. The rank-one terminal decoder pencil

Take \(r_+=1\), and write \(d=(d_1,d_2,d_3,d_4)\ne0\) for a generator
of the late positive moment image, in the normalized \(\ell_m\)
basis. No adjacent pair can both vanish: the corresponding two
consecutive taps would factor through the full \(E_5^{\rm pre}\)
at grade six, supplying the forbidden
[consecutive weighted pair](ERK11-SHARP-PREFIX-PURE-TAIL.md).

Put \(P=\Pi(e_{11})\). It cannot vanish: otherwise \(\Pi\)
would already decode all degree-five models from the first
ten rows, against the paid dense minimum eleven.
It belongs to \(X K[X]_{\le4}\) by the actual origin.
Set \(p_m=\ell_m(P)\), and \(y=1-c_{11}\).
The five reads \(p_1,\ldots,p_5\) identify \(P\) by the
weight-\(X(1-X)\) anchored Gram through degree four.
The custom weights from the positive taps that factor on the
prefix through grade six form \(W=d^\perp\) in the basis
\((Y^m/m!)_{m=1}^4\). This does not describe weights of other
polynomial degrees.

On the prefix \(Ae_{11}=0\) and \(Ye_{11}=y e_{11}\). Applying the
exact \(W\) rows to the two actual pairs gives scalars \(a,h\) with
\[
    p_{m+1}=a d_m,\qquad
    (m+1)p_{m+1}-y p_m=h d_m\quad(1\le m\le4).                 \tag{1}
\]
If \(y=0\), two distinct nonzero entries of \(d\) from the
outer no-pair tests force \(a=h=0\).
Thus \(p_2=\cdots=p_5=0\) and \(P\) must be a nonzero multiple of
\[
                   X(66X^4-120X^3+72X^2-16X+1).
\]
Its mean and first shifted moment are \(1/6,1/210\);
its next four shifted moments are zero. The
weight-\(X(1-X)^2\) Gram through degree three gives uniqueness.

If \(y\ne0\), (1) gives \(a\ne0\): otherwise
\(p_2=\cdots=p_5=0\), a nonzero \(d_3\) or \(d_4\) forces
\(h=0\), and \(y p_1=0\). For \(m=2,3,4\) put
\[
                   ((m+1)a-h)d_m=ya d_{m-1}.                 \tag{2}
\]
A zero of \(d_m\) in that range forces its predecessor zero,
so \(d_2d_3d_4\ne0\). Subtract the \(m=3,4\) equations after
cross multiplication, and take the second difference of
all three in the same way. The exact conditions are
\[
 y(d_3^2-d_2d_4)=d_3d_4,\qquad
       2d_2^2d_4-d_1d_3d_4-d_2d_3^2=0.                     \tag{3}
\]
Consequently the only possible reflected clocks for a given
charge line are zero or \(d_3d_4/(d_3^2-d_2d_4)\) under the
nonzero and cubic guards. Once the latter \(y\) is given,
(2) fixes \(h/a\), and (1) fixes the model line \(P\).

Independently of \(y\), \(e_{11}\notin E_4^{\rm pre}\).
Otherwise \(P\in X K[X]_{\le3}\), and \(p_2,\ldots,p_5\)
cannot all be zero by the weight-\(X(1-X)^2\) Gram. Thus \(a\ne0\).
Now \(A^2e_{11}=0\) is paid through grade six and gives
\(p_{m+2}=a' d_m\) for \(m=1,\ldots,4\). The overlap yields
\(a d_2=a' d_1,\ a d_3=a' d_2\).
If \(a'=0\), \(d_2=d_3=0\); if either \(d_2,d_3\) vanishes
with \(a'\ne0\), an adjacent zero pair again results.
Hence \(d_2d_3\ne0\) and \(d_1d_3=d_2^2\).
Subtract (2) for \(m=2,3\) after multiplying by \(d_3,d_2\):
it gives \(a d_2d_3=0\), a contradiction.
Equivalently, row 11 is dependent on its predecessors on
grade four but is independent of them on grade five.

## 2. At maximal alias dimension the Jacobi pair is actual tail data

For \(\alpha=2+r_+\), the fixed anchored kernel is contained
in \(\mathcal A_6^{\rm pre}\). Use \(P_4=XR_4,\ P_5=XR_5\), where
\[
 R_4=42X^4-84X^3+56X^2-14X+1,\qquad
 R_5=132X^5-330X^4+300X^3-120X^2+20X-1.
\]
Their means are \(1/30,1/42\), and all four positive moments
vanish. Thus actual late lifts have a nonzero ordinary read
even though the positive reads are zero.

**Rank two.** The known caps give \(c_{17}=1,\epsilon=0\)
and a three-dimensional \(H_6^{\rm late}\).
Its positive kernel is exactly \(K e_{17}\).
The Jacobi lifts prove \(e_{17}\in E_6\), not just the augmented
space. Every pure grade-six vector is determined by its
restriction to the prefix: a pure late vector would lie on
that line and be killed by the live \(b_{17}\).
The same single-coordinate conclusion works in a maximal
rank-one endpoint branch when \(\epsilon=\eta=1\), since
\(H_6^{\rm late}\) has dimension at most two. It also works
in the already measured \(\dim F_5=6\) endpoint branch:
its positive kernel is the sum of \(K e_{17}\) and the proven
late pure line, which can be subtracted without changing the model.

**Rank one and nonendpoint.** Let \((v,P_4)\) be an actual
late lift, and let \(u\in E_6^{\rm late}\) have positive read \(d\).
Here \(\epsilon=1,\eta=0\). The cap \(\dim E_6\le13\) and
\(bv=1/30\) yield \(E_6^{\rm late}=\langle u,v\rangle\),
with positive kernel \(Kv\). At grade seven
\(\dim E_7^{\rm late}\le3\).
The shifts 1 through 3 on \(u,Au,Yu\) give columns
\[
        (d_1,d_2,d_3),\quad (d_2,d_3,d_4),\quad
                                  (2d_2,3d_3,4d_4).
\]
The rank is at least two: if two of \(d_2,d_3,d_4\)
are nonzero, the clock factors 2,3,4 distinguish those
entries. Otherwise no adjacent zero pair leaves
\(d_2=d_4=0,\ d_1d_3\ne0\), and the first two columns
are independent. Since \(v\) is already in the positive
kernel, the rank is exactly two; the grade-seven positive
kernel is still \(Kv\). Both \(Av,Yv\) lie in this line
and have ordinary read zero by the paid identities.
Hence \(Av=Yv=0\).
This forces an endpoint-supported numerical vector in
the kernel of the actual \(A\), despite the nonendpoint
last clock. The determinant of the displayed columns,
up to sign, is the cubic in (3), so it vanishes
independently of the clock at row 11. With the no-pair
guards, either \(d_2d_3d_4\ne0\) or
\(d_2=d_4=0,\ d_1d_3\ne0\).

The positive reads here cut through row 12.
Indeed \(\dim H_6=13\), so at \(g=6,L=4,k=12\) the spare
is zero. The local five-slot penultimate on vectors zero
through 12 vanishes by the nonendpoint
[FourTap](WEIGHTED-ORDER-NINE-FOUR-TAP.md).
The [audited reanchoring proof](ERK11-SHARP-PREFIX-MOMENT-OBSTRUCTION.md)
then uses the same conditional weighted floors for sizes
nine and ten, paying \(k+1=13<14\).
The nonzero positive map on \(E_6^{\rm late}\) factors
through coordinate 12, so its kernel \(Kv\) is zero
at 12. The atom is supported on endpoint sites among
**13–16**. In particular this maximal branch is excluded
if none of those clocks is 1.
If there is exactly one such candidate, it has a zero
outgoing column (because \(Av=0\)), a nonzero ordinary
weight and the individual exactness below.

**Actual exact evaluation by the atom.** In the cases just
proved normalize \(v\) to the pair \((v,P_4)\).
For any grade-four pair \((u,R)\),
\[
                     b(v\odot u)=\ell_0(P_4R)=R(1)/30.
\]
The last equality holds because \(R-R(1)\) is divisible
by \(Y\) with degree at most four and the four positive
moments vanish. Thus the physical read \(30b\operatorname{diag}(v)\)
is exact evaluation at 1 through grade four.
If \(v\) is a single coordinate, that actual row itself is
degree-four exact, in particular row 17 in the maximal
rank-two case. A degree-five product would cost eleven,
so no degree-five stage exactness is claimed.

## 3. The full-tableau polynomial ambiguity at every grade 6–10

In those atom cases, \(P_4,P_5\) lift along the same invariant
endpoint line, after subtracting the optional pure \(F_5\)
line when needed. Their mean ratio is \(5/7\), so a true
zero pair has model \(P_5-(5/7)P_4\).
Since \(Yv=0\), there are also true zero pairs with models
\(Y^kP_4,Y^kP_5\) at grade \(6+k\), for \(k\ge1\).
For \(0\le j\le4\), these give \(2j+1\) independent models
at grade \(6+j\). Indeed, after extracting \(X\), any
relation has the form \(U R_4+V R_5=0\) with
\(\deg U,\deg V\le j\). The identity
\[
\begin{aligned}
 &(4620X^4-9240X^3+6111X^2-1491X+100)R_4\\
 &\quad+(-1470X^3+2205X^2-931X+98)R_5=2
\end{aligned}
\]
implies \(R_5\mid U\), hence \(U=V=0\).
The coefficient of the constant-direction pair and then
all other coefficients must be zero.

This exhausts the whole-tableau numerical zero-model
space: every model is anchored at 0 and kills
\(\ell_0,\ldots,\ell_{4-j}\) by ordinary order eleven.
These \(5-j\) constraints are independent on the anchored
space by the weight-\(X\) Gram through degree \(4-j\).
Their kernel has dimension \((6+j)-(5-j)=2j+1\).
Consequently
\[
                       \dim(E_g/F_g)=12-g \quad(6\le g\le10).
\]
In the maximal rank-two case, actual grade-six vectors
begin at 12 and 13, and the live adjacent path reaches
14,15,16 by \(A,A^2,A^3\) from row 13.
Together with \(e_{17}\in E_6\) these and the reverse caps
give \(\dim E_g=14,15,16,17,17\) at \(g=6,\ldots,10\).
The full pure ranks are exactly \(8,10,12,14,15\).
In the maximal nonendpoint rank-one branch
\(\dim E_6=13,\dim E_7=14\) by the preceding argument,
so \(\dim F_6=7,\dim F_7=9\); no later pivots are presumed.

## 4. Further weighted cutoff in the nonendpoint Jacobi branch

Retain the maximal rank-one nonendpoint assumptions.
Set \(\beta=bA\) and write \(t\) for its last nonzero
physical index. The conditional weighted floor and
strictness give \(15\le t\le16\).
Drop the first nonzero coordinate \(i\) of the endpoint
atom \(v\) in the
[pure-tail linear quotient](ERK11-SHARP-PREFIX-PURE-TAIL.md),
but descend \(\beta\) rather than \(b\), since
\(Av=Yv=0,\ \beta v=0\).
If \(i\le t\), after truncating at \(t\) this leaves at most
four tail slots, preserves strictness and the retained
physical diagonal clocks, and cannot remove \(t\)
(a row killing \(v\) cannot end at its leading site).
If \(i>t\), the original truncated tail already has at
most four slots. This quotient is only for linear words.

If \(c_t\ne1\), use four slots indexed 0 to 3,
padding leading zeros if necessary. Put \(y_j=1-c_j\)
locally and \(\mu_j=\beta A^j u\).
The shift-one word budget is three. If \(\mu_3=0\),
then \((\beta A)_2(A^2u)_2=0\).
If \((A^2u)_2=0\), the paid \(\beta YA^2u=0\) forces
\(y_3\mu_2=0\), so \(\mu_2=0\).
If \((\beta A)_2=0\) instead, \(\rho=\beta A\)
is supported on 0,1. Then \(\rho A u=\mu_2\)
reads only the edge from 0 to 1.
Two cost-three words give \(y_0\mu_2=y_1\mu_2=0\),
but the lower paid \(\rho Yu=3\mu_2\) cannot survive
if both clocks are zero. Again \(\mu_2=0\).
This contradicts the only cubic pattern with
\(d_4=0\), which has \(d_3\ne0\).
Thus all \(d_2,d_3,d_4\ne0\) and the top path
is live on exactly four slots.

Write \(T=\mu_3,\ U=\mu_2,\ V=\mu_1,\ \eta_i=A^i u\).
In the cyclic basis put
\(Y\eta_i=y_i\eta_i+s_i\eta_{i+1}+w_i\eta_{i+2}+\cdots\)
for \(i=0,1\). The single-clock words give
\(y_iU+s_iT=(4-i)T\) and
\(y_iV+s_iU+w_iT=(3-i)U\).
The mixed word \(\beta YA^{1-i}Y\eta_i\) at cost three,
less the high single-clock equation times the leftmost
factor 2, gives \(w_i y_3T=0\): the \(w_i\) term is on
the unique terminal path and higher terms vanish.
Since \(y_3T\ne0\), combine the two equations to obtain
\(y_i(U^2-TV)=UT\).
Thus \(y_0=y_1=z\ne0\), and their two-slot clock
subquotient is scalar, giving \(s_0=0\). It follows that
\[
         z d_3=4d_4,\qquad z d_2=3d_3,\qquad z d_1=2d_2.
\]
For the last equation substitute the first two into
\(z\) times the cubic (3) and cancel \(d_3d_4\).
This case is mandatory if just one site among 13–16
has clock 1, since \(\beta\) has zero coefficient there
and \(t\ge15\). In this case the two possible prefix clocks
from §1 simplify to \(c_{11}=1\) or \(c_{11}=1-z\).

There is also a genuine custom grade-seven row on the
literal prefix. Indeed \(E_7^{\rm late}=\langle u,Au,v\rangle\):
\(u,Au\) have independent first two positive reads by
\(d_1d_3-d_2^2=-z^2d_1^2/12\ne0\).
Put \(w(Y)=Y(Y-z)(2Y-z)\), with upper primitive
\(Tw=Y^2(Y-z)^2/2\) in the reflected variable.
The actual \(w\)-weighted combination of \(bA,bA^2,bA^3\)
is exact through grade seven and kills \(u,Au\) because
\(w(z)=Tw(z)=0\); it kills \(v\) as well.
It factors through the prefix and supplies an exact
**custom size-eight** output, not a Beta size-eight row.

## 5. Classification when the prefix pure space is clock-invariant

Suppose \(CF_5^{\rm pre}\subset F_5^{\rm pre}\).
The [first paid Hermite rent](../lower-bounds/paid-beta/separated-pure/SEPARATED-DEGREE-EIGHT-AND-NINE.md)
at grade five gives \(\dim F_6^{\rm pre}\ge8\).
The equality \(\dim F_6^{\rm pre}=4+\alpha\)
and the positive rank caps force \(r_+=2,\alpha=4\).
The endpoint atom and exact full pure ranks above apply.
Moreover \(CF_5\subset F_5\) in the full tableau:
for \(f\in F_5\), the prefix restriction of \(Cf\) is
in \(F_5^{\rm pre}\). Subtract a corresponding \(F_5\)
lift; the resulting pure late \(F_6\) vector is zero
by the rank-two kernel argument.

The prefix annihilator of \(F_5^{\rm pre}\) decomposes
by physical clock labels. A row there supported on one
clock and killing the constant also kills all polynomial
evaluations and \(F_5^{\rm pre}\), hence the whole
\(K^{11}\). There are exactly six represented labels,
each with a unique normalized row \(\lambda_x\)
giving evaluation at that clock. At zero it is the
origin row. For each \(x\ne0\), \(\lambda_x A\) is
supported strictly before the last position of \(\lambda_x\)
and integrates up to \(x\) on grade four. Rescaling gives
an ordinary order-five provider on at least six
preceding rows by the paid stage floor.
Thus the five nonzero normalized reads end exactly at
**7,8,9,10,11**, with distinct clocks \(x_1,\ldots,x_5\).
Consequently \(F_5^{\rm pre}\) restricts isomorphically
onto the zero-origin vectors of the first six:
any missing rank would give a second annihilator
supported there, whereas only the origin is supported there.

Let \(f_4=\dim F_4^{\rm pre}\in\{3,4\}\) and let \(K_4\)
be the nominal grade-four aliases on the first six.
The pure rank there is still \(f_4\), and the independent
origin and \(I_{x_1}\) model reads give numerical
\(E_4\) rank at least \(f_4+2\).
If \(f_4=4\), or that numerical rank is only five,
then paired rank minus numerical rank gives
\(\dim K_4=3\). Thus the alias space would be all
\(\{P:\deg P\le4,\ P(0)=I_{x_1}P=0\}\).
At the second provider \(\lambda_{x_2}A\) sees only
position 7 on a first-six zero pair, and that coordinate
is a fixed nonzero multiple of \(P(x_1)\).
Consequently \(I_{x_2}|_{K_4}\) is a multiple of
evaluation at \(x_1\). In the hyperplane case this makes
\(I_{x_2}\) a linear combination of \(I_{x_1}\) and
evaluation at \(x_1\) on the anchored space.
Testing \(X,X^2,X^3\) and rescaling \(x_1\) to 1
gives by the second difference
\((x_2/x_1)^2(x_2/x_1-1)^2=0\), impossible.

Thus \(f_4=3\), the first-six numerical \(E_4\) rank is
six, and \(K_4\) has dimension two. Its evaluation at
\(x_1\) is nonzero: otherwise the same independence
forces \(K_4\) to be the joint kernel of \(I_{x_1}\)
and evaluation at \(x_1\), and \(I_{x_2}\) again lies
in their span. On the one-dimensional line
\(K_4\cap\ker\operatorname{ev}_{x_1}\), the primitive has
double roots at 0 and \(x_1\), and a separate root \(x_2\)
by the second provider. Hence
\[
                 JP(X)={\rm const}\cdot X^2(X-x_1)^2(X-x_2).
\]
Any nonzero such \(P\) has \(P(x_2)\ne0\).
This proves degree-four model separation on the
literal first eight, with full numerical stage image
(five model directions plus three pure directions).
The grade-five aliases on those eight are exactly
\[
                     X(X-x_1)(X-x_2) K[X]_{\le2}.
\]
Indeed every anchored grade-five model has a first-six
zero representative after subtracting a matching pure
vector, and the next two normalized reads impose
exactly those two roots. This classifies the lower
prefix of an arbitrary invariant chart, not a calibrated
instance of the repaired first-eight family.

As a next exact causal test, put \(H=X\prod_{j=1}^5(X-x_j)\)
and \(G_i=H/(X-x_i)\).
The model \(G_i\) has a grade-five representative
supported only on row \(6+i\) up to nonzero scale.
Consequently \(H,JG_5,JG_4-aG_5\) are genuine grade-six
aliases, where \(a\) is the corresponding actual feed
coefficient after scaling. Similarly each earlier
\(JG_i\) must be correctable by only \(G_{i+1},\ldots,G_5\).
Every exact positive weight has to kill these corrected
aliases. These constraints account for real couplings
without assuming they suffice to construct a tableau.

## Scope and Lean

After the dense first-eleven and exact positive-rank
premises, the results are over a field in which \(11!\)
is nonzero, without any order, real-root or extra
exceptional-prime assumption. The unconditional recovery
of the dense prefix in a hypothetical 17-row ordinary
tableau uses the two characteristic-zero weighted floors.
No new ordinary RK stage bound or claim over arbitrary rings
follows here.

The core-only companion ERK11JacobiPrefixGate.lean checks
the terminal pencil, early-pivot contradiction, grade-seven
minor and cubic-pattern assertions, four-slot scalar
arguments, second-provider second difference, and the
Jacobi moment and Bézout identities. The proofs here supply
the rooted, chronological, dimension, and paid-field
transfers, not a new native order-eleven Lean theorem.
