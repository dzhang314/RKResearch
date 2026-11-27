# Middle-stage gates in the two-ended four-carrier ERK11 branch

Continue the [four-carrier two-ended reversal](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md)
and its [five-tap exclusion](ERK11-FOUR-CARRIER-FIVE-TAP.md).
Thus the 17-row strict chart and its weighted transpose after
reversal are each ordinarily exact through order eleven;
their actual grade-five spaces and pure model kernels coincide.
All ordinary weights are live, and the sole quadratic-defect
carriers are \(2,5,13,16\) at one physical clock
\(\theta\ne0,1\).
Write \(s\) for their indicator, \(r=As\),
\(\bar r=A^\star s=\lambda(r-r_{16}s)\) with \(\lambda\ne0\),
\(\beta=1-\theta\), \(A^\star=B^{-1}A^\mathsf TB\).
This is a conditional field deduction, with \(11!\) paid
after the previously earned branch premises.

**Results.** The literal first and last of the middle five
rows have a two-case exact clock test, not an arbitrary
degree-five spread. The common degree-six vector \(r^2\)
cannot already lie in the actual \(E_5\) in characteristic
zero, even in the paired-state branch. If both middle
boundary clocks are new, \(r^2\) and \(C^3r\) have independent
new grade-six classes. Over ordered fields both boundaries
are new, both boundary edges are absent, and all four edges
inside the middle block are live. The full carrier-state
cases and the ordinary interval 17–18 remain unresolved.

## Actual anchored lifts and a literal five-by-five middle block

The common pure space is
\(F_5=\langle s,sr,r,Cr,C^2r\rangle\).
On the first six, \(F_5\) maps isomorphically to
the vectors with zero at the origin.
Indeed \(s,sr\) distinguish the two carriers, and
\(r,Cr,C^2 r\) span the three independent noncarrier
profiles on rows 3,4,6 with nonzero \(r\) and
distinct clocks. The same holds at the opposite front
in reflected order. Define \(L(P)\) to be the unique
actual grade-five vector with model \(P\) and zero
first six, for \(\deg P\le5,\ P(0)=0\).
Existence and uniqueness follow by correcting the
clock-polynomial representative with the unique \(F_5\)
vector matching the first six. Define \(R(Q)\) by
zero last six for \(\deg Q\le5,\ Q(1)=0\).
Here both model variables have been converted to
ordinary \(X\); the reflected and ordinary grade-five
model maps agree after the affine change, since the
actual pure null spaces coincide.
The carrier restrictions of all \(E_5\) vectors are
affine in \(r_i\), and both end blocks distinguish two
carrier values. Hence both anchored lifts vanish at
**all four** carrier sites.

The physical supports of \(L(P)\) and \(R(Q)\) overlap
only on the five middle rows \(M=\{7,\ldots,11\}\).
The exact paid product is
\[
             \sum_{i\in M}b_iL(P)_iR(Q)_i
                                  =\int_0^1 P(X)Q(X)\,dX .
\]
This is the nonsingular weight-\(X(1-X)\) Gram on
polynomials through degree four after extracting the
endpoint factors. Thus **both** middle restrictions
are linear isomorphisms to \(K^5\).
For example any duplicate of an already present
first-six clean state at the first middle row would
give zero there in every \(L(P)\), impossible.
For a degree-five model polynomial \(P\) anchored at
both ends, \(L(P)-R(P)\in F_5\) is zero on all carriers.
The latter subspace has dimension three, so some
nonzero polynomial in the four-dimensional anchored
both-end space has \(L(P)=R(P)\).
In particular there is an actual nonzero \(E_5\) vector
with a nonzero model supported entirely on the five
middle coordinates.

More explicitly on each middle site,
\[
     L(P)_i=P(c_i)+r_i R_P(c_i),
\]
where \(R_P\) is the quadratic interpolant with values
\(-P(c_j)/r_j\) on \(j=3,4,6\).
One verifies the formula by cancelling the pure
remainder at each clean front site, then using \(s,sr\)
to cancel the two carrier sites; those terms are zero
on \(M\). There is a symmetric right formula with
the original \(r_j,c_j\) at \(j=12,14,15\).

Whenever the left-zero lift already has **actual grade
four**, its forward unary step is another left-zero
lift of grade five:
\[
        L(JP)|_M=A_{M,M}L(P)|_M,\qquad
                  JP(X)=\int_0^X P.
\]
Indeed the row block on \(M\) reads no later inputs
and the initial six are zero. Similarly on right-zero
grade-four lifts,
\(R(\bar J Q)|_M=(A_{M,M})^\star R(Q)|_M\),
where \(\bar J Q(X)=\int_X^1Q\), and the star uses
the actual diagonal \(b_i\), \(i\in M\).
These statements refer to a literal strict five-by-five
middle matrix, not arbitrary reconstruction.

## The first middle stage

Normalize the left front by its carrier clock \(\theta\).
Thus in this calculation \(x=c_7/\theta\),
\(z=c_6/\theta\), and physical \(f=r/\theta\);
the clean first-six nonorigin labels \(1/2,1,z\)
have \(f\)-values \(1/8,-1/2,z^2(1-z)\), respectively.
All are nonzero, and \(z\notin\{0,1/2,1\}\).
The two actual left-zero grade-four aliases are
\[
 P_0(X)=X^2(X-1)^2,\qquad
 P_1(X)=X(X-1)(X-\tfrac12)(X-z).
\]
Their actual numerical lifts are respectively
\(P_0(c)+(C-1)f\) and \(P_1(c)\) in normalized
units. We retain the notation \(L\) after this dilation.

The exact polynomial identity
\(4P_1=(X-z)P'_0\) gives
\[
        J(P_0+4P_1)=(X-z)P_0.
\]
Both unary lifts vanish at physical row 7 by strictness
and zero first six, so
\[
             (x-z)L(P_0)_7=0,\qquad L(JP_0)_7=0.          \tag{1}
\]
The latter is a genuine model read at grade five,
not an assumption of stage exactness of raw row 7.

Let \(G(X)=6X^2-15X+10\).
The quadratic fit \(T\) for \(JP_0=X^3G(X)/30\)
has interpolation values
\[
        T(1/2)=-2/15,\quad T(1)=1/15,\quad
        T(z)=zG(z)/(30(z-1)).
\]
The exact factorization is
\[
 \frac{XG(X)}{30}+(1-X)T(X)
    =\frac{(X-z)(2X-1)((6z-7)X-7z+8)}{30(z-1)^2}.       \tag{2}
\]
One can check it by the explicit numerator of \(T\)
in the scalar gate and its three interpolation values;
their nodes are distinct.

If \(x=0\), the first equation of (1) forces \(f_7=0\).
If \(x=1/2\), it forces \(f_7=1/8\).
If \(x=1\), the second equation of (1) forces \(f_7=-1/2\).
In all three cases the row of \(L\) would vanish
identically, by duplication of its first-six clean state,
in contradiction to the paid middle Gram.
If \(x=z\) and \(G(z)\ne0\), the second equation again
forces \(f_7=f_6\), the same contradiction.
Thus a repeated edge clock can occur only with \(G(z)=0\)
and \(f_7\ne f_6\).

In the remaining, genuinely new, case
\(x\notin\{0,1/2,1,z\}\),
the first equation gives \(f_7=x^2(1-x)\), and the
second combined with (2) gives \((6z-7)x=7z-8\).
The coefficient \(6z-7\) cannot vanish (its simultaneous
right side would contradict the paid 6).
The exact entire first-middle clock gate is therefore
\[
\begin{array}{ll}
x=z,\quad G(z)=0,\quad f_7\ne f_6 &\text{or}\\
x=(7z-8)/(6z-7),\quad f_7=x^2(1-x),\
                           x\notin\{0,1/2,1,z\}.
\end{array}
\]
The same rule applies to original row 11 in the
reflected normalization from physical 17.

## The half-clock pure square cannot have grade five

The common pure \(r^2\) has grade six.
If \(r^2\in E_5\), then \(r^2\in F_5\): as in the
[common grade-six test](ERK11-TWO-FRONT-CLOCK-NONINVARIANCE.md),
the first origin and \(\ell_0,\ldots,\ell_4\) give
separation on its candidate degree-five model.
At every active noncarrier its nonzero \(r\) can
therefore be cancelled from the \(F_5\) formula,
showing \(r=P_2(c)\) there for one quadratic.
At the repeated clean clock \(\theta\) (rows 4,14),
this equality forces \(r_4=r_{14}\).
Their two calibrated values
\(-\theta/2\) and \(-\beta/(2\lambda)\) give
\(\lambda=\beta/\theta\), so \(r/\theta=\bar r/\beta\)
off carriers.

Put \(a=\theta/\beta\ne0,-1\);
\(a=-1\) is impossible since \(\theta+\beta=1\).
The dimensionless clean shape \(r/\theta\) is
therefore one quadratic in physical \(c\).
At the three distinct sites
\(\theta/2,\theta,(1+\theta)/2\) it has values
\(1/8,-1/2,1/8\).
In normalized left coordinate \(X=c/\theta\)
that quadratic is
\[
    P(X)=\tfrac18+\tfrac{5a}{2}
                (X-\tfrac12)(X-1-\tfrac1{2a}).
\]
The opposite direction has the same formula with
\(a\) replaced by \(1/a\).
At row 6 this polynomial agrees with
\(F(z)=z^2(1-z)\).

If the left middle clock is new, \(P\) also agrees
with \(F\) at \(x=(7z-8)/(6z-7)\).
Thus \(F-P\) is a cubic with leading coefficient \(-1\)
and distinct roots \(1/2,z,x\).
At \(X=1\), its value \(1/2\) gives
\((1-z)(1-x)=-1\).
Combining this with \((6z-7)x=7z-8\) gives \(z+x=-4\).
The \(X^2\) coefficient equality
\(1-5a/2=1/2+z+x\) now gives \(5a=9\).

If the left middle clock is repeated, \(G(z)=0\).
Factoring \(F(z)-P(z)=0\) and cancelling
\(2z-1\ne0\) gives
\(5a(z-1)+2z^2-z-3=0\).
Three times this last expression minus \(G(z)\)
gives \((15a+12)z=15a+19\).
Multiply \(G(z)=0\) by \((15a+12)^2\) and
substitute to obtain
\[
                         75a^2+15a+62=0.
\]
No division by \(15a+12\) was needed.

The right gate imposes one of the same two constraints
on \(1/a\). In characteristic zero the pair is
impossible: two new cases would give \(81=25\);
a new and a repeated case would require
\(75(5/9)^2+15(5/9)+62=2524/27=0\);
two repeats give \(13(a^2-1)=0\) by subtracting the
reciprocal polynomial, and \(a=1\) gives \(152=0\).
The post-premise scalar proof actually works over paid
fields if \(13,19,631\) are additionally nonzero
(the mixed numerator is \(4\cdot631\), the repeated
numerator \(8\cdot19\)). Thus \(r^2\notin E_5\).
This removes a low-order algebraic degeneracy in the
paired-carrier case as well, not the paired case itself.

## A stronger cubic exclusion and literal path test when both sides are new

Suppose both middle boundary gates are new, in
particular whenever the field is ordered:
\(G(z)=6(z-5/4)^2+5/8\ne0\) in that setting.
If \(r^2\) and \(C^3r\) were dependent modulo \(E_5\),
the [proved noninvariance](ERK11-TWO-FRONT-CLOCK-NONINVARIANCE.md)
forces a nonzero coefficient of \(r^2\).
Cancelling \(r\) at live noncarrier nodes then gives
one cubic expression for \(r/\theta\) there; the
same-clock rows 4,14 again give \(\lambda=\beta/\theta\).
The cubic agrees with the preceding quadratic \(P\)
at the same three calibration nodes, so in left units
it is
\[
          P(X)+k(X-\tfrac12)(X-1)(X-1-\tfrac1{2a})
\]
for some \(k\). Equality with \(F\) at \(z,x\)
and removal of \(X-1/2\) yields the quadratic
\[
        2X^2-X-3+5a(X-1)+2k(X-1)(X-1-\tfrac1{2a})
\]
with those two roots. It is nonzero since its
value at 1 is \(-2\); hence it is genuinely
quadratic. The symmetric relation
\(6zx-7(z+x)+8=0\) for the new pair gives, by
Viète, \(5a-9-k/a=0\).
In the reflected direction the cubic coefficient is
\(\bar k=-k/a^3\) and the same relation gives
\(\bar k=(1/a)(5/a-9)\).
Together they force \(a=-1\), impossible.
Thus the two common degree-six vectors have independent
classes modulo \(E_5\) when both boundary clocks are
new (even with only two carrier \(r\)-values).
In particular \(\bar E_6\) has rank 13 or 14
in this branch by the already measured upper bound.

The new middle gate has two exact path implications.
First the literal boundary edges \(A_{7,6}\) and
\(A_{12,11}\) are **zero**.
In the left units, the bush
\(X^3-\tfrac32X^2+\tfrac12X=X(X-1)(X-1/2)\)
vanishes on the first five labels, but is nonzero
at row 6. Its actual primitive at clean row 7,
using the paid cubic residual formula, is
\((x-1)(f_7-F(x))/4=0\). Thus it cannot read row 6.
The reflected proof at original physical 11 for
\(A^\star\) is equivalent (all weights live) to
\(A_{12,11}=0\).

For a complementary inner path test, use unscaled
\(P_0=X^2(X-\theta)^2,\ Q_0=(1-X)^2(X-\theta)^2\).
Their anchored lifts \(v=L(P_0), w=R(Q_0)\) have
actual grade four and are zero through row 7 and
from row 11 onward, respectively, by the new gates.
The paid product \(b((A^2v)\odot w)\) is
\[
 \int_0^1 (J^2P_0)(X)Q_0(X)\,dX
   =\frac{660(\theta-\tfrac12)^4+
                       55(\theta-\tfrac12)^2+1}{831600}.
\]
For example \(J^2P_0=X^6/30-\theta X^5/10+\theta^2X^4/12\);
expand against \(Q_0\) and use ordinary Beta moments.
Only middle physical row 10 contributes, with its
unique path \(A_{10,9}A_{9,8}v_8\) and \(w_{10}\).
If that explicit integral is nonzero (always in an
ordered field), both those path edges and \(v_8,w_{10}\)
are nonzero.

Also \(G(z),G(\bar z)\ne0\) over ordered fields.
At row 8 the actual \(A v\) is zero because \(v_7=0\);
so if \(c_8=c_6\) the same interpolation of \(JP_0\)
as above would force \(r_8=r_6\) and hence \(v_8=0\).
This is impossible. The exact identity
\(A(v+4L(P_1))=(C-c_6)v\), now in ordinary units,
at row 8 then gives
\(4A_{8,7}P_1(c_7)=(c_8-c_6)v_8\ne0\).
Here \(P_1=X(X-\theta)(X-\theta/2)(X-c_6)\)
and the identity follows from \(4P_1=(X-c_6)P'_0\).
This forces \(A_{8,7}\ne0\), and the reverse proof
forces \(A_{11,10}\ne0\).
Thus the ordered-field branch has all four
inner adjacent edges of the middle five live,
but the two adjacent boundary edges absent.
These are literal support constraints, not a claimed
contradiction to the ordinary stage bound.

ERK11MiddleDefectGate.lean checks the exact scalar
factorization, normalized opposing-quadratic cases,
the opposite cubic coefficient test, and the centered
nonzero path numerator. The actual rooted, grade,
orthogonal and chronological bridges are mathematical
proofs in this note. No full 17-stage exclusion is claimed.
