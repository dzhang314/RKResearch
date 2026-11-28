# Two-front grade-five chart for the sole-late-carrier ERK11 case

**Scope.** Continue the maximal rank-two, all-early-live half-clock
branch of [the endpoint reduction](ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md),
with physical 16 its *sole* late quadratic carrier. All 17 weights are
live, the literal first eleven have full numerical \(E_5\), and the
full forward grade-five span has rank eleven. We use the actual
weighted transpose, which is order **ten**: no reverse order eleven
or reverse dense first eleven is assumed. The field is characteristic
zero, with ordering needed only for the later real central test.

There are either two or three carriers in total. In the latter case
their physical positions are \(2,9,16\).
Both fronts have an exact five-row clean-clock repeat, an independently
measured sixth pure pivot, and dual grade-five lifts with invertible
literal five-row mixed Gram. A local boundary either repeats its
sixth clock at a different response or is active at a genuinely
new clock. The reflected first eleven are dense through grade five, although
full reverse order eleven has not been assumed or earned. With three
carriers the central site imposes additional exact coupled moment/Gram
conditions; see the separate central exclusion. The two-total-carrier
case and repeated-boundary central cases are not closed by this packet.
No ordinary stage interval changes.

## 1. Clock and pure data at both ends

Let \(s\) be the carrier indicator and \(r=As\), and put
\(B=\operatorname{diag}(b_i)\), \(A^\star=B^{-1}A^\mathsf{T}B\).
The [sole-late-carrier data](ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md#sole-late-carrier-at-16-exact-localization-of-the-second-seed)
give a common carrier clock \(\theta=c_{16}\ne0,1\), \(r=0\)
on *all* carriers, nonzero off-carrier responses at physical
12,14,15, and at most two early carriers. The response at
physical 13 need not be assumed zero. The first carrier is 2: otherwise
the all-zero-clock initial rows would duplicate the origin in the
full literal first-eleven \(E_5\). The fourth-row argument of
[the weighted transpose note](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md#four-quadratic-carriers-in-the-half-clock-two-carrier-branch)
uses only the actual common grade-three space, carrier clock and
first-eleven independence, and excludes carriers at rows 3 and 4.
The fifth row cannot be a carrier either: its response would be
zero, and the first two clock moments would give zero reads of the
two distinct nonzero clean donor clocks. Its remaining weight at
the origin would make it duplicate row 2. The nonzero and distinct
clock guards follow from the same first-four calculation below.

The [adjoint-pure duality](ERK11-ADJOINT-PURE-DUALITY.md#if-p12-and-16-is-the-sole-late-carrier)
gives \(A^\star s=\lambda r\) for \(\lambda\ne0\). The
[order-ten reversal theorem](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md)
gives a reverse rank-five pure space
\(\bar F_5=E_5^{\perp_B}\cap\{x_{17}=0\}\),
and common forward and reverse spaces through grade four.
In either orientation, normalize the first carrier clock to 1
by scaling the matrix and clock by its nonzero clock. Below the
normalized stage clock is \(c\), the matrix is \(A\) in that
direction, and \(f=As\) is the normalized response. Both orientations
have exactly \(F_3=\langle s,f\rangle,\ F_4=\langle s,f,Cf\rangle\),
where \(C=\operatorname{diag}(c)\). In particular, the reverse
stage-order-two defect is \(-s/2\) in its normalized variable,
as it lies on the same line and its first-carrier value is \(-1/2\).

Write \(N=c_3\) and \(T=c_4\) in one orientation, numbering from
that origin. The standard first-four clock calculation is
\[
 f_3=N^2/2,\quad f_4=T^2(3N-2T)/(2N),\quad
 A_{43}=T^2(T-N)/N^2,\quad
 Ac^2-c^3/3=-s/3+(1-2N/3)f.
\]
If \(N=0\), the third row is the origin; \(T=0,N\) likewise
makes the fourth row a raw repeat. In the forward case these are
excluded by prefix rank; in the reverse case the normal form already
gives \(N=1/(2q),T=1/q\) with \(q\ne0\). If \(3N-2T=0\),
then \(f_4=0\); the actual grade-four identity \(Af\in F_4\),
with zero readings on rows 2 and 3, would force \(Af_4=0\),
whereas \(A_{43} f_3\ne0\). Thus this branch is absent.

The actual clean fifth row of the
[four-row head calculation](erk-single-quadratic-defect/SINGLE-SECOND-ROW-DEFECT-SIX-LOWER-BOUND.md#case-1-the-fourth-row-reads-the-second-coordinate)
forces \(T=2N,c_5=T,f_5\ne f_4\) once literal repeats are
excluded. Its local Case 1 equations use only the grade-four spans,
not the dimensional assumption of that note at grade five, and only
the initial carrier column is present through this row. In the
reverse orientation the same clean plateau follows here from the
[actual grade-six eigenmode](ERK11-TWO-GENERATOR-ENDPOINT-TAIL.md)
\(w\), supported at physical 13,14 once its terminal value has been
removed: its other possible same-clock coordinate 16 is killed by
the paid product with the sole late defect. This mode satisfies
\(bw=1\), and the paid product \(b(wr)=0\) has grade \(6+3\).
If \(r_{13}=r_{14}\), that product would equal \(r_{14}bw\ne0\).
Thus the two plateau responses are distinct, as required. Neither
a zero response at 13 nor an individual point atom there is needed.
Consequently in both directions
\[
 T=2N,\quad f_4=-2N^2,\quad Af=(N-C)f,\quad
 Ac^3-c^4/4=-s/4+(1-N^2+(N/2)C)f.                         \tag{1}
\]
The additional exact pure row is \(g=A(C-NI)f\) (grade five).
It vanishes through row 4 and
\[
      g_5=-N^2(f_5+2N^2)/3\ne0 .
\]
Indeed \(A_{54}=(f_5+2N^2)/(6N)\) from the first two
clock moments, and only its column 4 contributes.

Set \(P_3=X(X-N)(X-T)\) and \(V=A(P_3(c)-P_3(1)s)\).
This actual grade-four vector has model \(P_0=X^2(X-T)^2/4\).
Using (1) its exact reading everywhere is
\[
 V=P_0(c)-P_0(1)s+(N/2)(C-T I)f .                         \tag{2}
\]
It is zero through row 6 by strictness: its input is zero on
the first five. If \(v=(C-NI)(C-TI)f\) vanished globally, an
earliest clean clock outside \(0,N,T\) would have zero response.
The input of \(V\) is zero at all its predecessors, including
all carriers, but (2) would then have nonzero value there.
Hence all clean clocks would lie in \(0,N,T\), with all
carriers at 1, incompatible with paid scalar moments (the
square of their degree-at-most-four hull suffices). Thus \(v\ne0\).
Together \(s,f,Cf,C^2 f,g\) are independent: test rows 2,3,4,5
first and then \(v\ne0\). They span the actual rank-five pure
space in each direction, independently of equality of those spaces.

## 2. The sixth clock and the seventh boundary dichotomy

Write \(e=Ac^4-c^5/5\) as \(\alpha s+\rho(C) f+\eta g\).
On the first six physical rows, the donor relation
\[
 c^4-3N c^3+2N^2c^2=(1-N)(1-T)s
\]
can be applied under \(A\): it is true through row 5. Thus the
local expression for \(e\) there is
\(U_4(c)+\alpha' s+D(C)f\), with
\(U_4(X)=3N X^4/4-2N^2 X^3/3-X^5/5\).
Here \(\alpha'\) is a scalar and \(D\) a polynomial, both fixed
by (1); their actual values are not needed. Comparing at row 4 gives
\(\rho(T)=D(T)+U_4(T)/f_4=D(T)-2N^3/15\).
Subtract the row-4 identity from row 5 and use \(g_5\ne0\);
this gives \(\eta=-2N/5\ne0\). At any carrier, \(e=-1/5+\eta g\),
where its \(s\)-coefficient is measured at row 2.

This proves row 6 in the forward orientation must be clean
with \(z=c_6\notin\{0,N,T\}\). A carrier there would have
\(Ac^4=0\) by the same donor relation and its common low
carrier data, so \(g_6=0\) and it would duplicate row 2 on
all \(E_5\). At clean clock 0 or \(N\), (2) forces respectively
\(f_6=0\) or \(N^2/2\), and the grade-five residual formula
fixes \(g_6\) to that of the old row with that clock.
At \(T\) it fixes \(g_6\) affine-linearly in \(f_6\), making
the new \(E_5\) row dependent on rows 4,5. Every case contradicts
full first-eleven \(E_5\). In the reverse orientation the
already proved normal form supplies a clean new sixth clock
\(z=t/q\notin\{0,N,T\}\). The vanishing of \(V\) at row 6
now gives in each orientation
\[
                 f_6=z^2(T-z)/(2N)\ne0.                    \tag{3}
\]
The five pure columns already span the zero-origin vectors
on the first six: \(v\) has nonzero sixth read, and \(g\) has
nonzero fifth read while \(v\) is zero through five.

Put \(W=(C-zI)(P_3(c)-P_3(1)s)\), an actual grade-four
vector zero through the first six. Its model is \((X-z)P_3\).
Since \(P_3=P'_0\), the two actual grade-five vectors
\(A(V+W)\) and \((C-zI)V\) have the same model.
Their difference is pure and zero throughout the first six,
so it is literally zero by the measured pure rank there.
The seventh stage therefore satisfies
\[
             A V|_7=0,\qquad (c_7-z)V_7=0 .                \tag{4}
\]
No reverse order eleven is consumed.

Let \(J P_0(X)=\int_0^X P_0(t)\,dt\). As in the residual
comparison, \(AV\) has model \(J P_0\). On a carrier its
read equals \((2N/5)g\): use the first-carrier read to
calibrate the \(s\)-coefficient, and subtract its zero
rows 4 and 5 to get the \(g\)-coefficient from
\(J P_0(T)=4N^5/15,\ f_4=-2N^2\). Since the fifth response
is distinct no division loses a branch.

## 3. Exact mixed Gram without reverse order eleven

In physical forward model variables define \(L(P)\) as
the grade-five vector with model \(P\), zero on the first six,
for \(\deg P\le5,\ P(0)=0\). Define the reverse \(R(Q)\) with
model \(Q\), zero on the last six, for \(Q(1)=0\).
Both exist uniquely by first-six pure invertibility in the
respective orientations. The reverse pure component is in
\(E_5^{\perp_B}\), so pairing it with \(L(P)\) gives zero.
Its clock-polynomial component in \(1-c\) is exactly \(Q(c)\).
The ordinary order-eleven product of two actual degree-five
pairs therefore gives
\[
           \sum_{i=7}^{11} b_i L(P)_i R(Q)_i
                         =\int_0^1 P(X)Q(X)\,dX .          \tag{5}
\]
This proves both middle read matrices invertible: after
extracting the endpoint factors the model Gram is the
nonsingular weight-\(X(1-X)\) Gram through degree four.
It also earns reverse density: the reverse first-six projection of
\(ar E_5\) has rank six, and its kernel is the five-dimensional
space of the \(R(Q)\). Their restrictions to the next five coordinates
are invertible by (5). Therefore the reverse first eleven have full
numerical \(ar E_5\), with their usual grade-five model decoder.

In normalized local variables a left or reversed read
on a noncarrier has the form
\(P(c_i)+f_i S_P(c_i)+\gamma_P g_i\), where \(S_P\)
is quadratic. At any carrier the constant polynomial value
is removed by the \(s\)-correction already measured at the
first carrier, and \(f=0\). Its anchored row is therefore
exactly a multiple of evaluation at \(T\), since subtracting
the zero equations at 4 and 5 gives
\(\gamma_P=3P(T)/(2N^4)\). If this carrier is in the middle,
the multiple is nonzero by (5). In particular the coefficient
\(g_i\) on a middle carrier is nonzero in **both** orientations.

A third carrier cannot be physical 7 or 11: (4) at that
orientation's seventh stage would give \(g_i=0\), a zero
row of the mixed Gram. Thus it lies at 8,9,10.
The remaining seventh-stage noncarrier possibilities are:

* For \(x=c_7\ne z\), (2), (4) imply \(V_7=0\).
  At 0 or \(N\), the response matches the origin or row 3;
  \(AV|_7=0\) fixes the \(g\)-value to the same old value
  because its \(g\)-coefficient is nonzero. At \(T\),
  the same equation fixes \(g\) affinely in \(f\) on the
  existing rows 4,5. Each is dependence on the first six
  grade-five stage readings, hence the anchored seventh
  read is zero. These cases contradict (5).
  Thus \(x\notin\{0,N,T,z\}\), \(V_7=0\), and
  \(f_7=x^2(T-x)/(2N)\ne0\).
* For \(x=z\), the independent seventh read requires
  \(f_7\ne f_6\): equal response would fix the same
  \(g\)-value by \(AV|_7=0\). In this case (2) gives
  \(V_7\ne0\), without requiring \(f_7\ne0\).

The analogous statement holds at physical 11. If a carrier
were at 8, its nonzero \(AV\) would force \(V_7\ne0\): the
left boundary must repeat the sixth clock \(z\). But then the
factor \(C-zI\) makes \(W_7=0\), so \(AW\) vanishes at 8.
Its model is \(J[(X-z)P_3]=(X-z)P_0-JP_0\), whose value at
\(T\) is \(-4N^5/15\ne0\). The nonzero evaluation-on-\(T\)
carrier row requires a nonzero \(AW\) value, contradiction.
The reflected result excludes 10. Thus a third carrier can
only be physical 9, without an ordering requirement.

On each side take \(M=V\) for a new seventh clock, and \(M=W\)
for a repeated seventh clock. Each actual \(M\) vanishes through
its seventh row and at the central carrier, and the model of
\(AM\) at \(T\) is respectively \(+4N^5/15\) or \(-4N^5/15\).
Thus \(AM\) is nonzero at that carrier in both orientations,
forcing literal edges \(A_{98},A_{10,9}\ne0\) and the nonzero
values \(M_L|_8,M_R|_{10}\). The two-new case uses the squared
clock models \(P_0\) at both fronts in the companion central
exclusion.

Finally if there are exactly two total carriers, their
ordinary weights are opposite by \(b(s)=0\). The actual
degree-two product with any \(x\in E_8\) gives
\(b(s x)=0\), so \(x_2=x_{16}\). This is exact equality
on the whole \(E_8\), not a proposed deletion of a stage.

The exact fifth-row, primitive, and carrier evaluation coefficient
arithmetic is in ERK11SoleLateFrontGate.lean. The full tableau and
cross Gram derivations above are mathematical proofs.
