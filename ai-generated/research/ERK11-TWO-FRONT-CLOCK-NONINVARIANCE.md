# The four-carrier midpoint cannot be clock invariant

Continue the [two-ended four-carrier half-clock branch](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md)
with the literal [five-tap front](ERK11-FOUR-CARRIER-FIVE-TAP.md).
In particular both methods are order eleven, their actual \(E_5,F_5\)
agree, and the first eleven in each direction are literally dense.
The only carriers are physical 2,5,13,16, at one clock
\(\theta\ne0,1\). Write \(s\) for their indicator and \(r=As\),
\(\bar r=A^\star s=\lambda(r-r_{16}s)\) with \(\lambda\ne0\),
\(A^\star=B^{-1}A^\mathsf T B\). The actual pure spaces are
\[
      F_4=\langle s,r,Cr\rangle,\qquad
      F_5=\langle s,sr,r,Cr,C^2r\rangle .
\]
Products of vectors in these notes are coordinatewise unless
an operator is shown. The deductions after these premises are
over any field paying \(11!\), without ordering.

**Result.** \(F_5\) is not clock invariant. Thus at least four
distinct noncarrier clock labels have nonzero \(r\). In the
four-distinct carrier-state branch this also gives two independent
common grade-six directions, so the reversed numerical \(E_6\)
has dimension 13 or 14. The work does not exclude the full
four-carrier branch.

## Exact local provider obstruction in either direction

In normalized front units \(c_2=1,\ c_3=1/2,\ c_4=c_5=1\),
\(z=c_6\notin\{0,1/2,1\}\), and the clean \(f=As\) data are
\(f_3=1/8,\ f_4=-1/2,\ f_6=z^2(1-z)\).
There are two actual grade-four formal polynomial aliases
on the first six:
\[
       P_0(X)=X^2(X-1)^2,\qquad
       P_1(X)=X(X-1)(X-\tfrac12)(X-z).
\]
For \(P_0\), the numerical vector is
\(P_0(c)+(C-1)f\). This is a legitimate grade-four pair
since \(f\) is pure of grade three, and the displayed
values give zero at every one of the six physical sites.
For \(P_1\), the scalar bush evaluation already vanishes
at the four front labels. The two aliases are independent
since \(P_1(1/2)=0\), whereas \(P_0(1/2)=1/16\).

If the first-eleven \(F_5\) is clock invariant, its
annihilator decomposes over physical clock blocks.
Each block has dimension at most one, since a row in
it killing the constant also annihilates the six
polynomial clock columns and the five pure directions,
hence is the zero row on full \(K^{11}\).
Thus there are six normalized clock-local reads,
including the literal origin at clock 0.
At any nonzero label \(x\), the normalized row
\(\lambda_x\) is exact evaluation at \(x\) through
grade five (its action on the constant determines
the clock evaluation coefficient).
The actual \(\lambda_x A\) is supported before the
last position of \(\lambda_x\) and integrates through
grade four to \(x\).
Dividing the tableau and the output by \(x\) gives
the usual ordinary order-five method on its preceding
physical rows. The paid RK5 minimum six follows, e.g.,
from the reverse count in
[01-PAID-GRADE-FIVE-SURPLUS](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md).
The five nonzero clock-local reads must therefore end
at positions 7,8,9,10,11 in order. The first gives a
true ordinary order-five provider on the literal first
six after dilation by a nonzero \(x\).

An exact order-five provider to \(x\) on the first six
must kill both alias models. Since \(x\ne0\),
\(I_xP_0=I_xP_1=0\) implies
\[
\begin{aligned}
       G(x)&=0,\qquad G(X)=6X^2-15X+10,\\
 H(x,z)&=0,\qquad
       H(x,z)=24x^3-(30z+45)x^2+(60z+20)x-30z .
\end{aligned}
\]
These follow from \(I_xP_0=x^3G(x)/30\) and
\(I_xP_1=x^2H(x,z)/120\). The exact identity
\[
        2H(x,z)-(8x+5-10z)G(x)
                      =5((7-6z)x+8z-10)
\]
gives \((7-6z)x=10-8z\).
Multiply \(G(x)=0\) by \((7-6z)^2\) and substitute:
the resulting polynomial in \(z\) is \(4G(z)=0\).
No division by \(7-6z\) was used.
It is in fact nonzero: if also \(10-8z=0\),
a linear combination gives \(2=0\).
Consequently \((7-6z)(x-z)=G(z)=0\), so the earliest
possible provider clock is exactly \(x=z\), with
\(G(z)=0\). This statement is also a necessary
condition if just one first-eleven pure space is
invariant, without assuming global invariance.

## Simultaneous global invariance is impossible

The span of \(s,sr\) is clock invariant (common carrier
clock). Thus \(CF_5\subset F_5\) is equivalent to at
most three distinct **noncarrier** labels on which
\(r\ne0\). Indeed, invariance requires \(C^3r\in F_5\),
so the offcarrier values give a monic cubic hull
annihilating those clock labels. Conversely if at
most three such labels occur, one can take their
cubic hull; it also includes \(\theta\), since row 4
is active there, hence it annihilates \(r\) globally.

The three offcarrier labels
\(\theta/2,\theta,(1+\theta)/2\) are distinct and active
at physical rows 3,4,15, respectively. This is measured
from the two actual normalized fronts and
\(\bar r=\lambda r\) off carriers.
The active clock \(c_6\) is different from \(0,\theta/2,\theta\);
the active \(c_{12}\) is different from \(1,\theta,(1+\theta)/2\)
by the same reversed-front facts.
In the putative three-label invariant case these force
\[
 c_6=(1+\theta)/2,\qquad c_{12}=\theta/2 .
\]
Thus the normalized sixth clocks \(z=c_6/\theta\) and
\(\bar z=(1-c_{12})/(1-\theta)\) satisfy
\[
        z=\frac{1+\theta}{2\theta},\qquad
        \bar z=\frac{4z-3}{4(z-1)} .
\]
Invariance under \(C\) implies invariance under \(1-C\);
thus the proved first-provider constraints apply on both
actual prefixes, giving \(G(z)=G(\bar z)=0\).
The latter after multiplying by \(16(z-1)^2\) is
\(2J(z)=0\), with \(J(z)=8z^2-22z+17\).
The explicit Bézout identity
\[
              (22-24z)G(z)+(18z-12)J(z)=16
\]
contradicts \(11!\ne0\).
No square-root or ordering argument is used.

## A measured reverse numerical rank consequence

The actual \(C^3r\) is a grade-six pure vector in both
directions, since the common grade-three pure \(r\) is
followed by three clock factors, equally expressible
in the reflected clock. By the preceding result it is
not in \(F_5\).
Moreover \(F_6\cap E_5=F_5\): if an actual grade-six
pure vector also has a degree-five model \(P\), then
\(P(0)=0\) and the original five paid shifts \(0,\ldots,4\)
give \(\ell_m(P)=0\). The anchored weight-\(X\)
Gram through degree four is nonsingular, so \(P=0\).

If the four carrier \(r\)-values are distinct, the
common grade-six vector \(r^{\odot2}\) has a genuinely
quadratic carrier restriction. Since \(E_5\) restricts
affinely and \(C^3r\) is affine on those four sites,
any relation modulo \(E_5\) between \(r^{\odot2}\) and
\(C^3r\) would first give zero coefficient of
\(r^{\odot2}\); the remaining term is nonzero modulo
\(E_5\) by the preceding paragraph.
Thus their independent classes force
\(\dim \bar E_6\ge13\).
They also force that bound in the paired-value case
if \(r_4\ne r_{14}\): at those clean same-clock sites,
dividing a hypothetical relation by the respective
nonzero \(r_i\) gives different quadratic values,
again forcing its coefficient to vanish.
The reverse bound \(\bar E_6\subset E_6\) follows
by pairing with the common actual pure \(F_4\);
indeed \(E_6=F_4^{\perp_B}\) by the measured rank.
So the reverse numerical grade-six rank in these
cases is 13 or 14, without presuming it equals 14.

ERK11TwoFrontGramGate.lean verifies the provider
elimination (including its same-clock conclusion),
the reflection polynomial, and the exact Bézout
unit. The restricted rooted space and last-support
transfers are mathematical in this note, not a new
native ERK11 stage theorem.
