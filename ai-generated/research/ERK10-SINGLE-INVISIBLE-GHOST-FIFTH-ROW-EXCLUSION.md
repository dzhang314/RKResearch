# The fifth physical row rules out last ghost tap 11 in one-clock ERK10

Use the [single invisible ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md)
for a hypothetical 14-stage strict explicit rooted-order-ten tableau
over a characteristic-zero field. There is exactly one zero output
weight, every quadratic defect is invisible, its physical stage is 2,
its pure indicator is \(e=e_2\), and \(r=Ae\) is the ghost column.
Assume all nonzero \(r\)-values occur at the one clock \(t=c_3\).
All indices below are original one-based physical stage numbers.

**Result.** The latest nonzero outgoing tap of the ghost is at
physical **12 or 13**. The [prior late cutoff](ERK10-SINGLE-INVISIBLE-GHOST-LATE-CUTOFF.md)
excluded taps through 10. This note excludes 11, using only an
actual forward grade-four linear relation and exact duplicate
incoming lists. More generally, when the reduced reverse rank-two
room is clock-invariant, its second eigenline must already be
visible in one of physical rows 4 or 5, as specified below.
No ordinary reverse order is presumed; the 12/13 and other ghost
cases remain open.

## A reusable early-election condition

Continue to use \(I\) for the live coordinates,
\(W_i=B_I^{-1}(E_{8-i}^{\perp}|_I)\), and the literal \(A^\vee\)
of the invisible-ghost ledger. The \(W_i\) have ranks \(i\),
\(r|_I\in W_2\), \(W_3\) is not clock-invariant, and the
old pure spaces project into the corresponding linear rooms.
Suppose \(W_2\) is clock-invariant. As in the late-cutoff
argument, \(f_3=2,f_4=4\): if \(f_3=3\), its live projection
fills \(W_2\); together with the pure one-dimensional ghost
kernel this would make \(F_3\) invariant and the reviewed
outgoing gain would force \(f_4\ge5\). Then \(F_3=\langle e,r\rangle\)
itself is invariant (\(Cr=tr\)), so it instead pays \(f_4\ge4\).
The paid projection \(F_4|_I=W_3\) is exact by rank.

Choose an independent \(s\in W_2\) normalized by \(s_3=0\);
this is always possible because \(r_3\ne0\), and defines its
line uniquely. It is a \(C\)-eigenvector: \(Cs\in W_2\), and
its \(r\)-coefficient in the basis \(r,s\) is zero by evaluation
at physical 3. Extend \(s\) by zero on the single ghost.
For any fourth independent lift \(w\) with
\[
                         F_4=\langle e,r,s,w\rangle ,
\]
the following calculation shows **at least one of \(s_4,s_5\)
is nonzero**. The calculation has no dependence on the clock
of the eigenline or on late reversal.

## Literal local fourth and fifth reads

Assume instead \(s_4=s_5=0\). Rescale all forward \(A,c\) by
\(1/t\) so \(t=1\); nonzero weights, strictness, root grade
spans and literal duplicate statuses are unchanged. This is
only a forward local rescaling, not a new exact reversed
order condition. Use \(\theta=c_2\ne0\) in the rescaled units.
The actual \(r_3=A_{32}\) satisfies \(2\theta r_3=1\).

The paid cubic defect is
\[
     Ac^2-c^3/3=-\theta^3 e/3+(\theta^2-2\theta/3)r .
\]
The [prior literal fourth-row contact](ERK10-SINGLE-INVISIBLE-GHOST-LATE-CUTOFF.md)
uses only \(F_3=\langle e,r\rangle\) and the one-clock assumption:
the clock of row 4 cannot be 0 or 1 without a literal duplicate,
so \(r_4=0,\ c_4=3/2\). The absorbed quadratic and cubic
conditions give row 4 exactly
\[
               (A_{41},A_{42},A_{43})=(3/8,0,9/8).
\]
Let \(q=Ac^3-c^4/4\in F_4\) be the true quartic defect.
At row 4, \(q_4=-9/64\) while \((Ar)_4=(9/8)r_3\ne0\).
As all \(e,r,s\) vanish there, \(w_4\ne0\), and the
specific grade-four vector
\[
                         Q=q+\frac{Ar}{8r_3}
\]
has no \(w\)-coefficient. So \(Q\in\langle e,r,s\rangle\).
At row 3 we have \(e_3=s_3=0,\ (Ar)_3=0\), and
\(q_3=\theta^3r_3-1/4\); thus its \(r\)-coefficient is
\(\theta^3-\theta/2\). At row 5 we also have
\(e_5=s_5=0\), so \(Q_5=(\theta^3-\theta/2)r_5\).

Put \(y=c_5,\ a=A_{53},\ d=A_{54}\).
The actual ghost read there is \(r_5=A_{52}\), and
\((Ar)_5=a r_3\) since \(r_4=0\).
The genuine quadratic defect is zero at the live row 5,
the cubic defect is as above, and the calibrated
quartic relation is \(Q_5=(\theta^3-\theta/2)r_5\).
They give respectively
\[
\begin{aligned}
 \theta r_5+a+\tfrac32 d &= y^2/2,\\
 \tfrac23\theta r_5+a+\tfrac94 d &= y^3/3,\\
 \tfrac12\theta r_5+\tfrac98 a+\tfrac{27}8 d &= y^4/4 .
\end{aligned}
\]
Eliminating only the two taps gives
\[
                        2\theta r_5=y^2(2y-3)^2 .
\]
There are three possible actual incoming lists; all are
literal duplicates.
* If \(r_5=0\) and \(y=0\), the first two equations give
  \(a=d=0\); \(A_{52}=0\) and the row sum gives \(A_{51}=0\).
  Thus the whole row is zero, a duplicate of origin 1.
* If \(r_5=0\) and \(y=3/2\), the first two give
  \(a=9/8,d=0\), and the row sum gives \(A_{51}=3/8\).
  This is the literal whole incoming list of row 4
  padded at physical column 4, since \(A_{52}=0\).
* Otherwise \(r_5\ne0\) and the one-clock hypothesis
  gives \(y=1\). The cleared equation gives
  \(r_5=1/(2\theta)=r_3\).
  The first two then give \(a=d=0\),
  and the row sum fixes \(A_{51}=1-r_3=A_{31}\).
  Thus row 5 equals row 3 padded at physical columns 3
  and 4. The same incoming calculation applies if one
  directly takes the \(y=1\) branch of the scalar disjunction.

All later columns in each list vanish by strictness.
A literal duplicate can be merged, preserving rooted
order ten on thirteen stages, contradicting the independent
fourteen-stage floor. Hence the required early election
\((s_4,s_5)\ne(0,0)\) follows.

## Application to last 11 and a necessary late-12 guard

If the last nonzero tap is 11, the prior late-cutoff theorem
gives \(W_2=\langle r,z\rangle\), with a nonzero pure
\(z=e_{12}/b_{12}-e_{13}/b_{13}\) supported only on the late
opposing pair. In particular \(W_2\) is clock-invariant
and the normalized second line \(s\) is \(Kz\).
It has \(s_4=s_5=0\), contradicting the local exit.
Since the last tap cannot be 14 (terminal point exactness
through grade four), the only remaining physical choices
are 12 and 13.

If the last tap is 12, \(r_{13}=0\) but \(u_{13}\ne0\)
for the actual reduced reverse quadratic defect \(u\).
Thus \(u,r\) are independent, and \(W_2=\langle u,r\rangle\)
is clock-invariant because \(Cu\in W_2\) and \(Cr=tr\).
The normalized \(s=u-(u_3/r_3)r\) still has \(s_{13}=u_{13}\ne0\).
It is a single-clock eigenvector; the early-election
condition therefore forces **\(c_{13}=c_4\) or \(c_{13}=c_5\)**,
with the relevant \(s\)-entry nonzero. This is a further
necessary condition, not a late-12 exclusion. At last 13
the same local argument applies whenever \(W_2\) is invariant;
it does not assume that invariance in the dependent reverse case.

[ERK10SingleGhostFifthRowGate.lean](../lean/RKCert/ReviewedNative/ERK10SingleGhostFifthRowGate.lean)
kernel-checks the quartic calibration, denominator-free
cleared relation and all complete incoming-list matches.
The actual grade, literal prefix and duplicate merging
bridges are the mathematical argument above. No unrestricted
change to ERK10 14–15 is asserted.
