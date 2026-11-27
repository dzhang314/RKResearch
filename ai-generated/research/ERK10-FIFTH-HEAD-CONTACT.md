# A genuine grade-four contact closes the shared-dormant eight-clock ERK10 chart

Work over any characteristic-zero field in the
[all-live two-carrier equality ledger](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md).
The only quadratic-defect carriers are physical rows 2 and 13,
at a common clock \(\theta\ne0,1\); their indicator is \(s\).
Write \(r=As\). The actual lower pure flags are
\[
          F_2=Ks,\quad F_3=\langle s,r\rangle,\quad
          F_4=\langle s,r,Cr\rangle .
\]
The full all-live weighted reversal has the same flags through
grade four and takes \(r\) to a nonzero multiple of itself,
read in reverse order. All 14-stage candidates in this scope
have distinct full rooted physical states, because a literal
duplicate can be merged, contradicting the independent 14-stage
lower bound.

**Result.** The literal clocks necessarily satisfy
\(c_5=c_4,\ c_{10}=c_{11}\), and the taps between each pair
are nonzero. This uses only genuine grade-four tests, not a
flatness assumption on \(F_5\). Consequently:
* If every middle row is \(r\)-active, nine and ten distinct
  active clocks are impossible. In the eight-label case with
  ten active rows, exactly the two indicated pairs repeat, at
  different clocks, and both have unequal active amplitudes.
  This eight-label case remains open.
* If there are exactly eight active rows at eight distinct
  clocks, the two middle dormant rows are physical **5 and 10**.
  Their point-exact incoming reads are literal Simpson rows on
  their nearby three original clocks, as specified below.
* In particular the two-dormant shared-clock chart is
  **excluded** by combining the fifth-row contact with the
  independent fixed-Lobatto norm.

No unrestricted 15-stage lower bound is asserted.

## The local Q calibration, with no fifth-grade flatness

Temporarily rescale \(A,c\) by \(\theta^{-1}\), so the
carrier clock is 1. Such rescaling preserves the pure spaces
and all strict duplicate tests; formal primitives in these
local coordinates are still the same \(J\).
Set \(t=c_3\), \(x=c_4\), \(y=c_5\) in these units.
Rows 3 and 4 are the first two \(r\)-active rows with
distinct nonzero clocks, by the existing grade-four entrance
proof. It gives
\[
 r_3=t^2/2,\qquad r_4=x^2(3t-2x)/(2t),\qquad
 A_{43}=x^2(x-t)/t^2,\qquad
 Ar=\gamma(C-t)r,\quad \gamma=t/(3t-2x).
\]
The denominators are nonzero: \(t\ne0,\ x\ne0,t\),
and \(r_4\ne0\). Also the calibrated cubic defect is
\(Ac^2-c^3/3=-s/3+(1-2t/3)r\).
Write \(w=-r/2\), so \(w_3=-t^2/4\) and
\(4t w_4=x^2(2x-3t)\).

Use the quartic \(Q(X)=X^2(X-y)(2X-3t)\).
It vanishes at zero and its derivative has degree three,
so the actual defect
\[
           A Q'(c)-Q(c)=q\,s+(a+b C)w
\]
belongs to the actual \(F_4\). This is the **only** source
of the local contact: no \(F_5\) formula is used.
Row 2 calibrates \(q=-Q(1)\), because \(Q'(0)=0\).
Also \(Q'(t)=4t w_3\) and
\(Q(t)=4t(t-y)w_3,\ Q(x)=4t(x-y)w_4\).
At rows 3 and 4 the term on the carrier input contributes
\(-2Q'(1)w\). The only extra predecessor contribution at 4
is from row 3, where \(Q'(t)=4t w_3\), so it equals
\(4t(Aw)_4\).
The two distinct clock evaluations determine
\[
          a+b X=-2Q'(1)+4t\gamma(X-t)+4t(y-X).
\]
At physical row 5, which is not a carrier, \(Q(c_5)=0\).
Subtracting \(4tAw\) from the calibrated equation and
then cancelling the known carrier contribution leaves only
the literal read from the immediately preceding row 4:
\[
        A_{54}\,[Q'(x)-4t w_4]
            =6 A_{54} x(x-t)(x-y)=0 .
\]

Here is the exact zero-tap check. If \(A_{54}=0\), denote
\(a=A_{52},b=A_{53}\). The genuine quadratic and cubic
equations and \(Ar=\gamma(C-t)r\) give
\[
 2(a+tb)=y^2,\qquad 2ta+3t^2b=y^3,\qquad
 (3t-2x)t^2b=2t(y-t)a .
\]
Thus \(t^2 b=y^2(y-t)\) and \(2ta=y^2(3t-2y)\), and the
third relation forces \(y^2(y-t)(y-x)=0\).
For \(y=0,t,x\), the two solved entries \(a,b\) and the
row sum make the entire physical row 5 duplicate row
1, 3, or 4, respectively. In the latter two cases its
incoming list is literally the earlier list padded with
zeros: at \(y=t\) the read on row 3 is zero, and at
\(y=x\) the read on row 4 is zero by hypothesis.
Such a duplicate is removable by combining its output
coefficient and redirecting each later tap to the earlier
stage. Induction in the true rooted recursion then
preserves every test, which contradicts the independent
14-stage floor. Therefore \(A_{54}\ne0\), and the quartic
gate gives \(y=x\). This argument is the local contact
from the dependent case of the
[paid grade-five surplus](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md),
isolated **before** its final use of \(F_5\)-flatness.
All bridge steps here are paid at grade at most four.

In the reversed chart the same argument gives
\(c_{10}=c_{11}\) and \(A^\star_{10,11}\ne0\); with every
weight live this means \(A_{11,10}\ne0\).
If both members of a shared-clock pair are active and
their \(r\)-amplitudes were equal, their evaluations on
\(E_3=\mathcal P_{\le3}(c)+\langle s,r\rangle\) would
agree. For forward rows 4 and 5 their difference of
incoming rows then annihilates \(E_2\) on physical 1–4.
But clock polynomials of degree at most two interpolate
the distinct values \(0,t,x\) there, and \(s\) independently
corrects the carrier row even if its clock coincides.
Thus \(E_2\) already restricts to the full four-coordinate
space. The difference would be zero, contradicting
\(A_{54}\ne0\). Reflection gives the other pair.

## If the repeated later entrance is dormant, it is exactly Simpson

If row 5 is dormant, it has no tap on the earlier carrier.
Its clock \(y\) cannot be zero, since the homogeneous
first two primitive equations on its active predecessors
would make it duplicate the origin. Its point exactness
through four follows from \(s_5=r_5=0\) and the true
\(F_4\) shape. Undoing the clock scaling, put \(p=c_5\);
the original entrance amplitudes are
\(c_3^2/(2\theta)\) and
\(c_4^2(3c_3-2c_4)/(2\theta c_3)\).
The grade-four \(Ar=0\) equation at row 5, after
clearing the common factors, is three times \(c_3\)
times its \(c^2\)-primitive equation minus twice its
\(c^3\)-primitive equation. Hence
\(p^3(c_3-p/2)=0\), so \(c_3=p/2\). The contact already
gives \(c_4=p\). Its exact first two monomial primitives
and row sum now solve uniquely
\[
    (A_{51},A_{53},A_{54})=(p/6,\ 2p/3,\ p/6),\qquad A_{52}=0 .
\]
Also the two active entrance amplitudes have ratio
\(r_4/r_3=-4\).
The reverse literal row 10 has the same formulas in
reflected coordinates, with length \(1-q\) for
\(q=c_{10}=c_{11}\), on physical rows \(14,12,11\);
in particular \(c_{12}=(1+q)/2\) and
\(r_{11}/r_{12}=-4\).
These ratios are independent of any rescaling of \(r\).

## Counts and the separate shared-clock exclusion

When all ten middle rows are active, the two forced
repeat pairs exclude \(q=9,10\). For \(q=8\), they cannot
share one clock, which would lose at least three labels;
so exactly these two pairs repeat and their amplitudes
are unequal as above. This case is not disposed of.

When there are exactly eight distinct active singleton
clocks, rows 4 and 11 are active by the forward and
reflected entrances. The forced adjacent repeats then
make rows 5 and 10 dormant and account for both additional
middle rows. In the shared-clock branch \(p=q=\zeta\),
the [localized-port packet](ERK10-SHARED-DORMANT-PURE-PORT.md)
already proves the fitted cubic is proportional to
\(R=L_4/(X-\zeta)\), with \(L_4(\zeta)=0\). The just-earned
actual entrance ratio gives
\(R(\zeta)=-4R(\zeta/2)\).
Equivalently \(\zeta L_4'(\zeta)=8L_4(\zeta/2)\);
the exact integer Bézout certificate of constant \(1201\)
in that packet rules this out. Thus there is no shared
dormant clock. This conclusion does not require a
fifth-grade square (whose total grade ten would not be
paid by order ten), nor any of the sixth-grade response
identities.

[ERK10FifthHeadContactGate.lean](ERK10FifthHeadContactGate.lean)
checks the cleared quartic, zero-tap case, and Simpson
identities. The rooted-space and literal deletion
arguments are the mathematical bridge above.
