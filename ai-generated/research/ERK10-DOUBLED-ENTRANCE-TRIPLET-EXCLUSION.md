# The doubled literal entrance excludes the all-live ERK10 (2,3,3) chart

Work over a characteristic-zero field in the
[two-carrier ERK10 equality chart](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md).
The [fifth-head contact](ERK10-FIFTH-HEAD-CONTACT.md) gives actual
nonzero taps \(A_{54},A_{11,10}\) and \(c_5=c_4,\ c_{10}=c_{11}\).
Here the local clock doubling is shown to hold **whether or not**
the later repeated row is \(r\)-active. The zero-pooled chart
of one uniform opposing pair and two active triples is then
entirely excluded. The nonzero-pooled eight-label ten-active-row
chart and the five-pair zero-pooled chart are not excluded here.

## Doubling with an active repeat

As in the contact packet, temporarily scale \(\theta\) to 1.
Let \(t=c_3\), \(p=c_4=c_5\), and \(a=A_{54}\ne0\).
The entrance has \(t,p,p-t\ne0\). Write
\(\Delta r=r_5-r_4\) and \(\Delta b=A_{53}-A_{43}\).
Subtracting the two genuine quadratic and cubic primitive
equations, and using the two stages' common clock, gives
\[
 \Delta r+t\Delta b+pa=0,\qquad
 2t\Delta r+3t^2\Delta b+3p^2a=0 .
\]
The calibrated genuine \(Ar\) relation at both stages gives
\[
 (3t-2p)(t^2\Delta b+2r_4a)=2t(p-t)\Delta r,\qquad
              2t r_4=p^2(3t-2p).
\]
The first two equations give \(t^2\Delta b=p(2t-3p)a\)
and \(t\Delta r=3p(p-t)a\). Substitution in the third
after multiplication by \(t\) gives
\(4p^2a(p-t)(p-2t)=0\). Hence \(p=2t\) over the stated
field. This use of the literal repeated tap is already
paid through grade four.

In the original units this proves
\(c_4=c_5=2c_3\), and by reflection
\(c_{10}=c_{11}=2c_{12}-1\).
In particular the two calibrated unary heads simplify to
\[
             Ar=(c_3-C)r,\qquad
             A^\star r=(C-c_{12})r
\]
throughout the all-live two-carrier equality chart.
The notation \(A^\star\) uses unpermuted physical coordinates.
The factor of proportionality between the two choices of
\(r\) cancels.

## Excluding the two active triples

In the [(2,3,3) frontier](ERK10-TWO-TRIPLE-FRONTIER.md), the
uniform opposing pair has clock \(a\); its earlier member is
one of 3,4,5, and its later member one of 10,11,12.
The two triple clocks and the two internal true clean clocks
are four distinct roots of \(L=42X^4-84X^3+56X^2-14X+1\);
the four true clean physical rows also include 0,1.

If row 5 were true clean, its clock \(c_5=c_4\ne0\) would
have to be \(a\): the independently nonzero \(r_4\) requires
an active group there, and the two triple clocks are distinct
from all true clean clocks. The active row 3 then has clock
\(a/2\ne a\), so its clock is one of the two triple clocks.
Both \(a\) and \(a/2\) would be roots of \(L\), contrary to
the earlier exact \(L(X),L(2X)\) Bézout identity of constant 59.
By reflection row 10 cannot be true clean either.

Thus 4/5 and 10/11 are two active repeat pairs.
Neither can be from the uniform pair, which is split across
the two frontier ranges. A triple cannot supply both
two-row groups, so these pairs belong to the two different
triples. Their occupancy forces the uniform pair to be
exactly physical 3 and 12. Therefore \(c_3=c_{12}=a\),
and the two triple clocks are \(2a,2a-1\).
But the exact identity
\[
 (-147X^3+735X^2-1222X+677)L(X)
 +(147X^3-147X^2+46X-3)L(X-1)=86
\]
excludes two roots of \(L\) at distance one in any
characteristic-zero field. This exhausts the chart
without requiring real signs or ordering.

[ERK10DoubledEntranceGate.lean](ERK10DoubledEntranceGate.lean)
checks both cleared identities. The literal rooted and count
bridges are the preceding mathematical argument. No
unrestricted ERK10 numerical bound changes.
