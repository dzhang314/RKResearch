# One-clock reverse seed cannot be independent with a moving rank-two room

Work over any characteristic-zero field in the
[single invisible ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md).
On a hypothetical 14-stage strict explicit order-ten tableau,
the only zero output weight is physical 2 and the original
quadratic defect is entirely invisible. Let \(e=e_2\) be its
pure grade-two indicator, \(r=Ae\) the genuine pure grade-three
outgoing column, and \(u\) the actual quadratic defect of the
reduced weighted transpose on the thirteen live rows.

Assume original pure rank \(f_4=4\), that \(u\) is supported
at exactly one clock \(\theta\), that \(u,r_I\) are independent,
and that their exact live dual room \(W_2=\langle u,r_I\rangle\)
is **not** clock-invariant. These assumptions are incompatible.
No assumption on original \(f_3\) is made; the newly applicable
case is \(f_3=2\). One-clock dependent and clock-invariant-room
cases are not excluded here, nor are multiple ghosts.

## 1. Endpoint kernel and the first count

Let \(I\) be the live set. Because \(f_4=4\) and the only lost
pure direction is \(Ke_2\), paid orthogonality gives
\(F_4|_I=W_3\). Thus all its projected vectors, including \(u\),
vanish at the old physical origin 1 and terminal 14, by old
grade-four point exactness there. Choose ghost-zero old pure
lifts by subtracting a multiple of \(e_2\) at the ghost.
In particular this earns \(u\) as an actual old pure
**grade-four** vector (not necessarily grade three).
As a numerical profile \(Cu=\theta u\) everywhere, including
its chosen ghost zero.

The moving room \(W_2=\langle u,r\rangle\) gives
\(W_3=\langle u,r,Cr\rangle\), and the genuine reverse
linear incoming obstruction says \(W_3\) is not invariant.
As in the
[cubic-rank packet, §2](ERK10-SOLE-INVISIBLE-GHOST-CUBIC-RANK-TWO.md#2-the-exact-terminal-kernel-with-one-carrier-block),
this means \(r\) has at least three active clock eigenspaces
in the quotient by \(Ku\). The exact old \(F_5\) is therefore
\[
                         Ke_2+\langle u,r,Cr,C^2r\rangle .
\]
If the quotient had exactly three active labels, this space
would be clock-invariant, contrary to the grade-five
outgoing bound and \(f_6=7\). Thus that quotient has at
least four active labels. With the genuine old lifts and
clock multiplication, the six independent pure directions
\[
                            e_2,\ u,\ r,\ Cr,\ C^2r,\ C^3r
\]
all belong to \(F_6\) and vanish at physical 14.
They fill that evaluation kernel, of rank six, because
\(Ae_{14}=0\) is a genuine grade-six advance with model
value \(b_{14}\ne0\) at 1, as explained in the linked proof.

In particular \(r^2\), actual pure at grade six, has live form
\[
                       r_i^2=\alpha u_i+r_i R(c_i),            \tag{1}
\]
where \(R\) has degree at most three. Wherever \(u_i=0\) and
\(r_i\ne0\), this gives the literal \(r_i=R(c_i)\).
Call \(u\)-active stages carriers. There are at least three
distinct off-\(\theta\) active \(r\) labels by the four quotient
labels. If exactly three, then total \(r\)-support has at most
four labels; the seven \(br\) moments kill every pooled mass.
At each off-\(\theta\) label the active amplitudes are uniform
by (1), so their ordinary mass cancels and the groups save at
least six live physical sites.
The carrier block also saves two: \(bu=0\) requires at least
two carriers, two carriers with \(bu=bu^2=0\) are uniform and
opposing, and three or more compress to at most one ordinary
site. The square test uses the genuine grade-four lift in
\(E_7\) against \(bu\in E_7^\perp\), not the unearned grade
of \(u^2\). Thus at most \(13-6-2=5\) ordinary sites would
remain, impossible. At least **four** distinct off-\(\theta\)
\(r\)-active labels occur.

Let \(m\) be the carrier count. Both endpoints have \(r=u=0\).
If \(m\ge5\), at most \(11-m\le6\) noncarrier \(r\)-actives
and the one carrier clock give at most seven \(r\)-labels.
Again all \(br\) pools would vanish and the four distinct
off-\(\theta\) active groups would need at least eight
noncarrier rows, impossible. Therefore
\[
                                 2\le m\le4.                  \tag{2}
\]

## 2. A corrected cubic mask costs no extra clock grade

We will need the following precise form of the
[anchored cubic-response seam](ERK10-INVISIBLE-GHOST-UNBALANCED-AFFINE-CLOSURE.md#2-a-paid-scalar-and-causal-lemma-when-the-literal-response-is-cubic).
Suppose the carriers are uniform in \(u\), with amplitude
\(\rho\ne0\), and uniform in \(r\), with amplitude \(\eta\).
Their ordinary weight sum is zero by \(bu=0\). Put
\[
 T=R(c)-r-R(c_2)e_2-\frac{R(\theta)-\eta}{\rho}\,u .
\]
This erases the ghost, the carrier block and every
\(r\)-active noncarrier. The scalar clock model is \(R\).
Although the correction \(u\) itself may cost old grade
four, the genuine vectors \(CT\) and \((1-C)T\) **both**
cost at most grade four: their clocked base costs four,
and the \(u\)-corrections are just scalar multiples
\(\theta u,(1-\theta)u\) of the same actual grade-four
pure vector. The corresponding models are \(XR,(1-X)R\).
In particular \(A(CT)(1-C)T\) is genuinely paid at grade nine.
If only the endpoints and at most one extra noncarrier
dormant stage remain, ordinary \(R\)-weighted quadrature
is supported there (the uniform carrier weights cancel).
The endpoint-only case contradicts the anchored Gram.
Otherwise the one interior dormant clock \(w\) yields
\((X-w)R\propto L_4\) and this causal product is literally
zero. Its exact scalar seam is nonzero by the earlier
Bézout check. This will close every branch with those
uniform profiles and counts.

## 3. Nonzero coefficient \(\alpha\)

The tests of \(bu\) against \(1,r,r^2,ru\) respectively
pay old input grades \(0,3,6,7\).
At the one carrier clock, equation (1) gives
\[
                  \alpha u_i=r_i^2-R(\theta)r_i .
\]
Multiplying by \(b_i u_i r_i\) and summing on the carriers
uses the \(ru\) test to give \(\sum b_i u_i r_i^3=0\),
in addition to the first three tests. Thus all four
\(bu\)-weighted amplitude moments in \(r\) vanish.
With \(m\le4\), each \(r\)-value group separately has
zero \(bu\) mass. Because \(\alpha\ne0\), its \(u\)-value
is also uniform and nonzero, so every group's ordinary
weights cancel. All pooled carrier \(br\) moments vanish.

If \(m=4\), there are at most seven active noncarriers,
so their pooled \(br\) row is zero. But the four distinct
off-\(\theta\) labels again need eight rows. Thus \(m\le3\),
and there is only one carrier value group: two groups would
need at least two rows each. The carrier profiles are uniform
in both \(r\) and \(u\).
If pooled noncarrier \(br\) were zero, its at least four
uniform active clock groups would save at least eight ordinary
sites (the carrier block also cancels). This is impossible.
So the noncarrier pool is nonzero, requiring at least eight
active labels. The remaining noncarrier dormant rows number
at most \(13-m-8\le3\), including the endpoints. The
corrected cubic-mask case in §2 applies and contradicts.

## 4. Zero coefficient \(\alpha\)

Now (1) gives the literal profile \(r_i=R(c_i)\) at
**all** \(r\)-active live sites, including carriers.
The pooled \(br\) row cannot be zero: its at least four
off-\(\theta\) active groups alone would then save at
least eight ordinary sites, leaving at most five.
There are therefore at least eight effective \(r\)-labels.

At clock \(\theta\) the carrier \(r\)-values are \(0\)
or \(R(\theta)\). If both values occur, \(bu,bur\) give
zero pooled \(bu\) in each subgroup. The additional paid
\(bu^2,bu^2 r\) tests (using the old \(u,ru\) lifts)
give zero pooled \(bu^2\) in each too. If there is only
one value group, both facts hold on it without separation.
In every case a nonempty subgroup has at least two rows,
and a two-row subgroup has uniform \(u\) and opposing
ordinary weights.

If \(m=4\), at least eight effective \(r\)-labels require
seven active noncarriers with distinct off-\(\theta\)
clocks and a nonzero carrier \(r\) pool at \(\theta\).
If carriers split, their nonzero-\(r\) subgroup has two
rows and ordinary mass zero, so that pool cannot occur.
If all carriers have \(r=0\), it is also absent.
If all four have nonzero \(r\), all eleven non-endpoint
live rows are \(r\)-active and the \(R\)-weighted
quadrature is supported only at the two endpoints.
The same anchored Gram excludes it. Thus \(m\le3\).

There is now only one carrier \(r\)-value:
* If its value is nonzero, the cubic mask
  \(R(c)-r-R(c_2)e_2\) already vanishes at all carriers.
  With \(m=3\), there are at least seven noncarrier active
  rows (eight effective labels including \(\theta\)),
  giving at least ten \(r\)-active rows overall.
  With \(m=2\), if there were only seven such noncarrier
  rows they would have to be at the seven distinct
  off-\(\theta\) clocks, but the carrier pair cancels
  ordinary mass and then cannot supply an eighth effective
  label. Thus this case too has at least ten \(r\)-active
  live rows. The plain middle-seam or endpoint Gram
  contradiction applies with at most three dormant rows.
* If all carriers have \(r=0\) and \(m=2\), their \(u\)
  amplitudes are uniform and opposite weights cancel.
  There are at least eight noncarrier active sites, so §2
  again applies using the corrected mask.

The last possibility is **three carriers with \(r=0\)**.
All eight other non-endpoint live rows are \(r\)-active,
so the plain \(R\)-weighted quadrature is supported on
\(0,\theta,1\). If \(\theta\) is an endpoint or the
ordinary carrier mass is zero the endpoint Gram contradicts.
Otherwise \(\theta\) is an interior Lobatto root and
\((X-\theta)R\propto L_4\). The three \(u\)-amplitudes
are distinct: if at most two nonzero values occurred,
the two zero moments \(bu,bu^2\) would make their ordinary
weight sum zero. Write their physical positions \(i_1<i_2<i_3\).
The true old \(Au\) is pure of grade five. At each of
the three carriers its value is a single scalar multiple
of \(u_i\), since all \(r\)-directions in \(F_5\) vanish
there. The value at \(i_1\) is zero by strictness and the
ghost-zero support of \(u\), so that multiple is zero.
Consequently \(A_{i_2,i_1}=0\) by evaluating \(Au\)
at the second carrier.

Take \(T=R(c)-r-R(c_2)e_2\), genuinely grade three.
It is supported at the endpoints and the three carriers.
The vector \(CT\) is zero at the original origin.
Thus \(A(CT)\) is zero at \(i_1\) by strictness and at
\(i_2\) by the exact tap zero. At the carrier clock its
model \(J(XR)\) is constant; its grade-five pure deviation
is a scalar multiple of \(u\), again because \(r=0\)
there. Its two zero values at distinct \(u\)-amplitudes
force it zero at **all** three carriers.
The grade-nine mixed product \(A(CT)(1-C)T\) is now
numerically zero: it is zero at the carriers and original
origin, and the right factor kills the terminal.
Its formal Lobatto seam is nonzero. This final contradiction
exhausts \(\alpha=0\).

[ERK10InvisibleOneClockMovingGate.lean](../lean/RKCert/ReviewedNative/ERK10InvisibleOneClockMovingGate.lean)
checks the amplitude relation that pays the fourth moment,
the literal tap cancellation, the affine two-zero gate
and the compensated mask coefficient. Low rank, support
and the rooted-order bridge remain the proof above.
