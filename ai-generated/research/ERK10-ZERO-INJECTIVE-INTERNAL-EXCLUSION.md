# The injective old-grade-four zero-weight ERK10 branch is impossible

Work over a characteristic-zero field. A 14-stage strict
explicit rooted-order-ten tableau with at least one zero
output coefficient cannot have its diagonal output map
\(B=\operatorname{diag}(b)\) injective on the **original**
grade-four pure space \(F_4\).
The [injectivity theorem](ERK10-ZERO-WEIGHT-INJECTIVE-F4.md)
reduces that branch to exactly one ghost, with the same
genuine graded pure/model spaces through grade four in
the actual live reverse. The
[sole-origin proof](ERK10-SOLE-ORIGIN-GHOST-EXCLUSION.md)
excludes that placement. This note concludes the branch
by excluding all internal placements. No ordinary or
weighted high order is assumed for the live reverse
with an internal ghost.

Together with the
[all-live exclusion](ERK10-ALL-LIVE-COMPLETENESS.md),
any 14-stage characteristic-zero ERK10 candidate needs
a **nonzero original pure grade-four vector supported
entirely on zero-weight rows**. The **noninjective**
case is not excluded, and the numerical 14–15 interval
is unchanged. All stage indices below are one-based
old physical indices except where explicitly reversed.

## 1. Live matching and the precise projection guard

Let the internal ghost be \(g\). Its indicator
\(e_g\) is genuinely pure of grade five. The injective
ranks give \(E_5=(BF_4)^\perp\) and
\(W=F_4|_I=\bar F_4\) on the live coordinates \(I\).
The original quadratic defect \(d\) is nonzero at row 2:
its clock is nonzero (else a literal duplicate of origin).
It is supported at one clock \(\theta=c_2\), with common
nonzero amplitude \(d_*\). Write \(s=d/d_*\) and \(r=As\).
The true flags are
\[
 F_2=Ks,\qquad F_3=\langle s,r\rangle,\qquad
 F_4=\langle s,r,Cr\rangle,\quad C=\operatorname{diag}(c).
\]
Both \(F_4\) and \(W\) are non-clock-invariant by the
reviewed incoming gain, in the old and then the low-grade
exact reduced reverse respectively.
In particular their residual \(r\), respectively \(r_I\),
has at least two different clock labels outside \(\theta\);
if exactly two, its \(\theta\)-block is not proportional
to the carrier indicator, since otherwise the pure span
would be a sum of invariant clock blocks.

It follows that the only single-clock support line in old
\(F_4\) is \(Ks\), and the analogous line in \(W\) is \(Ks_I\).
Indeed, in \(\alpha s+(\beta+\gamma C)r\) isolating
\(\theta\) requires the affine factor to vanish at two
outside labels. Isolating an outside label also requires
vanishing at two other labels, using \(\theta\) itself if
there were exactly two outside labels. The same argument
uses the live blocks for \(W\).

Suppose two live **nonorigin** rows \(i,j\) agree on
all actual \(E_4\) evaluations. Their clocks agree, and
\[
                       z=e_i/b_i-e_j/b_j
\]
lies in \(E_5\) by annihilating \(BF_4\). It is pure \(F_5\):
its five numerical \(bC^k\) moments vanish at the equal
clocks, and its model vanishes at the old origin. The
anchored \(X\)-Gram on quartics makes that model zero.

If \(z_I\notin W\), then \(z,e_g\) are independent modulo
old \(F_4\) *by restriction*. They would fill the two
increments of \(F_5\); both are clock eigenvectors, so
\(CF_5\subset F_5\). The reviewed outgoing gain at
separated grade five would give \(f_6\ge5+3=8\).
In fact \(f_6\le7\): \(E_6\) has rank 12 and its pure
vectors are killed by the origin evaluation and the
four independent \(bC^j,\ 0\le j\le3\).
The independence follows by testing \(c,\ldots,c^4\)
with the anchored \(X\)-Gram and then testing \({\bf1}\).
Therefore \(z_I\in W\); its single-clock support
forces \(z_I\in Ks_I\).
Thus a matching live nonorigin pair exhausts the
**live** carriers and their weights oppose.
This does **not** assert that all original carriers
are live. A hidden \(e_g\)-component can distinguish
the old lift of \(z_I\) from \(z\), and will not be
dropped.

## 2. Exactly two live carriers and the actual early flags

The paid shift-one frontier gives a live carrier at
physical 13 with \(\theta\ne1\). Let \(m\) be the number
of live carriers. Their ordinary sum is zero by the
actual \(bs=0\), so \(m\ge2\). There are at least two
different live noncarrier \(r\)-active clock labels:
* If \(g=2\) or \(g\ge5\), the literal old early
  calculation gives distinct nonzero clocks and
  nonzero \(r\) at old rows 3 and 4, both live.
  It uses the genuine rank-three \(F_4\) and the
  fact an old duplicate is removable, not the
  liveness of carrier 2.
* If \(g=3\) or 4, the first four actual reduced
  reverse rows are old 14,13,12,11. No two of
  these can be literal duplicates: a duplicate
  gives a live nonorigin \(E_4\) match, whose
  carrier pair would also have to include the
  other live carrier at physical 2.
  The common old/low reverse flags therefore give
  the same first-two-response calculation there.
  At reversed row 3, another carrier would duplicate
  the first carrier by its quadratic condition;
  if instead the clock is zero it duplicates the
  origin. At reversed row 4 a carrier would
  duplicate the first carrier by the quadratic
  and cubic equations; a noncarrier uses the
  usual two-entry solve. Thus both physical 12
  and 11 are noncarriers, with distinct nonzero
  reflected clocks and nonzero reverse response.
  Since the reverse response lies in
  \(\langle s_I,r_I\rangle\) independent of \(s_I\),
  it is a nonzero multiple of \(r_I\) on
  noncarriers, which proves the needed two labels.

For clarity the first-four scalar calculation cited
here is purely actual low-grade algebra. Normalize
the first carrier clock to 1 in the relevant orientation.
A carrier at row 3 has zero tap to row 2 by its true
quadratic condition, so duplicates it. At a noncarrier
row 3 with clock \(t\), its response is \(t^2/2\),
and \(t=0\) would duplicate the origin. The calibrated
cubic defect is \(-s/3+(1-2t/3)r\). If row 4 is a
carrier, the two nonorigin reads \(a,b\) obey
\(a+tb=0,\ 2ta+3t^2b=0\), and so are both zero:
a carrier duplicate. At a noncarrier row 4 of clock \(p\),
\[
       r_4=\frac{p^2(3t-2p)}{2t},\qquad
       A_{43}=\frac{p^2(p-t)}{t^2}.
\]
The clocks \(p=0,t\) give literal duplicates.
The pure \(Ar\)-shape has form \(\gamma(C-t)r\)
from the first carrier and first response, so
\((Ar)_4=A_{43}r_3\ne0\) forces \(r_4\ne0\) and
\(\gamma=t/(3t-2p)\). This also explains why the
previous paragraph needed no exact higher reverse
order.

If \(m\ge4\), there are at most \(13-m-2\le7\) live
active noncarriers, since the two physical endpoints
are live and inactive. The carrier moments
\(b(s r^j)=0\), \(j=0,1,2\), cost \(2,5,8\);
as their clock is fixed they remove carrier contributions
to the first two \(r\)-moment families.
On the noncarrier active labels, \(br\) has seven
zero clock moments and \(br^2\) has four.
A nonzero pooled \(br\) requires at least eight
different labels, impossible. Zero pooled \(br\)
requires at least two rows per label, hence at most
three labels, so \(br^2\) cancels groupwise too.
Each active pair therefore cancels ordinary mass.
Since at least two active labels occur, the potential
scalar support is at most \(13-m-2q\le5\).
This contradicts the anchored ordinary support floor
of six. Thus \(m\le3\).

The same three amplitude moments on the live carriers
force each value group of \(r\) to have zero total
weight independently. With at most three rows they
share a single common \(r\)-value (not necessarily zero
if physical 2 is the ghost). Thus any pair of live
carriers matches on \(E_4\), and §1 forces **exactly
two live carriers**. If \(g\ne2\) they are physical
2 and 13; also \(r=0\) on both since \(r_2=0\).
The actual live reversed response is then a nonzero
multiple of \(r|_I\), its \(s\)-coefficient being
killed by its zero value at physical 13, the first
carrier in the actual reverse.

## 3. Genuine fifth contact and use of the pure ghost direction

Assume \(g\ne2\). The original first two physical
noncarriers really are 3 and 4, even if one of their
output weights is zero: a hypothetical carrier
there was just seen to be a literal duplicate under
the actual low equations. All preceding forward
quadratic/cubic and \(Ar\) formulas apply at the
**physical numeric rows** 3 and 4, not just at
weighted ones.

Here is the precise fifth-row reuse, including a
possible carrier ghost at row 5. In original units
scaled to carrier clock 1, let \(y=c_5\) and
use \(Q(X)=X^2(X-y)(2X-3t)\) with the genuine
quartic defect \(A Q'(c)-Q(c)\in F_4\).
Write \(w=-r/2\). Calibrating on the actual rows
2,3,4 gives the old formula
\[
 A Q'(c)-Q(c)
 =-Q(1)s+\big[-2Q'(1)+4t\gamma(C-t)+4t(y-C)\big]w .
\]
Units in this calibration are \(t,p,p-t,r_4\ne0\)
and \(3t-2p\ne0\); all were paid at the preceding
two true response stages. No weight \(b_3\) or \(b_4\)
is used, so the formula also holds when \(g=3,4\).
At row 5 \(Q(y)=0\), and a possible carrier there has
\(y=1\), so \(Q(1)=0\) too. Subtract \(4tAw\) there.
The carrier tap contribution \(Q'(1)A_{52}\) equals
\(-2Q'(1)w_5\), and \(Q'(t)=4t w_3\) kills the row-3
tap. The remaining true equation is
\[
                    6 A_{54}p(p-t)(p-y)=0 .
\]
If \(A_{54}=0\), the quadratic/cubic solves at row 5
make a carrier there a literal duplicate of row 2.
For a noncarrier they give the same formulas as at
row 4 with \(p\) replaced by \(y\); the actual calibrated
\(Ar\) equation then gives \(y^2(y-t)(y-p)=0\).
In the three possibilities \(y=0,t,p\), the two solved
entries and the row sum literally duplicate rows
1,3,4, respectively. In each case both old weights
need not be nonzero: merging duplicates still
preserves original ordinary order. Thus
\(A_{54}\ne0,\ y=p\).
The [doubled differences](ERK10-SINGLE-INVISIBLE-GHOST-DEPENDENT-THIRTEEN.md)
give \(p=2t\), including a carrier fifth row:
the extra cleared term
\(\epsilon t^2(p-1)\) is zero if its indicator
\(\epsilon=1\) because then \(p=1\).
When both repeat members are noncarriers, the same
paid difference is \(t(r_5-r_4)=3p(p-t)A_{54}\),
hence \(r_5-r_4=3p A_{54}\ne0\).
This is a true numeric contact, not a weighted
mean declaration.

The exact old \(F_5\) is
\[
                       \langle s,r,Cr,C^2r,e_g\rangle .
\]
Indeed \(F_4+CF_4\) has the four independent projected
directions just displayed by noninvariance of \(W\),
and the ghost line is independent of them. For the
physical fifth row put \(\epsilon=s_5\) and take
\[
                   H=r_4 e_5^{\mathsf T}
                    -r_5 e_4^{\mathsf T}
                    -\epsilon r_4 e_2^{\mathsf T}.
\]
It kills \(s,r,Cr,C^2r\), because \(r_2=0\),
the fourth row is noncarrier, and rows 4/5 have
the common clock \(p\). In particular \(HAr=0\).
The true column \(A(Cr)\) is pure of grade five.
But by its literal reads at 2,4,5, with \(r_1=r_2=0\),
\[
                H A(Cr)= t HAr+(p-t)A_{54}r_4^2
                         =(p-t)A_{54}r_4^2\ne0 .
\]
Thus \(H e_g\ne0\), so \(g\) is physical 4 or 5
(the index 2 is excluded in this subsection);
in the \(g=4\) case it forces \(r_5\ne0\).
In either case the ghost clock \(p\) is already
attained at a **live active** noncarrier
(the other member of the 4/5 pair).

## 4. Neither fourth nor fifth ghost survives the live moments

Now \(g=4\) or 5, so live carrier \(r\)-values are zero
and \(r^\vee=A^\vee s_I\) is proportional to \(r_I\)
as proved in §2. At most nine live noncarrier rows
are \(r\)-active. With pooled \(br=0\), there are
at most four distinct active labels, and the four
\(br^2\)-moments cancel them groupwise.
Each two-row active group cancels ordinary weight.
The ordinary support floor of six implies
\(13-2-2q\ge6\), hence \(q\le2\).
Adding the unweighted ghost introduces **no extra
numerical \(r\)-clock**, by the precise last conclusion
of §3. Therefore the whole original \(F_4\)
would be clock-invariant, contradiction.

With nonzero pooled \(br\) at least eight labels
occur. For nine active rows the cases are one repeat
at eight labels or nine singletons. The known
[scalar eight/nine-label proof](ERK10-THREE-CARRIER-EXCLUSION.md)
works on precisely these live active sites:
* At eight labels, \(\nu_x=(br)_x=\kappa/D'(x)\ne0\);
  \(R(x)=(br^2)_x/\nu_x\) interpolates to degree
  at most three by the four second moments.
  The lone weighted pair variance equals the difference
  of the \(br^3\) total and \(\sum_x\nu_x R(x)^2\).
  Both totals are zero via actual old pure grades
  and Vandermonde. With both pair weights nonzero,
  the two amplitudes must agree, so \(r_i=R(c_i)\)
  on every **live** active row.
* At nine singleton labels, \(\nu_x=P(x)/D'(x)\) with
  \(\deg P\le1\), nonzero at each label.
  Interpolate \(Q(x)=P(x)r_i\), of degree at most four.
  The cubic moment on \(Q^2/P\) eliminates the degree
  four square in the constant-\(P\) case, and the
  pole residue \(Q(\xi)^2/D(\xi)\) at a nonconstant
  \(P\)'s root \(\xi\) in the other. Either gives a
  cubic-or-less \(R=Q/P\) describing the literal
  amplitudes on the live sites.
The ghost itself need not match that polynomial.
Its weight is zero; both live carriers cancel
ordinary weight, and with nine active live rows
the only remaining live support is the endpoints.
Thus the paid scalar anchored \(X(1-X)\)-Gram on
\(R\) is a direct contradiction, without constructing
a numeric mask at the ghost.

The last case is eight live active singletons, so
there is one extra **live** dormant noncarrier besides
the endpoints. The genuine reduced reverse first
five rows are old \(14,13,12,11,10\), all live despite
the deleted fourth/fifth ghost **later** in its
chronology. None of these first five can be a
literal duplicate: that would give an old E4 live
match, and only the two carriers 2/13 could match;
physical 2 is not among them. The common exact
graded profiles through four therefore give the genuine
reversed fifth-head and doubling just used above,
with its two live carriers and their zero response.
In particular physical 11 is active and 10/11 have
the same clock \(q=c_{10}=c_{11}\). For eight distinct
live active labels, physical 10 must be the only live
dormant. Its reverse stage is the true Simpson
read: in the reflected interval of length
\(p'=1-q\), its reads at the preceding reflected
clocks \(0,p'/2,p'\) are \(p'/6,2p'/3,p'/6\);
its carrier tap is zero by the actual zero response
there. This follows by the quadratic and cubic
equations (or the
[original Simpson contact](ERK10-FIFTH-HEAD-CONTACT.md))
and uses no reverse stage beyond those five.
In particular the actual ratio of the prior two
responses is \(r_{11}/r_{12}=-4\), by the normalized
third/fourth formulas at clocks \(p'/2,p'\), after
canceling their common reverse-to-forward scaling.

The eight-site Vandermonde and \(br^2\) moments fit
a nonzero cubic-or-less \(R\) to the live singleton
amplitudes. If \(q\) is an endpoint, the scalar
anchored Gram again contradicts \(R\ne0\).
If not, the ordinary test
\(X(1-X)(X-q)R Q\) for \(\deg Q\le3\) pays degree
at most nine and reduces to the first pure \(br\)
moment on live actives (degree of the multiplier at
most six), with both endpoints and the one live dormant
killed, and live carriers canceling. Thus
\((X-q)R\) is proportional to the fixed Lobatto quartic
\(L_4=42X^4-84X^3+56X^2-14X+1\).
This is a scalar test, not a numerical dormant mask:
extra support at the zero-weight ghost need not vanish.

Reflect with \(\xi=1-q\ne0\). Up to a nonzero scale
the cubic is now \(L_4(Y)/(Y-\xi)\), and the actual
response ratio just obtained reads
\(\xi L_4'(\xi)=8 L_4(\xi/2)\) at the root \(L_4(\xi)=0\).
The exact integer certificate is
\[
\begin{aligned}
 A(X)&=252X^3-392X^2+182X-23,\\
 2[X L_4'(X)-8L_4(X/2)]&=7L_4(X)+A(X),\\
 (-273672X^2+268968X-50848)L_4(X)
  +(45612X^3-65100X^2+24738X-2263)A(X)&=1201 .
\end{aligned}
\]
This contradiction ends the fourth/fifth placements.
Thus every internal ghost \(g>2\) has been excluded.

## 5. The first carrier ghost relocates to an excluded position

It remains to exclude \(g=2\) without assuming the
two live r-carriers' common response is zero. By §2
there are exactly two live carriers \(i<j\), both
after physical 2, with \(b_i+b_j=0\).
All three stages \(g,i,j\) have clock \(\theta\),
so agree on \(E_1\). The two live carrier evaluations
also agree on **all \(E_7\)**: \(b s\) annihilates that
space by the paid \(2+7=9\) test; on live coordinates
it is the nonzero opposite-weight row on that pair.

Define a linear map \(S\) on the full coordinate space
by fixing all coordinates except \(j\), where
\[
                         (S f)_j=f_g+f_i-f_j .
\]
It is lower triangular, fixes the constant column,
and is an **involution** because \(g,i\) are fixed.
Thus \(A'=SAS^{-1}=SAS\) remains strict lower
triangular.

For any actual old rooted product of total grade
at most nine, \(S(fh)=(Sf)(Sh)\).
If both factors have grade at most seven, their
values at \(i,j\) agree separately, making the
new coordinate precisely the product at \(g\).
If one has grade at least eight, the other has
grade at most one. That low factor agrees at all
three \(g,i,j\), so factors out of the expression
defining \(S\). The identity at every other
coordinate is unchanged. Since \(A'S=SA\),
the genuine rooted recursion transports every
numeric stage vector through grade nine exactly
by \(S\), with unchanged formal model.
Hence \(b'=bS^{-1}=bS\) preserves every actual
order-ten test, and the new \(F'_4=S F_4\).

The new weights at \((g,i,j)\) are
\((b_j,\ b_i+b_j,\ -b_j)=(b_j,0,-b_j)\).
Thus the sole ghost is now **\(i>2\)**.
The new diagonal is still injective on \(F'_4\):
otherwise \(e_i\in F'_4\) and
\(S^{-1} e_i=e_i+e_j\in F_4\).
This vector is supported at the one clock
\(\theta\), so would be proportional to the old
\(s\). But its value at \(g=2\) is zero while
\(s_g=1\), impossible. The relocated tableau is
therefore in the just-excluded \(g>2\) branch.
This eliminates the remaining internal ghost
without either a finite-field order assumption
or an unproved higher reverse model.

[ERK10ZeroInjectiveInternalGate.lean](../lean/RKCert/ReviewedNative/ERK10ZeroInjectiveInternalGate.lean)
checks the true fifth-row contrast, reflected
scalar ratio and exact Lobatto certificate,
and the involutive stage relocation with strictness,
weighted output transformation and complete
rooted-word induction through grade nine.
The actual \(E_j,F_j\) ranks and polynomial
interpolation bridges are the audited mathematics above.
