# A single invisible ERK10 ghost: the reverse square and its two-clock Gram witness

Work over a characteristic-zero field with a literal 14-stage strictly
explicit order-ten tableau, exactly one zero output coefficient, and a
quadratic defect \(d=Ac-c^2/2\) supported on that coordinate. The
[equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md) applies.
Write \(E_j,F_j\) for the genuine numerical and pure spaces in grade
\(j=\text{tree size}-1\), \(B=\operatorname{diag}(b)\), \(C=\operatorname{diag}(c)\),
and \(Y=1-C\). All integrals below are formal. There is no positivity
or ordering assumption.

**Partial result.** The ghost is physical row 2, with a live outgoing
read at row 3. There is a genuine live-only reverse space through grade
three and exactly one possible nonlinear extra direction at grade four.
If the outgoing column has exactly two active clock labels, the pure
grade-three space in either direction restricts to the same line on
each of the two labelled blocks. The reverse space separates the two
lines, while the original live projection is their one-dimensional
mixed line. The actual reversed quadratic
defect has a square outside the linear grade-four reverse flag. Its
failure is detected at a specific label by a genuine marked Gram against
the extra **forward** grade-four direction. This excludes uniform
two-label outgoing columns, forces at least six and at most nine
nonzero outgoing taps in that chart, and gives a strict split condition
on two opposing same-amplitude pairs. The one-label and higher-label
charts are not excluded, nor are all surviving two-label charts.

## 1. Physical entrance and paid flags

If \(c_2=0\), stage 2 is literally a duplicate of stage 1, which could
be merged and would violate the independent fourteen-stage floor.
Hence \(\theta=c_2\ne0\), and \(d_2=-\theta^2/2\ne0\); the unique ghost
is physical stage 2. Put \(e=e_2\), \(I=\{1,3,\ldots,14\}\), and
\(r=Ae\). Then \(e\in F_2\), \(r\in F_3\).
With \(t=c_3\), the condition \(d_3=0\) gives
\(2\theta r_3=t^2\). If \(t=0\) both entries of the third row are
zero, another duplicate of row 1. Thus \(t,r_3\ne0\).
Also \(r_1=r_2=r_{14}=0\); the last equality uses the
paid grade-four point exactness of the terminal row.

The forward ranks obey
\[
 f_2=1,\qquad 2\le f_3\le3,\qquad 3\le f_4\le4,\qquad f_5=5,
 \quad f_j=\dim F_j.
\]
The upper bounds follow by strict rise into \(F_5\); they do
**not** assume that the cubic or quartic polynomial primitive defect
is already accounted for by \(r\) or \(Ar\).
Let \(V_j\) be the reverse row flag of the equality ledger, so
\[
 V_1=E_7^\perp,\quad V_2=E_6^\perp,\quad V_3=E_5^\perp,
 \qquad \dim V_j=j,\qquad
 h_2=2bYA-bY^2.
\]
Here these annihilators use the ordinary row/vector pairing. All three
row spaces vanish at the ghost because \(e\in E_2\). Define
\(W_j=B_I^{-1}(V_j|_I)\), writing weighted rows as columns on the live
set. These spaces still have ranks \(1,2,3\). In particular
\(r_I\in W_2\), \((Cr)_I\in W_3\) by the actual degree-three and
degree-four pure tests.

## 2. The true linear reverse rooms, with the square exposed

On \(I\), with reverse chronological order, use the strictly
explicit matrix
\[
 A^\vee=B_I^{-1}(A_{I,I})^{\mathsf T}B_I .
\]
It has clock \(y_i=1-c_i\) by the actual \(bA=bY\); it is not assumed
to have order ten. Because rows in \(V_j\) vanish off \(I\), right
multiplication by \(A\) on \(V_j\), restricted to \(I\), is precisely
\(A^\vee\) on \(W_j\) after normalizing by \(B_I\).
Consequently
\[
 W_{j+1}=W_j+Y W_j+A^\vee W_j\quad (j=1,2).
\]
In the reflected variable \(y\) its actual polynomial primitive
deviations \(A^\vee y^k-y^{k+1}/(k+1)\), for \(k\le 3\), belong to
\(W_3\). For \(k\le2\) they belong to \(W_2\), and for \(k=1\)
they give the reverse quadratic \(u=h_2/(2b)\) on \(I\).
Indeed the row
\[
 bY^k A-bY^{k+1}/(k+1)
\]
annihilates \(E_{8-k}\) by the formal scalar integration by parts:
\(k+1+(8-k)=9\). It has ghost component zero because \(e\in E_2\).
There is no missing deleted-column term. At the true reversal
entrance, physical 13, \(y_{13}\ne0\) by the shift-one weighted
floor, and
\[
 u_{13}=-y_{13}^2/2\ne0.
\]

The actual reverse pure spaces \(\bar F_j\) therefore satisfy
\[
 \bar F_2=W_1,\qquad
 \bar F_3=W_2,\qquad
 \bar F_4=W_3+\langle u^2\rangle.                 \tag{R}
\]
For the equality statements, the linear moves \(Y,A^\vee\) give
the displayed lower inclusions. Conversely, at each unary root the
deviation is the sum of the unary of a lower pure difference and the
polynomial primitive deviation for its model. At each product root,
the contributions are the lower pure differences times their
polynomial factors plus the product of two pure differences.
There is no nonzero pure grade one; the only two-pure product through
grade four is the square of the quadratic line. This proves (R) by
the genuine reverse recursion, and does not supply a full reversed
order statement.

The rank-three linear room \(W_3\) is **not** clock-invariant.
Otherwise use the reviewed
[linear incoming Hermite bound](../lean/RKCert/NodalHermiteRank.lean),
with the reversed stage order, \(U=W_2,\ W=W_3,\ N=A^\vee\) and
two failed nodes. The inclusion \(N U\subset W\) is paid above and
all primitive defects through degree four belong to \(W\).
Two failed clock blocks are guaranteed: if there were fewer, take
the nonzero polynomial \(P\) of degree at most one vanishing on
all failed blocks. Spectral projections (allowed by the hypothesized
invariance) on each matched block let \(P(y)\) belong to \(W\).
Then its paid tests against \(1,y\) give
\(\int_0^1 P(y)y^i\,dy=0\) for \(i=0,1\), contradiction by the
nonsingular unweighted two-by-two moment matrix.
The incoming bound would give \(2+2\le3\).
This reasoning uses only the verified linear primitives, not
unknown preservation of reverse squares.

If \(W_2\) **is** clock-invariant, the actual reverse outgoing Hermite
bound at grade three forces \(\dim\bar F_4\ge4\).
The required true reverse separation through grade three holds:
if a degree-at-most-three polynomial \(P(y)\) belongs to
\(\bar F_3=W_2\), its four pairings with \(y^i\) give the ordinary
formal moment system through degree six. That matrix is
nonsingular in characteristic zero, and \(P=0\).
By (R) this proves \(u^2\notin W_3\) and \(\dim\bar F_4=4\).
It also implies \(f_3=2\): if \(f_3=3\), the projection of \(F_3\)
onto the live sites equals \(W_2\) by rank and the paid pairing.
Because \(e\in F_3\) and there is only one ghost, this would make
the original \(F_3\) clock-invariant as well. Its outgoing gain
would force \(f_4\ge5\).

## 3. Two outgoing clocks: identification and the marked Gram gate

Assume \(r\) is nonzero only at exactly two different live clocks
\(\alpha,\beta\), both present on its support. Put
\(R=\langle r_I,(Cr)_I\rangle\). It has rank two and is clock stable.

First \(f_4=4\). Otherwise \(f_4=3,\ f_3=2\) and
\(F_4=\langle e,r,Cr\rangle\) is invariant, contrary to the
[reviewed forward incoming bound](../lean/RKCert/ReviewedNative/ForwardNodalGain.lean)
at grade three: \(f_4\ge f_3+2\). Thus \(F_4|_I=W_3\) by rank.
The rank-three room contains \(R\). Moreover \(u,Yu\in W_2\)
and \(r_I\in W_2\). If \(u\notin R\), then \(W_3=R+\langle u\rangle\)
would be clock-invariant (as \(Yu\in W_2\subset W_3\)), impossible.
If \(u\) and \(r_I\) are independent they now span both \(R,W_2\);
otherwise \(Yu\) and \(u\) span \(R\). Hence \(W_2=R\).
In particular \(f_3=2\), the reverse square is genuinely new,
and \(r_{13}\ne0\).

The two nonzero localized rows \(b r\,{\bf1}_{c=\alpha}\),
\(b r\,{\bf1}_{c=\beta}\) now each belong to \(V_2\).
They annihilate all of \(E_6\), separately, not merely on sum.
Testing the pairs \(1,r,r^2\) (grades 0,3,6) gives
\[
 \sum_{i:c_i=x} b_i r_i^j=0
       \quad(x=\alpha,\beta;\ j=1,2,3).             \tag{M}
\]
In particular each label has at least two active rows. If a label
has at most three distinct nonzero amplitudes, (M) localizes again
in the amplitude variable: each same-amplitude subgroup has pooled
ordinary weight zero. Therefore a nonuniform label needs at least
four active rows. At exactly four it either has two opposing
equal-amplitude pairs or four distinct amplitudes.

Choose any \(z\in F_4\setminus\langle e,r,Cr\rangle\).
The stable rank-three subspace \(\langle e,r,Cr\rangle\) plus \(z\)
is \(F_4\). The reviewed outgoing gain at grade four prevents \(F_4\)
itself being invariant, since \(f_5=5<4+2\). Consequently
\[
 F_5=\langle e,r,Cr,z,Cz\rangle .
\]
Write \(u_i=a_x r_i\) on a labelled active group \(x\).
From (M), \(u^2\) is orthogonal to every clock polynomial, to
\(e,r,Cr\), and hence to \(E_3\); it need not kill \(E_5\).
At least one of the following pairings is nonzero:
\[
     \langle u^2,z_I\rangle_{B_I}\ne0,\qquad
     \langle u^2,(Cz)_I\rangle_{B_I}\ne0 .
\]
Otherwise it would annihilate \(E_5|_I\), contradicting \(u^2\notin W_3\).
A two-clock Vandermonde separation therefore gives a label \(x\)
with \(a_x\ne0\) and
\[
             Q_x:=\sum_{c_i=x} b_i r_i^2 z_i\ne0.       \tag{G}
\]
This is a genuine signed marked Gram failure, not an approximate
defect rank. It is independent of the choice of complement \(z\)
up to a nonzero overall scalar, since replacement by a vector
of \(\langle e,r,Cr\rangle\) has zero \(Q_x\) by (M).
In particular a label contributing (G) is nonuniform.
If its four rows are two opposing weight pairs with amplitudes
\(a,b\), weights \((w,-w)\), \((v,-v)\), and within-pair forward
grade-four differences \(\Delta,\Delta'\), then
\[
    a w\Delta+b v\Delta'=0,\qquad
    Q_x=a^2 w\Delta+b^2 v\Delta'\ne0 .
\]
Both differences must already be nonzero: both same-amplitude
pairs split at actual grade four, not at grade five or later.

There are at least six live active rows by this selection and the
other label's cancellation. For the upper count put
\(G(X)=(X-\alpha)(X-\beta)\) and use the actual ghost-corrected
grade-two mask \(T=G(c)-G(\theta)e\).
It is zero at the ghost and at every \(r\)-active row.
Its exact scalar model is \(G\). Thus the \(r\)-free live clocks
integrate \(G(X)P(X)\) through \(\deg P\le7\).
They include the physical clocks 0 and 1. If there were at most
three distinct clean clocks, let \(K\) be the monic product of
the at most one interior clean factor. Testing with
\(X(1-X)K(X)S(X)\) makes \(GK\) orthogonal under weight \(X(1-X)\)
to all polynomials up to its degree at most three, a contradiction
by the nonsingular anchored Beta matrix. Thus at least four
distinct clean clocks and at most nine live active rows occur.
If there are exactly four clean clocks, \(G K\) with both
interior factors is the fixed Lobatto quartic by the same four
orthogonality tests. In this case the complement \(z\)
must be nonzero on the chronological first nonzero clean clock
and on the last clean clock different from 1. For the first,
the actual grade-three vector \(CT\) is zero before that row.
The zero-pure polynomial primitive \(J[XG]\) does not vanish at
this contact by the [fixed-four scalar check](ERK10-FOURTEEN-STAGE-EQUALITY.md#scalar-reconstruction-in-the-unbalanced-chart)
(the immediately preceding quadratic four-clock calculation).
Therefore its grade-four error cannot vanish there, and all forward
grade-four pure vectors on this row are multiples of \(z\).
The reflected argument uses actual reverse grade-two polynomial
\(G(c_I)\), whose reflected \((1-C)\) multiple gives the last
contact. By (R) and \(u=0\) at a clean row all reverse grade-four
pure vectors there are likewise multiples of \(z_I\).
These contact statements do not call the other clean rows point
exact through grade four.

If both labels additionally have zero ordinary pooled weight within
every amplitude subgroup, the clean rows integrate ordinary degree
nine without \(G\); the two endpoint tests require at least six
distinct clean clocks, so there are only six or seven live active
rows. The nonuniform group then has size four or five and exactly
two amplitude subgroups, of sizes \((2,2)\) or \((2,3)\).
The other label is uniform with two or three rows.
No such opposing-amplitude case is excluded by this note alone.
The [follow-up closures](ERK10-SINGLE-GHOST-TWO-CLOCK-CLOSURES.md)
exclude four distinct clean clocks and every two-clock case with
seven or more active physical rows.

## 4. A literal row-four consequence and the remaining scope

Whenever \(f_3=2\) (in particular throughout the two-label chart),
the true cubic defect is in \(\langle e,r\rangle\).
At physical rows 2 and 3 its coefficients are fixed:
\[
 Ac^2-c^3/3
  =-\theta^3 e/3+(\theta^2-2\theta t/3)\,r .
\]
For \(z_0=c_4\), the two literal row-four equations give
\[
 A_{42}=\frac{z_0^2(3t-2z_0)}{2\theta t},\qquad
 A_{43}=\frac{z_0^2(z_0-t)}{t^2}.
\]
Here \(z_0=0,t\) would duplicate row 1 or row 3, respectively,
by the two formulas and the clock sum. So \(A_{43}\ne0\) and
\((Ar)_4\ne0\). In the two-clock branch either \(c_4\) is the
other active clock or \(r_4=0,\ c_4=3t/2\).
In the one-label branch \(f_4=4\) as well: a smaller room would
give \(f_3=2\), then the rank-two \(F_3=\langle e,r\rangle\)
would be invariant and demand at least two outgoing gains.
However \(W_2\) need not have been proved invariant for one label;
if \(u\) and \(r_I\) are independent it is invariant
(both \(Yr_I\) and \(Yu\) belong to their span),
whereas proportionality requires a separate analysis.
No claim rules out this branch.

[ERK10SingleGhostGate.lean](../lean/RKCert/Research/ERK10SingleGhostGate.lean) verifies the
small scalar entrance, localization, paired Gram, and Beta determinants.
[ERK10SingleGhostRank.lean](../lean/RKCert/Research/ERK10SingleGhostRank.lean) proves the
abstract two-clock lane identification in finite-dimensional Lean/Mathlib.
The rooted bridge and application to the actual equality filtration
above remain mathematical, reusing the cited reviewed native Hermite
lemmas. Neither an unrestricted 15-stage floor nor deletion of the
literal ghost has been proved.
