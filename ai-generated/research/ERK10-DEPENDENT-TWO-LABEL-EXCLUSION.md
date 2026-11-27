# The constant-amplitude ERK10 chart needs at least three active clocks

Continue the all-live, dependent \(d,Cd\) case of the
[fourteen-stage order-ten equality analysis](ERK10-FOURTEEN-STAGE-EQUALITY.md)
over any characteristic-zero field. By the two shifted-nine tap exits
its carriers include literal rows 2 and 13, with a common clock
\(\theta\ne0,1\). As in the [dependent profile](ERK10-DEPENDENT-R-PAIR-PROFILE.md),
assume that every carrier has the same nonzero quadratic defect
amplitude. Write \(s\) for their indicator and \(r=As\).
A noncarrier is active if \(r_i\ne0\); a row is called clean here
if both \(s_i,r_i=0\), hence point exact through grade four.
The original and weighted reversed flags agree through grade four,
and their \(E_5\) spaces are equal. All chronology is literal.

**Result.** Any remaining chart in this constant-amplitude fork
has **exactly two or three carriers and at least three distinct active
clock labels**. This closes all the two-label populations, including
same-clock contacts with the carrier and the formerly surviving triples.
At two carriers the amplitude assumption is automatic and there is
a particularly exact rank/prefix ledger below. A separate four-clock
Jacobi calculation also excludes the two-carrier, three-label maximal
population \((3,3,3)\). Nonconstant amplitudes and zero output weights
are not covered by this packet; there is no unrestricted numerical
stage-bound improvement.

## The first two active stages and the fifth-stage local tests

Temporarily normalize \(\theta=1\), scaling \(A,c,r\) together.
Then \(d=-s/2\). A carrier at row 3 forces \(A_{32}=0\)
by the quadratic residual at clock 1, and duplicates row 2.
Here and below, a literal duplicate incoming row can be merged
into its earlier copy, preserving ordinary order and contradicting
the 14-stage lower bound. Thus row 3 is a noncarrier with
\(t=c_3\ne0,\ r_3=A_{32}=t^2/2\). A zero clock there
would make the entire row zero, duplicating the origin.
The actual cubic residual is
\[
                Ac^2-c^3/3=-s/3+(1-2t/3)r ,
\]
by calibration on rows 2 and 3 in \(F_3=\langle s,r\rangle\).

If row 4 is a carrier, write \(a_{ij}=A_{ij}\).
The quadratic and cubic equations give
\(a_{42}+t a_{43}= (2t/3)a_{42}+t^2 a_{43}=0\),
so it duplicates row 2. Else \(z=c_4\) and those equations give
\[
  a_{42}=\frac{z^2(3t-2z)}{2t}=r_4,\qquad
  a_{43}=\frac{z^2(z-t)}{t^2}.
\]
The values \(z=0,t\) duplicate rows 1,3, respectively.
Also \(Ar=\gamma(C-t)r\) in \(F_4=\langle s,r,Cr\rangle\):
evaluate at row 2 to kill the coefficient of \(s\), and at
row 3 to normalize its clock factor. At row 4,
\((Ar)_4=a_{43}r_3\ne0\) implies \(r_4\ne0\).
Thus the first two active rows are literal rows 3 and 4,
with distinct nonzero clocks, and the reversed rows 12 and
11 are active and distinct as well. In particular the one-label
case is impossible, without using a positivity or field-order argument.

If row 5 is a carrier, \(r_5\ne0\): otherwise \(a_{52}=0\),
and the calibrated quadratic and cubic residuals force
\(t a_{53}+z a_{54}=t^2 a_{53}+z^2 a_{54}=0\),
which again makes row 5 duplicate row 2.

Now assume the two active numerical labels are precisely \(t,z\)
in these units, and the physical row 5 is **clean** in the
grade-four sense. Let \(u=c_5\), \(b=a_{53},c=a_{54}\).
Here \(a_{52}=0\) by \(r_5=0\) and the fact there was only
one preceding carrier. If \(u=0\), the same two homogeneous
linear equations force a duplicate of row 1. Thus \(u\ne0\).
Point exactness through grade four gives
\[
  bt^2+cz^2=u^3/3,\quad bt^3+cz^3=u^4/4,\quad
  b r_3+c r_4=0.
\]
Substitute the explicit amplitudes in the last equation:
\(u^3(2t-u)=0\), so \(u=2t\).
The primitive of \(X(X-t)(X-z)\), whose actual previous
read is zero, gives
\(u^2(3u^2-4(t+z)u+6tz)/12=0\), hence \(z=2t=u\).
The forthcoming clean noncontact excludes this. The same
argument at the reverse fifth row excludes a clean row 10.

## A two-label mask and no short clean support

Return to physical clock units. For two distinct active labels
\(\alpha,\beta\) put \(G(X)=(X-\alpha)(X-\beta)\).
The actual vector \(T=G(c)-G(\theta)s\) has grade two,
model \(G\), and is supported on clean rows only.
Also \(b\)-integration of \(G P\), \(\deg P\le7\), uses
only clean rows: the active labels are roots of \(G\); the
carrier ordinary mass is zero and their clock is fixed.
So the paid \(G\)-weighted quadrature and the two genuine
first/reverse-last boundary primitives are the same as in the
[clean-five exclusion](ERK10-UNBALANCED-CLEAN-FIVE-EXCLUSION.md),
whether or not this \(G\) came from a quadratic-defect interpolation.

For clarity the clean-five hypothesis here counts only
literal clean rows with \(G(c_i)\ne0\), i.e. the actual
support of \(T\). Both endpoints have nonzero \(G\):
if \(G(0)=0\), the first nonzero clean row is unable to
read either \(T\) or \(C T\), but their genuinely paid
first two primitives force \(G=0\); reflection does the
same at 1. Now if the support of \(T\) has at most
five rows, choose \(u,v\) to be the first nonzero and last
nonterminal clocks on this support. Earlier/later omitted
true clean rows have \(T=0\) and do not affect the boundary
primitive proof. At most three distinct support clocks
are impossible by the anchored Beta determinant.
Four distinct support clocks give the four-root fixed Jacobi
contact contradiction from the [equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md),
including its repeated endpoint-clock option.
With five distinct support clocks there are exactly five
supporting rows, and \(A(C(C-u)T)\) and \((C-v)(C-1)T\)
have disjoint support: the only potential central overlap before
the unary step is their middle supporting row, at which
the left input is delayed strictly. This pays exactly the
mixed primitive of the clean-five theorem, already excluded.
Thus the literal support of \(T\) has **at least six** rows.
In particular if there are exactly six clean physical rows,
none of their clocks equals either active label. The fifth-stage
calculation now rules out clean rows 5 and 10 in those charts.

## Four carriers: all two-label cases closed

With at least four carriers the earlier census gives at
most two active labels, hence exactly two by rows 3 and 4.
It forces exactly four carriers and active populations
\((2,2),(2,3),(3,3)\). Both triple populations leave at
most five physical clean rows, contradicting the mask.
The \((2,2)\) case with both labels distinct from \(\theta\)
is closed by the [four-pair seam transfer](ERK10-DEPENDENT-R-PAIR-PROFILE.md).

In the remaining \((2,2)\) case one active label is \(\theta\).
The only active rows are 3,4,11,12, since each label must
appear at both ends. There are six physical clean rows,
so the local fifth-stage exit forces the other two carriers
to be rows 5 and 10. They have \(r_5\ne0,r^\star_{10}\ne0\)
by the carrier calculation. Let \(\beta\) be the other active
clock. The actual \(A C T\) is zero through row 5 by strictness
and its zero earlier inputs (its grade-three input \(CT\)
is zero also at the origin). Write its grade-four model
and pure difference as
\[
       A C T=J[XG](c)+a s+(p+q C)r.
\]
At the two front carriers of clock \(\theta\), the different
\(r\)-values 0 and \(r_5\) force \(p+q\theta=0\).
At the noncarrier active row of clock \(\theta\) this now gives
\(J[XG](\theta)=0\). Since
\[
 J[X(X-x)(X-y)](x)=x^3(2y-x)/12 ,
\]
we have \(\theta=2\beta\).
The reflected test gives \(1-\theta=2(1-\beta)\),
a contradiction. No four-or-more-carrier chart survives.

## Two or three carriers, and the exact-six population

With at most three carriers, the carrier moments of \(r\)
through degree two imply that all their \(r\)-values equal zero.
Indeed a nonzero mass point for at most three distinct values is
impossible, and two distinct groups each with zero pooled weight
would require at least four live physical carriers. The value
at row 2 is zero. Thus \(b r^3=0\) comes entirely from
the active rows. At two active labels, the pooled \(b r\)
and \(b r^2\) vanish separately at each label.
Every active group requires at least two rows. If all amplitudes
are constant at both labels, then \(F_4\) is the direct sum of
the carrier and two active-group indicators, C-invariant
and closed under coordinatewise products, excluded by the
[native rank-three core](../lean/ERK-GRADE-EIGHT-OFF-CORE.md).
If an active group of size three is nonuniform, its \(r\)-values
are all distinct; two distinct values would need two cancelling
weights per value. Its cubic charge \(\sum b_i r_i^3\)
is nonzero by the three paid moments and the three-node
Vandermonde. Therefore neither \((2,2)\) nor \((2,3)\)
can survive. With three carriers nothing else is possible,
since six active rows would leave only five clean rows.

With two carriers the mask allows at most six active rows,
so there are exactly six, with populations \((3,3)\) or
\((2,4)\). There are six clean rows, and rows 5,10
cannot be among them. Hence the clean internals are exactly
rows 6–9 and the active rows are exactly 3,4,5,10,11,12.

At a repeated label \(x\) among the front three active
rows with **different** \(r\)-values, use the same grade-four
\(A C T\) equation. Its actual value is zero on all those
rows. The two distinct \(r\)-values force \(p+qx=0\),
and so \(J[XG](x)=0\), hence \(x=2y\) for the other active
clock \(y\). The reflected statement is
\(1-x'=2(1-y')\) for a repeated rear label \(x'\)
with distinct amplitudes.

In \((3,3)\), both triples are nonuniform (otherwise the
cubic charges cannot cancel), hence each has three distinct
amplitudes. The repeated labels at front and rear are opposite,
so \(x=2y,\ 1-y=2(1-x)\) give \(x=2/3,y=1/3\).
At the first nonzero clean clock \(u\) the actual \(CT\)
still has zero earlier values, and its unary is point exact.
Thus
\[
   0=J[X(X-1/3)(X-2/3)](u)=u^2(3u-2)^2/36 .
\]
This forces a forbidden clean contact \(u=2/3\).

In \((2,4)\), the uniform pair has one row at either end.
The quadruple repeats at both ends, and its first three
positive \(r\)-moments vanish (the pair cancels its cubic
charge). If its four amplitudes are all distinct, both
repeats force \(x=2y\) and \(1-x=2(1-y)\), impossible.
Three distinct amplitudes would require at least six
cancelling weights by Vandermonde. One amplitude
is the excluded uniform rank-three core.
Thus only two amplitudes in two opposing pairs need checking.
If the two front amplitudes differ, so do the two rear
ones and the same contradiction applies. Otherwise the
front two rows are a literal equal-amplitude tagged pair.
Carrier and uniform active-pair differences vanish in \(E_5\).
The quadruple's two weighted pair differences in \(E_5\)
lie on one line linking their two nonzero amplitudes,
by \(E_5=F_4^{\perp_B}\). The line occurs because
vectors equal on all four pairs have dimension ten,
less than \(\dim E_5=11\). Both quadruple pairs must split.
But before the second row of the front repeated pair
(row 5), \(E_3\) already interpolates the four tags
origin, carrier, active \(\alpha\), active \(\beta\):
use polynomial values at \(0,\alpha,\beta\) and
correct the carrier by \(s\). Equal \(E_4\) rows read
\(E_3\) equally, and strictness with this interpolation
makes their reads of all \(E_4\) inputs equal too.
All grade-five products already agree, so this pair
could not split in \(E_5\), contradiction.

## Two-carrier ledger beyond the two-label branch

With only two carriers, their two amplitudes and weights
are forced to agree and oppose, respectively, by
\(b d=b d^2=0\). Thus the constant-amplitude premise
is automatic in this case. They are physical rows 2 and 13,
\(A_{13,2}=0\) by \(r_{13}=0\), and \(r^\star=\lambda r\),
\(\lambda\ne0\). By adjointness
\[
        A_{13,*}-A_{2,*}=\lambda\,b\operatorname{diag}(r)/b_{13}.
\]
The two carriers agree on \(E_7=F_2^{\perp_B}\), and first split
in full \(E_8\). On the literal middle rows 3–12 the projections
of \(E_5,E_6\) are precisely the annihilators of
\(\{br,bCr\}\) and \(\{br\}\), of ranks eight and nine;
the two endpoint coordinates and the one shared carrier value
split freely from these projections.

If the pooled \(b r\)-measure is zero, the active clock count
is at most five (each needs two rows). Counts up to four also
have vanishing pooled \(b r^2\), so the earlier effective support
count \(12-2q\) forces \(q\le3\). Count five uses exactly ten
active rows in five pairs. Their pooled \(b r^2\)-measure must
be nonzero (otherwise only the endpoints support quadrature),
and its four moments force it nonzero at all five sites.
Each pair thus has unequal \(r\)-values. A nonzero pooled
\(b r\)-measure, on the other hand, requires eight or more
clock labels. These are independent continuation branches.

There is one further exact exit at \(q=3\): three active
triples \((3,3,3)\) would leave just three clean rows with
clocks \(0,u,1\). The six distinct effective ordinary sites
must be exactly the Lobatto sites, with the three active
clock values and \(u\) its four interior roots.
Take now the **cubic** \(G\) vanishing at the three
active labels, and \(T=G(c)-G(\theta)s\) of grade three.
The actual \(CT\) and \((C-1)T\) have overlap only at
the internal clean row, so \(A(CT)\cdot(C-1)T=0\)
and the mixed grade-nine primitive is paid.
In centered variable \(Z\), for \(U=2u-1\), take the
scaled \(G(Z)=21(Z^3+UZ^2+U^2Z+U^3)-14(Z+U)\).
This is the quotient of the centered Lobatto quartic by
\(Z-U\), at its true root. The mixed integral
\(\int_{-1}^1 J_{-1}[(Z+1)G](Z-1)G\) is
\[
  -\frac{14}{225}
       (4725U^6-4095U^4+915U^2+23).
\]
Modulo \(J_4(U)=21U^4-14U^2+1=0\) the bracket is
\(4(15U^2+17)\). The explicit Bézout
\(25J_4+(63-35U^2)(15U^2+17)=1096\) contradicts zero.
This scope is independent of a real ordering.

[ERK10DependentLocalGate.lean](../lean/RKCert/Research/ERK10DependentLocalGate.lean)
checks the fifth-row contact, doubled-clock relations and
the cubic Lobatto receipt. The short-support contradictions
reuse their prior Lean files; literal tableau bridges here are
mathematical. No conclusion is made for nonconstant amplitudes,
zero-output-weight tableaux, or the unrestricted 14–15 interval.
