# Six off clocks and six clean clocks at shift two

A strictly explicit, last-active twelve-row tableau exact on all rooted
profiles through size nine for
\(\ell_2(P)=\frac12\int_0^1(1-X)^2P(X)\,dX\) cannot have exactly six
distinct off clocks and six distinct clean clocks over a
characteristic-zero field. No ordering or sign is needed.
In paid positive characteristic \(11!\ne0\), the assertion is
conditional on a nonzero integer certificate in the actual
first-clean placement, specified below.

Combining with the [six-off/five-clean result](WEIGHTED-ORDER-NINE-SIX-OFF-FIVE-CLEAN.md)
excludes the entire six-off population at shift two over characteristic
zero: six off labels imply at least five clean labels by the paid Gram
after off-aggregate cancellation, and there is room for at most six.

## Forward and reverse inputs

Use the actual four-tap terminal classification and late ranks of
[FourTap](WEIGHTED-ORDER-NINE-FOUR-TAP.md)
and [Off Gates](WEIGHTED-ORDER-NINE-OFF-GATES.md).
As before, \(d=Ac-c^2/2\), \(F_4=dP_{\le2}(C)\), and some nonzero
polynomial \(G\) of degree at most two fits \(d_i=G(c_i)\ne0\) on
off sites. A tagged state is the clock together with clean/off;
there are twelve distinct states on twelve physical rows in this
branch, so every state is unique. The seven paid tests
\(\beta C^k d=0\), \(0\le k\le6\), cancel every off aggregate,
hence each off weight is individually zero. The scalar quadrature
on clean clocks is exact through degree eight. In particular the
live final stage is clean at clock 1.

The four-tap witness \(v\in E_4\) has leading row 8, with
\(\theta=c_8=c_9\ne1\), and \((C-\theta)v\) is supported only
at row 12. The physical edge from row 8 to 9 is nonzero.
The space \(H_5=E_5+K e_{12}\) has dimension ten. The actual
finite profile \(P_{\le5}(c)+dP_{\le3}(c)\) lies in it and has
dimension ten by interpolation, first on six distinct clean
labels, then on six distinct off labels. So it equals \(H_5\).
Use this profile for the actual \(e_{12}\).
Its off polynomial, of degree at most five, vanishes on all
six off labels and is therefore identically zero. Its clean
polynomial \(P_{\rm end}\) is zero at the five other clean labels
and takes value one at 1. Thus it has degree five and
\(P_{\rm end}=-G R\) with \(\deg R\le3\), proving \(\deg G=2\).

The polynomial of \(v\) on off sites has degree at most four.
Only an off site at \(\theta\) could be nonzero, since \(v\)
is supported at \(\theta\) and the clean terminal site.
At most one off state has this label. Five other off zeros
force the entire off polynomial to vanish. Hence \(v\) is
zero on all off sites, row 8 is clean, and row 9 is off because
two clean copies of the same state are impossible.
Therefore at least two clean sites lie before row 8 (only four
of rows 8–12 could be clean). One is the origin; the first
nonzero clean row has some clock \(a\) before row 8, in
particular \(a\ne0,\theta\).

Let \(P\) be the grade-four scalar model of \(v\).
The two-curve description and the zero off polynomial imply
\(P=-G R'\) for \(\deg R'\le2\). On clean sites \(v=P(c)\),
so \(P\) is zero at the four distinct clean labels other
than \(\theta,1\), while \(P(\theta)=v_8\ne0\).
Consequently \(P\) has degree four and no additional roots,
so \(P(1)\ne0\) as well.
As in the first-clean calculation in the high-off note,
\(J(XG)(a)=0\) and \(G(0)\ne0\) by testing the actual masked
vectors \(C(G(c)-d)\) and \(G(c)-d\) at the first nonzero
clean row. Thus \(G\) divides the product of the three distinct
nonzero clean labels other than \(\theta,1\). It occupies two
of these labels, and the remaining one is denoted \(t\).
After monic normalization of \(G\) and scaling \(v\) by a unit,
\[
                           P=X(X-t)G .
\]
The notation \(t\) is a clock, not an index. The first nonzero
clean clock \(a\) before row 8 is either \(t\) or one of the two
roots of \(G\). No assertion on the numerical ordering of
these clocks is made.

## Paid quartic moments and an actual grade-five clean minor

The six clean labels are \(0,\theta,1,t\) and the two roots of \(G\).
Their nodal hull is \(X(X-1)(X-\theta)(X-t)G\).
By the exact degree-eight clean quadrature its three tested moments
against \(1,X,X^2\) vanish. Equivalently
\[
 \int_0^1 X(1-X)^3(X-\theta)(X-t)G(X)X^k\,dX=0,
                         \qquad 0\le k\le2 .
\]

Since \(v_{12}=P(1)\ne0\), \((C-\theta)v\) is a nonzero multiple
of \(e_{12}\) already in \(E_5\). Thus \(\dim E_5=10\).
If its polynomial model separated, there would be a dense size-six
explicit derivative decoder on ten stages, contrary to the
[paid dense width eleven](erk-dense-width/README.md).
An alias polynomial through grade five vanishes at 0 and
has the four tested weighted moments against \(1,X,X^2,X^3\) zero.
By the anchored Gram, such polynomials are exactly the line
\(K R_5\), where
\[
                       R_5=X(66X^4-120X^3+72X^2-16X+1).
\]
The formal pair space therefore has dimension eleven, so its pure
subspace \(F_5\) has dimension five (subtract the six-dimensional
polynomial image). It contains four independent \(dP_{\le3}(c)\)
columns and the independent pure alias column \(R_5(c)\), the
latter detected at 1 by \(R_5(1)=3\ne0\).
Thus every pure column restricts on the clean sites to a
multiple of \(R_5(c)\). The actual \(Av\) vanishes through
row 8. Applying this observation to \(Av-(JP)(c)\) at \(a,\theta\)
gives the necessary equation
\[
                     (JP)(a)R_5(\theta)-(JP)(\theta)R_5(a)=0 .
\]
In particular there is no division by either value of \(R_5\).

## Two arithmetic cases

If \(a=t\), these are exactly the premises of the previously
checked `HighOffGate.lobattoQuarticImpossible`:
first-clean chronology \(J(XG)(a)=0\), three moments of
\((X-a)(X-\theta)G\), and the clean minor of \(J(X(X-a)G)\).
Its only additional integer guard is the nonzero
\(D_{\rm pencil}\) from the
[high-off proof](WEIGHTED-ORDER-NINE-HIGH-OFF.md).

Otherwise \(a\) is one of the two head roots. Write \(G=(X-a)(X-b)\).
The chronological equation \(J(XG)(a)=0\), multiplied by 12,
is \(a^3(2b-a)=0\); hence \(G=(X-a)(X-a/2)\).
Scale the moment polynomial and \(P\) by 2 to avoid denominators:
\[
   S=(X-t)(X-\theta)(2X^2-3aX+a^2),\qquad
   \widetilde P=X(X-t)(2X^2-3aX+a^2).
\]
With \(S=\sum_{i=0}^4 c_i X^i\), the three tested moments
multiply by \(2520,2520,27720\), giving exactly coefficient rows
\[
                 (126,42,18,9,5),\qquad
                 (42,18,9,5,3),\qquad
                 (198,99,55,33,21)
\]
on \(c_0,\ldots,c_4\). This is the same shifted weight arithmetic
checked in `HighOffGate.momentIntegersCorrect`.
The clean minor of \(60 J\widetilde P\) is divisible as a scalar
polynomial by \(a\theta(a-\theta)\), nonzero by literal chronology
and the two distinct nonzero clean labels. No other
parameter-dependent quantity is cancelled.
The explicit integer certificate presented in
`SixOffSixGate.calibratedRootImpossible` is a linear combination
of these three moment polynomials and the divided primitive minor,
equal to the nonzero constant
\[
 D_{\rm root}=
 173833915438769983085557868203824782091278591073457262721465370242792856516213780065507782212769838343711604093504796240000000 .
\]
The coefficients and the polynomial verification algorithm are
in the Lean source. No Gröbner computation is part of the trusted
replay. The root case is ruled out if \(D_{\rm root}\ne0\) in the
field; failure of the specific constant at a prime says nothing
about existence at that prime.

## Verified boundary

The Lean-core leaf checks the root chronology, exact moment/minor
polynomial expansions, coefficient certificate and scalar-field
transfer. The other placement uses the already checked pencil
arithmetic from the high-off leaf. The original saturated dimensions,
degree-four separator, physical late chart, dense-width lemma,
and rooted \(E_5,F_5\) application are documented mathematical
inputs; this is not an end-to-end native weighted tableau theorem
in the reviewed `HasOrder` API. At shift two over characteristic
zero, the existing lower census now leaves only one off clock
or five off clocks with six clean labels. The shift-one problem
and the ordinary order-eleven stage bound do not follow.
