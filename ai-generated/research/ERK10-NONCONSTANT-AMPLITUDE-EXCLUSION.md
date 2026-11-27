# Nonconstant one-clock amplitudes cannot occur in the all-live ERK10 equality case

Work over any characteristic-zero field, with actual rooted order ten
on fourteen strictly explicit stages and with every output weight
nonzero. This case uses the
[equality and weighted-transpose ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md)
through grades four and five, not an assumption of common grade-five
pure models. Assume \(Cd=\theta d\) for the actual quadratic residual
\(d=Ac-c^2/2\), but its nonzero amplitudes are not constant.
Then **no such chart exists**. The constant-amplitude
[two/three-carrier cases with at least three active labels](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md)
and charts with zero output weights are separate.
No unconditional change to the 14–15 stage interval is claimed.

## A second clock, a degree-five cubic amplitude, and a short core

The shifted-nine tap floor in both orientations gives the live taps
at \(2,1\) and \(14,13\), so the common pure \(F_2\) places the
nonzero quadratic residuals at \(\theta=c_2=c_{13}\ne0,1\).
Set \(w=Ad\). It is independent of \(d\), since otherwise
\(\langle d\rangle\) would be \(A,C\)-invariant and the triangular
partial-inverse argument on \(Ac-c^2/2\) would put \(c\) there.
The paid grade-three noninvariance gives
\(F_3=\langle d,w\rangle,\ F_4=\langle d,w,Cw\rangle\).

The vector \(w\) has nonzero values at exactly one numerical clock
\(\psi\) outside \(\theta\). If it had none then \(F_3\) would be
C-invariant. If it had two, the expression of \(d^2\in F_4\) as
\(a d+(b+eC)w\) would force \(b=e=0\), contradicting the
nonconstant nonzero amplitudes. Write \(w_\theta,w_\psi\)
for its two actual coordinate restrictions, both in \(F_4\)
by the scalar clock projections. Then
\[
       d^2=d_L d+\nu w_\theta,\qquad
       w_\theta=d(d-d_L)/\nu,\qquad
       d_L=d_2=-\theta^2/2,\quad \nu\ne0 .
\]
Indeed the coefficient of \(d\) is fixed by row 2, where \(w_2=0\);
the nonconstant case forces the coefficient of \(w_\theta\) nonzero.
Thus \(F_4=\langle d,d^2,w_\psi\rangle\).
Also \(d^3=\nu d w+d_L d^2\) is a genuine pure **grade-five**
vector, since \(d\) ignores \(w_\psi\). It follows that
\(b d^j=0\) for \(1\le j\le5\), including \(j=5\) by the
pure product of \(d^2\) at grade four and \(d^3\) at grade five.
The moments \(b w_\psi=b w_\psi^2=0\) are paid at grades
four and eight.

The clock \(\psi\) is neither endpoint. In fact consider the
first physical clock not in \(\{0,\theta\}\), which exists by
polynomial separation. If \(w=0\) there, the row is point exact
through grade four, but its earlier numerical clocks are only
0 and \(\theta\). The two primitives of \(X(X-\theta)\)
and \(X^2(X-\theta)\) would force respectively the incompatible
values \(3\theta/2\) and \(4\theta/3\) at that nonzero clock.
Thus this first clock is \(\psi\ne0\), has nonzero \(w_\psi\),
and precedes the first nonzero clock outside \(\{\theta,\psi\}\).
In the weighted transpose, \(A^\star d=\lambda w+\mu d\)
with \(\lambda\ne0\) by common \(F_3\);
off the carrier it has the same active support. The reflected
argument forces \(\psi\ne1\) and locates an active \(\psi\)-row
before the first nonzero offcore row in the reversed order.

Call a numerical clock outside \(\{\theta,\psi\}\) **offcore**.
Every offcore row is point exact through grade four.
For \(G(X)=(X-\theta)(X-\psi)\), the actual grade-two
mask \(T=G(c)\) is supported on the offcore rows, contains
both endpoints, and satisfies exact \(G\)-weighted output
moments there through degree seven.
The first and reflected last clean boundary primitives
are paid by the unary steps of \(CT\) and \((1-C)T\).
The [clean-five mask transfer](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md)
applies verbatim: if there were at most five offcore physical
rows, the Beta and fixed-quartic tests or the genuine
mixed unary cut would contradict the
[clean-five scalar closure](ERK10-UNBALANCED-CLEAN-FIVE-EXCLUSION.md).
There are consequently **at most eight physical core rows**
at the clocks \(\theta,\psi\). This counts even rows at either
clock which happen to have zero defects.

## Census and elimination of the nonzero theta-amplitude measure

The pooled positive-degree moment measure \(b_i d_i\) on
nonzero \(\theta\)-amplitudes either vanishes at each distinct
amplitude or needs at least six distinct active amplitudes,
by its five exact zero moments. On the \(\psi\)-side
at least two active rows are needed by \(b w_\psi=0\).
If the theta measure is nonzero, the core budget is saturated:
six distinct nonzero theta amplitudes and two active psi
rows. The two psi rows have equal amplitude and opposite
weight by \(b w_\psi=b w_\psi^2=0\).
Thus the paid \(b w^3=0\) (grade nine) now also pays
\(b d^6=0\), since its psi contribution is zero and its
theta contribution is
\[
       \nu^{-3} b\bigl(d^6-3d_Ld^5+3d_L^2d^4-d_L^3d^3\bigr).
\]
Six positive-degree moments on six distinct nonzero
amplitudes force all six weights zero, contradiction.

In the remaining case every distinct theta amplitude
has zero pooled weight, hence at least two physical rows.
There are two or three distinct theta amplitudes under
the eight-row budget and the two required active psi rows.
If there are three, the core consists of three theta
opposing pairs and one uniform opposing psi pair.
If there are two and psi is uniform on its active rows,
\(F_4=\langle d,d^2,w_\psi\rangle\) is the direct sum of
three disjoint coordinate indicator lines, C-invariant and
closed under products. The
[native rank-three core obstruction](../lean/ERK-GRADE-EIGHT-OFF-CORE.md)
excludes this.
Otherwise since theta pools cancel all powers of \(d\),
its \(w_\theta^3\) contribution is zero.
Thus \(b w_\psi^3=0\) too. A nonuniform psi side
needs at least four physical rows, by the first three
positive-degree amplitude moments and all-live weights:
with at most three distinct amplitudes every group must
cancel, and two separate groups need four rows.
The budget is saturated: there are two theta pairs
and four active psi rows. The latter are either **two
opposing pairs of different amplitudes**, or **four
distinct amplitudes**. Three distinct amplitudes cannot
be paired in four rows; one amplitude was excluded.
This lists every remaining core presentation, without
assuming any vanishing weight.

## Both balanced four-pair presentations transfer the seam exclusion

The two presentations are:
(A) three theta amplitude pairs and one psi pair; or
(B) two theta amplitude pairs and two psi amplitude pairs.
All core scalar mass cancels, so the six offcore physical
rows are six distinct scalar sites and exactly the six
Lobatto clocks (the anchored quadrature argument).
Write their chronological clocks as \(0,u,w_0,y,v,1\).
Their \(G\)-values are already nonzero by definition.

A tag is the numerical clock and the pure local amplitude
of one of the four pairs. At grade four every vector has
the form \(P(c)+a d+b d^2+e w_\psi\), with \(\deg P\le4\),
so is constant on each tagged pair. To fit arbitrary
values on all four dirty tags, \(E_3=\mathcal P_{\le3}(c)
+\langle d,w\rangle\) suffices:
* In (A), the three distinct theta values of \(d\)
  are separated by \(1,d,w_\theta\), since \(w_\theta\)
  is a genuine quadratic in \(d\). Adjust the lone psi value
  using the independent polynomial values at \(\theta,\psi\).
* In (B), choose a multiple of \(w\) to fit the difference
  of the two psi values; then choose a multiple of \(d\)
  to fit the theta difference (accounting for the chosen \(w\)
  on theta). Fit the residual constants at the two clocks.

Adding \(G(c)L_1(c)\) at grade three fits arbitrary values
at any two additional offcore sites: their \(G\)-values are
nonzero and the term vanishes on all core tags.
In either forward or reflected direction, no tag repeats
before the third offcore row. If \(j\) is the first repeat
in that range, all preceding tags are distinct physical
labels, and the grade-three restriction to them is onto.
Its earlier copy and row \(j\) already agree on \(E_4\);
hence their incoming rows agree on \(E_3\) inputs.
Strictness and surjectivity force the **literal incoming
rows** equal, impossible in a minimal fourteen-stage method.
Indeed redirecting a literally identical row to its earlier
copy preserves every rooted condition and reduces stage count.
This argument does not require every pair to split at \(E_5\).

Therefore the third offcore row is at most physical 7,
and the fourth is at least 8; each half contains three
offcore and four core rows. If there is a tag repeated
within the first half, its second occurrence must be
row 7: the first nonzero offcore clock requires an
actual order-four method on its predecessors, hence at
least four predecessors, including at least three core
stages. The three prior distinct core tags are at rows
2–4, and the first and second interior offcore rows are
5,6. If \(E_3\) is onto their first six physical labels
there is a literal incoming duplicate as above.
Otherwise its rank there is five (it is onto the first five).
Take the nonzero \(E_3\) vector in that first-five kernel;
it also vanishes at row 6. Its model cannot be zero:
in (A) those three earlier distinct core tags include
at least two distinct theta amplitudes, on which the two
pure directions \(d,w\) restrict independently; in (B)
they include both clocks, again giving independence.
So its model is a nonzero multiple of
\(X(X-u)(X-w_0)\). The two literal point-exact unary
tests at \(u,w_0\) give \(u=2w_0,\ w_0=2u\), impossible.
Reverse the same argument to exclude a pair within the
other half. All four pairs cross the literal 7|7 split.

Grade four surjects onto each half: first fit core tags
as above, then use \(G(c)L_2(c)\) at grade four to
fit its three offcore coordinates. The one-dimensional
half-zero vectors \(V_L,V_R\) are zero at all core
rows, since each tagged pair crosses. They are nonzero
and supported on the three opposite offcore sites.
For their degree-four models \(P_L,P_R\), use the
actual representation \(P(c)+a d+b d^2+e w_\psi\).
In (A), vanishing at the three distinct theta amplitudes
forces \(P(\theta)=0\); it follows \(P(\psi)\ne0\),
because the model already vanishes at its three own
offcore clocks and cannot be zero (a pure \(F_4\) vector
has only core support). In (B), the two differing psi
amplitudes force \(P(\psi)=0\), similarly \(P(\theta)\ne0\).
Thus the two models after nonzero scaling have the same
nonzero residue modulo \(G\).

The exact
[balanced linear seam determinant](ERK10-BALANCED-SEAM-EXCLUSION.md)
now applies. The literal cut only needs that \(A V_L\)
vanish on the left and at the first right **offcore**
row \(y\), since its input is supported on the right
offcore sites. This is true strictly even if physical
row 8 is itself a core row. Similarly \(A^\star V_R\)
vanishes on the right and at its last left offcore row
\(w_0\). The actual grade-four probes are
\((C-v)(C-1)G(c)\) and \(C(C-u)G(c)\), respectively.
They pay the two annihilating mixed linear forms on
that same residue. The clock chronologies are among
the 24 fixed Lobatto permutations, and the earlier
axiom-free finite determinant is nonzero for all of them
over the characteristic-zero splitting field. This rules
out both balanced presentations.

## The last unbalanced presentation: four distinct psi amplitudes

Now there are two theta amplitude pairs and four distinct
active psi amplitudes. Let \(u\) be the first nonzero
offcore clock. As above there is a psi-active stage before it,
and \(A(C G(c))\) is zero at all rows up to \(u\) by strictness.
At each psi-active site the grade-four formula is
\(J[XG](\psi)+a\,w_\psi\) (other pure directions have
theta support). If two such distinct amplitudes occurred
before \(u\), this would force \(J[XG](\psi)=0\),
hence \(\psi=2\theta\). At the actual offcore row \(u\),
point exactness gives
\(0=J[X(X-\theta)(X-\psi)](u)=u^2(u-\psi)^2/4\),
impossible since \(u\) is offcore. Thus **exactly one**
psi-active row precedes \(u\).

Before \(u\) there can be at most one occurrence of each
theta tag and no offcore zero-clock duplicate.
Indeed until the first such repeat, \(E_3\) can match all
earlier physical values: use ordinary values at
\(0,\theta,\psi\), and \(d\) for the theta difference.
A repeated theta tag already agrees in \(E_4\), and a
zero-clock offcore row is point exact at 0 and equals
the origin in \(E_4\). Therefore either would have a
literal duplicate incoming row by the strict read argument.
As there are at most four distinct earlier rows, and the
actual preceding chart at \(u\) has order four, there
must be exactly four: origin, two different theta
amplitudes, and one psi-active row. The physical row
of \(u\) is 5.

Normalize \(\theta=1\) for the rest of this local calculation
and write \(p=\psi/\theta,\ u=c_5/\theta\) in these units.
The two theta defect values are \(\ell=-1/2\) and \(x\ne\ell\).
The normalized \(w_\theta\) values are \(0,x(x-\ell)/\nu\);
here \(\nu\) is understood in the same scaled units.
Let \(B_\theta,B_p\) denote the pooled incoming coefficients
of the actual clean row 5 at the two nonzero donor clocks.
Its exact reads of \(d,w\in F_3\) are zero, so
\[
                  B_p w_p=(\ell x/\nu) B_\theta .
\]
Indeed if the theta coefficients are \(B_1,B_2\), then
\(B_1\ell+B_2x=0\) and
\(B_2 x(x-\ell)/\nu=-(\ell x/\nu)B_\theta\).
Also
\[
 3(B_\theta+B_p p^2)=u^3,\quad
 4(B_\theta+B_p p^3)=u^4,\quad
 3u^2-4(1+p)u+6p=0 ,
\]
the last by the exact zero primitive of \(X(X-1)(X-p)\)
at the nonzero clock \(u\).
The actual cubic defect is
\(Ac^2-c^3/3=(2/3)d+\rho w\)
by evaluating at the first carrier in \(F_3\).

* In chronology \(1,1,p\) after the origin,
  before \(p\) the two nonzero donor clocks are just
  \(1,1\). At the second theta row \(Ac^2=Ac\);
  the cubic residual gives
  \(\rho\,x(x-\ell)/\nu=(x-\ell)/3\).
  Thus \(\rho=\nu/(3x)\).
  At the psi row likewise \(Ac^2=Ac=p^2/2\), so
  \(w_p=xp^2(3/2-p)/\nu\).
  Hence \(B_\theta=-p^2(3-2p)B_p\).
  Combining the exact quadratic and cubic moments above
  gives \(u=2\), and its last primitive equation yields
  \(p=2=u\), a core contact.
* In chronology \(1,p,1\), call \(a=A_{42},\,b=A_{43}\)
  the actual second theta reads at 1 and \(p\).
  At the first psi stage, \(w_p=\ell p^2/2\) and
  \(\rho=-2+4p/3\). At the second theta stage
  \(w_\theta=\ell a\), and the calibrated quadratic,
  cubic and amplitude equations are
  \[
     2a+2p b=2x+1,\quad
     2p a+3p^2 b-1=2x,\quad
     -\nu a=x(2x+1).
  \]
  They imply \(\nu(2-3p)=2p x\) after cancelling
  \(2x+1\ne0\). Consequently
  \((2-3p)B_\theta=p^3 B_p\).
  The two paid moment equations then force \(u=2p\),
  and the remaining primitive forces \(u=1\),
  again a forbidden core contact.

These are the only chronological orders since physical
row 2 is a theta carrier. This excludes the last
nonconstant-amplitude presentation.

[ERK10NonconstantAmplitudeGate.lean](../lean/RKCert/Research/ERK10NonconstantAmplitudeGate.lean)
checks the sixth-moment polynomial expansion, first-
offcore double-contact gate, and both local contact
systems. The unchanged 24-case check handles the
balanced cases. The tableau, filtration and interval
interpretations are provided mathematically, not as
a single native rooted-order theorem.
