# Two dirty clocks cannot occur in a rational rank-three order-five port

Assume a six-row strict explicit rational tableau with a genuine
order-five output, and \(\dim F_5\le3\) for the actual secondary
defect flag. This closes the two-dirty-label case of the
[rank-three port census](../erk10-rank-three-port-labels/README.md).
No stage-six condition is imposed. In particular a clean row is not
assumed to annihilate incoming size-five defect columns.

## Groups and support

Write \(\boldsymbol d=A\boldsymbol c-\boldsymbol c^2/2\);
its two group vectors \(\boldsymbol d_e,\boldsymbol d_f\) are its
restrictions to the two distinct dirty clock labels \(e,f\). The
second row clock \(e\) is nonzero. By the census,
\(F_4=\operatorname{span}(\boldsymbol d_e,\boldsymbol d_f)\) and
\(\dim F_5=3\). In particular, for
\(\boldsymbol U=A\boldsymbol c^2-\boldsymbol c^3/3\) and
\(\boldsymbol G=A\boldsymbol c^3-\boldsymbol c^4/4\), one has
\[
 A\boldsymbol d=\rho\boldsymbol d_f,\qquad
 \boldsymbol U=(2e/3)\boldsymbol d_e+\lambda\boldsymbol d_f.
\]
The first components follow from row two. Row three must be the
first dirty row at \(f\): at a clean row or a row with clock \(e\),
\(A\boldsymbol d=0\) would force \(a_{32}=0\).
It would then duplicate the origin if clean, or the second row if
at clock \(e\). Duplications contradict the strict stage floor.

The final output kills both group columns. A singleton dirty group
has zero output weight. Rational scalar precision four requires at
least three nonorigin active sites (the anchored three-site square
gate in the preceding packet). The possible number of sites is at
most the number of clean nonorigin rows plus the number of repeated
dirty groups, at most \(5-2=3\). Equality requires each group to be
singleton or double; each repeat to have a nonzero nonorigin aggregate
weight; and each clean nonorigin row to have its own distinct active
site. On live repeats the two nonzero defect values must differ,
else its group equation forces a zero aggregate. Hence if there
is a repeat, the genuine size-five column \(\boldsymbol d^2\) is
independent of both group columns and
\(F_5=\operatorname{span}(\boldsymbol d_e,\boldsymbol d_f,\boldsymbol d^2)\).
It vanishes on clean rows, making those rows pure through derivative
size five. Such incoming rows kill the two grade-four group
columns, **not necessarily** \(\boldsymbol d^2\).

## Two singletons and one repeat

With two singleton groups, the two initial dirty taps of any clean
row occur in a fixed ratio by \(A\boldsymbol d=0\).
They act as one effective donor in nonconstant clock moments.
Let \(p\ne0\) be the first clean clock. Its exact linear and
quadratic moments force the effective quadratic-to-linear ratio to
be \(2p/3\). Put \(\boldsymbol T=A\boldsymbol d_e\).
The restrictions of \(\boldsymbol G,\boldsymbol T\) to clean rows
are proportional, since \(F_4\) vanishes there, and the first
clean \(T\)-entry is nonzero. Thus after subtracting the
\(\boldsymbol G\) contribution the effective cubic-to-linear ratio
is \(p^2/2\) at every clean row, as read at \(p\) itself.
For the next clean clock \(q\), let \(y\) be its effective
linear term, and \(v\) its tap into \(p\). Then
\[
 y+pv=q^2/2,\quad (2p/3)y+p^2v=q^3/3,\quad
 (p^2/2)y+p^3v=q^4/4 .
\]
Their linear combination is \(q^2(p-q)^2/4=0\).
This is impossible because the clean sites are distinct and nonzero.

With one repeated group, the first clean row is pure through
size five. Its singleton dirty coefficient, when that stage precedes
it, must vanish by the corresponding degree-four group column.
Thus that row receives nonconstant moments on at most one
nonorigin site, the repeated clock. A nonzero row cannot integrate
degrees one, two, and three using the origin and only one other
site: normalized to unit horizon, the ratio of the first two moments
would give site \(2/3\), whereas the ratio of the first and third
would give site-square \(1/2\). This also covers an earlier row
before the repeat closes (then every dirty coefficient is zero).

## Two repeated groups

The preceding degree-three test forces the only clean nonorigin row
to be last, since any earlier row has at most one complete pair.
Normalize \(e=1\), \(s=f/e\ne0,1\), and let \(k=a_{32}\) in these
units. The original two defects are \(\delta_1=-1/2\) and
\(\delta_s=k-s^2/2\ne0\);
\(\rho=-k/(2\delta_s)\), \(\lambda=(k-s^3/3)/\delta_s\).

At the first repeated row compare with the initial row of the
same clock. Only the initial two dirty columns matter for the
nonconstant quantities. Their two tap differences are not both
zero because the defect changes. The equations for \(A\boldsymbol d\)
and \(\boldsymbol U\) therefore give a zero determinant:
* For a first repeat at 1 the rows are
  \((-1/2,\delta_s)\) and \((1/3,s(s-2/3))\).
  This gives \(k=s(1-s)\) and requires \(3s-2\ne0\).
* For a first repeat at \(s\) they are
  \((-1/2-\rho,\delta_s-\rho s)\) and
  \((1-\lambda,s(s-\lambda))\).
  This gives \(k=s^2(s-1)/(2s-3)\). The undivided
  determinant rejects \(2s-3=0\) because \(s\ne0,1\).

Let \(a,b\ne0\) be the new defects in chronological repeat order.
Every \(\boldsymbol Z\in F_5\) has the same slope
\[
       \frac{Z_{\rm new}/d_{\rm new}-Z_{\rm old}/d_{\rm old}}
            {d_{\rm new}-d_{\rm old}}
\]
on both pairs: it is its coefficient on \(\boldsymbol d^2\).
The nonzero denominators follow from the live weight splits.

For the two vectors \(\boldsymbol T,\boldsymbol G\) their slopes
follow from explicit read formulas. At repeated clock \(x=1,s\) with
new defect \(d\), the aggregate taps \(X,Y\) to clocks 1 and \(s\) solve
\[
  X+sY=x^2/2+d,\qquad X+s^2Y=x^3/3+\lambda_x d,\quad
  \lambda_1=2/3,\quad\lambda_s=\lambda.
\]
Then \(G=X+s^3Y-x^4/4\). When there is only one preceding row at
clock 1, \(T=-X/2\). Otherwise the new row repeats \(s\) and
has only one preceding row at \(s\), so \(T=\rho d-Y\delta_s\).
This gives the paired slopes using the same expressions evaluated
on the original two rows.

For chronology \((1,s,1,s)\), the determinant of the two columns
of \((T,G)\)-slopes is \(s(s-1)/(12ab)\). For \((1,s,s,1)\)
it is \(-s(s-1)(2s-3)/(12ab)\).
Both are nonzero by the guarded chronologies and distinct clocks.
The actual rank-three slope equalities would make the columns equal.
Thus neither chronology occurs.

Exactly one dirty label with several physical occurrences, or four
distinct dirty labels, are separate remaining cases. The present
exclusion does not bar unrelated order-ten constructions.

## Replay

    python -B audit.py
    sha256sum -c sha256.txt

From the project's ai-generated/lean directory:

    lake env lean RKCert/ReviewedNative/ERK10RankThreePortTwoLabels.lean

The SymPy replay starts from the exact moment formulas and reproduces
both initial repeat guards and both two-pair determinants.
The Lean scalar module checks the singleton and the two chronological
incompatibilities. The rooted grade and physical support reductions
are mathematical as stated above.
