# Four dirty labels are impossible in a rational rank-three order-five port

This closes the four-distinct-dirty-label alternative of the
[rank-three port census](../erk10-rank-three-port-labels/README.md).
The setting is six rational strict explicit rows with actual order-five
weights at horizon one and \(\dim F_5\le3\).
No sixth-order row or output condition is used. Together with the
[two-label exclusion](../erk10-rank-three-port-two-labels/README.md),
this leaves only a single dirty clock label for this low-rank port
problem; repetitions at that one label remain separate.

## Actual inputs and output moments

With \(\boldsymbol d=A\boldsymbol c-\boldsymbol c^2/2\) and
\(C=\operatorname{diag}(\boldsymbol c)\), the census gives
\[
 F_5=\operatorname{span}(\boldsymbol d,C\boldsymbol d,C^2\boldsymbol d).
\]
The four dirty rows have different clocks, and \(d_i=P(c_i)\) on them
for a nonzero quadratic-or-lower polynomial \(P\), using the genuine
size-five column \(\boldsymbol d^2\).
Only the origin and one other row are clean. The latter has nonzero
clock \(\eta\), is pure through derivative size five, and must be
physical row five or six. Let \(b_o,b_\eta\) denote the output
weights on these two actual physical rows.
The other weights are all nonzero: on the four dirty rows
\((b_i d_i)_i\) annihilates degrees \(0,1,2\), hence is proportional
to their nonzero barycentric cofactor vector. If the multiplier
were zero, output would be supported just on the origin and \(\eta\),
which cannot even have rational scalar precision four.

Write \(JQ(x)=\int_0^x Q(X)\,dX\), \(I Q=JQ(1)\).
By elementary bush moments and the three actual defect annihilations,
\[
\begin{split}
 I P&=b_oP(0)+b_\eta P(\eta),\\
 I (XP)&=b_\eta\eta P(\eta),\\
 I (X^2P)&=b_\eta\eta^2 P(\eta).
\end{split}
\]
The pure clean row reads every polynomial of degree at most three
as its true primitive at \(\eta\).
It cannot read itself; on its predecessors \(C\boldsymbol d\)
is the evaluation of \(XP\) (also at the origin), and
\(A(C\boldsymbol d)\in F_5\) vanishes at the clean row.
Thus \(J(XP)(\eta)=0\).

We have \(P(\eta)\ne0\): otherwise \(I(XP)=I(X^2P)=0\)
forces \(P\) proportional to \(P_0=X^2-6X/5+3/10\).
That polynomial has no rational root because its discriminant
is \(6/25\). We also have \(P(0)\ne0\).
If \(P(0)=0\), write \(P=aX^2+cX\).
On the same clean predecessors \(\boldsymbol d\) then equals
the evaluation of \(P\), so \(A\boldsymbol d=0\) at the clean row
forces \(a\eta^3/3+c\eta^2/2=0\).
Its preceding marked relation gives
\(a\eta^4/4+c\eta^3/3=0\).
Since \(\eta\ne0\), these imply \(a=c=0\), a contradiction.

These conclusions allow the dirty clock set to contain zero, or the
clean clock to coincide with a dirty label. The distinctness used here
is only among the four actual dirty rows.

## Two weighted primitive identities

Use \(\boldsymbol e_o,\boldsymbol e_\eta\) for the coordinate vectors
of the physical origin and sole nonorigin clean row.
Replacing polynomial reads of \(A\) by their primitives and true
grade-at-most-five defects gives
\[
\begin{split}
 (JP)(\boldsymbol c)-P(0)A\boldsymbol e_o
                         -P(\eta)A\boldsymbol e_\eta &\in F_4,\\
 (J(XP))(\boldsymbol c)-\eta P(\eta)A\boldsymbol e_\eta &\in F_5 .
\end{split}
\]
Indeed subtract the first formula from \(A\boldsymbol d\), and the
second from \(A(C\boldsymbol d)\); each replacement of a monomial
read uses degrees at most two in the first, three in the second.
In particular these arguments do not apply \(A\) to \(C^2\boldsymbol d\).

Weight the second formula by \(\boldsymbol b^\top\).
Since \(I(J(XP))=I((1-X)XP)\), the three output moments give
\[
 \eta P(\eta)\bigl[
   (\boldsymbol b^\top A)_\eta-(1-\eta)b_\eta
                 \bigr]=0.
\]
Both scalar factors outside the bracket are nonzero, so the
clean physical column pays literal \(D(1)\).

If the clean row is sixth, \(A\boldsymbol e_\eta=0\).
Thus \((1-\eta)b_\eta=0\). When \(\eta\ne1\) this gives \(b_\eta=0\).
When \(\eta=1\), the local \(J(XP)(\eta)=0\) is already \(I(XP)=0\),
which again forces \(b_\eta=0\) by \(P(\eta)\ne0\).
Dropping the last output-zero row leaves five-stage order five,
contrary to the real strict stage floor. This closes row six without
a generic clock or pivot hypothesis.

## Literal D(1) when the clean row is fifth

Weight the first primitive formula, using the clean \(D(1)\)
identity just obtained. The equations
\[
 I(JP)=I((1-X)P)=b_oP(0)+(1-\eta)b_\eta P(\eta)
\]
give \((\boldsymbol b^\top A)_o=b_o\), since \(P(0)\ne0\).
The actual \(D(1)\) residual is supported only on the four dirties.
For every \(j=0,1,2,3\) its pairing with \(\boldsymbol c^j\)
vanishes: the ordinary unary-bush condition is
\(\boldsymbol b^\top A\boldsymbol c^j=1/[(j+1)(j+2)]\),
which is also \(\boldsymbol b^\top(1-\boldsymbol c)\boldsymbol c^j\)
by the scalar moments. Four distinct dirty sites give an invertible
Vandermonde, hence full literal \(D(1)\).
At the last dirty row its output weight is nonzero, so its clock is 1.

The case \(\eta=1\) can already be rejected without dividing by
\(1-\eta\): the local marked relation and \(I(XP)=b_\eta\eta P(\eta)\)
give \(b_\eta=0\), while the clean \(D(1)\) column reads
\(b_6a_{65}=(1-\eta)b_\eta=0\). Since \(b_6\ne0\), row five is
both unreferenced and output zero, so dropping it would give
five-stage order five. The next hull proof also permits \(\eta=1\)
as an arithmetic edge case.

## Two scalar gates force an impossible hull

The three dirty predecessors of the clean fifth row have distinct
clocks \(e,f,g\). Put \(H(X)=(X-e)(X-f)(X-g)\).
The literal clean row has predecessors \(0,e,f,g\), so
\(JH(\eta)=a_{51} H(0)\); its \(A\boldsymbol d=0\) similarly
gives \(JP(\eta)=a_{51}P(0)\). Therefore
\[
 R(X)=H(X)-H(0)P(X)/P(0)
\]
is a monic cubic with \(R(0)=0\) and \(JR(\eta)=0\).
Its degree-four final quadrature gives
\[
 I((X-1)R)=b_\eta(\eta-1)R(\eta).
\]
Indeed \((X-1)H\) vanishes at every dirty label, including the
last at 1. On the dirty rows the correction term is proportional
to \((C-I)\boldsymbol d\), killed by the final weights.
The origin contributes zero because \(R(0)=0\).

The two gates also hold with \(R=XP\) after normalizing \(P\) monic.
Here \(P\) really has degree two: in the equations
\(J(XP)(\eta)=0\), \(I((X-\eta)XP)=0\), the coefficient matrix
on its linear and constant terms has determinant
\(-(12\eta^2-20\eta+9)/72\) after dividing the local equation by
\(\eta^2\). This is nonzero because the quadratic has negative
discriminant; zero leading term would force \(P=0\).
Thus \(R-XP=\alpha X(X-2\eta/3)\), by the local integration gate.
The final gate says \(\alpha\Delta=0\), where
\[
 \Delta=\frac{4\eta-3}{36}
          -\frac{b_\eta(\eta-1)\eta^2}{3}.
\]

For clarity, exact solution of the two equations for the monic
coefficients \(P=X^2+cX+d\) gives
\[
 c=-\frac{3(15\eta^3-10\eta^2-15\eta+12)}
              {5(12\eta^2-20\eta+9)},\quad
 d=\frac{3\eta(20\eta^2-35\eta+16)}
              {10(12\eta^2-20\eta+9)} .
\]
Using the genuine \(I(XP)=b_\eta\eta P(\eta)\), it follows that
\[
 \Delta=\frac{(10\eta^2-15\eta+6)(12\eta^2-20\eta+9)}
                   {36(30\eta^3-80\eta^2+75\eta-24)} .
\]
The denominator is nonzero because
\(P(\eta)=\eta(30\eta^3-80\eta^2+75\eta-24)/
[10(12\eta^2-20\eta+9)]\ne0\).
Both numerator quadratics are strictly positive over \(\mathbb Q\).
The Lean nonzero proof instead clears the denominator directly.

It follows \(R=XP\), so \(H=P(X)(X+H(0)/P(0))\).
But at each of the three distinct dirty predecessor clocks \(P\)
is nonzero. All three would have to equal the sole root of the
last linear factor. This is impossible and closes the row-five
placement.

## Replay and native scope

    python -B audit.py
    sha256sum -c sha256.txt

From the project's ai-generated/lean directory:

    lake env lean RKCert/ReviewedNative/ERK10RankThreePortFourLabels.lean

The Lean endpoint checks the two polynomial coefficients and the
nonzero hull pressure from three explicit scalar conditions. It is
not a native theorem deriving \(D(1)\) from a literal tableau.
The rooted bridges and both physical chronologies are argued above.
