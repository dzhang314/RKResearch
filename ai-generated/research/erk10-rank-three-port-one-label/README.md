# One dirty clock cannot support a rational six-stage rank-three order-five port

Work over \(\mathbb Q\) with six strict explicit rows, a genuine
ordinary order-five output at a nonzero horizon, and
\(\dim F_5\le3\) for the actual secondary defect space.
This complements the [two-label](../erk10-rank-three-port-two-labels/README.md)
and [four-label](../erk10-rank-three-port-four-labels/README.md)
closures and the [general label census](../erk10-rank-three-port-labels/README.md).
The result concerns actual order five and no order-six equations
are used.

The common clock \(e\ne0\) of all dirty rows is the second row clock.
Write
\[
\begin{split}
 \boldsymbol d&=A\boldsymbol c-\boldsymbol c^2/2,\qquad
 \boldsymbol V=A\boldsymbol d,\qquad
 \boldsymbol U=A\boldsymbol c^2-\boldsymbol c^3/3,\\
 \boldsymbol W&=A\boldsymbol V,\qquad
 \boldsymbol G=A\boldsymbol c^3-\boldsymbol c^4/4 .
\end{split}
\]
The census gives \(\dim F_4=2,\dim F_5=3\). The vectors
\(\boldsymbol d,\boldsymbol V\) are independent: otherwise
\(\boldsymbol V=0\) by nilpotence, so row three uses only the origin
and either duplicates the origin or the dirty second row.
They therefore span \(F_4\), and
\(\boldsymbol U=(2e/3)\boldsymbol d+\lambda\boldsymbol V\)
from row two. The genuine grade-five columns include
\(C\boldsymbol V,\boldsymbol W,\boldsymbol G,\boldsymbol d^2\).
The output annihilates every column of \(F_5\).

A rational scalar rule of degree four needs at least three distinct
nonorigin live sites, by the anchored three-site obstruction.
Thus there are at most three dirty physical rows (the dirty group
can contribute at most one site). The one-physical-dirty case is
the [one-starter obstruction](../erk10-seven-opening-pure-high/README.md),
which already shows \(\dim F_5\ge4\) in that case; equivalently one
can apply its projected dimension-two low-rank argument directly,
with no FSAL required.

## Unequal nonzero dirty values

If a clean row has nonzero \(V_i\), then
\(\boldsymbol d,\boldsymbol d^2,\boldsymbol V\) span \(F_5\).
The clean restriction of \(C\boldsymbol V\) is proportional to
that of \(\boldsymbol V\), so only one clean clock can have \(V_i\ne0\).
For two dirty rows with unequal defects, their output weights
are both zero by the two equations on \(\boldsymbol d,\boldsymbol d^2\).
Thus all three clean nonorigin rows must be live at distinct
nonzero sites, and \(\boldsymbol b^\top\boldsymbol V=0\) kills
the single nonzero clean entry, impossible.
For three dirty rows, both clean nonorigin rows and the single
dirty site must be live and distinct, in particular their clocks
are not \(e\). Then \(\boldsymbol b^\top(C-eI)\boldsymbol V=0\)
kills the single nonzero clean entry instead. So in either case
\(\boldsymbol V\) vanishes on all clean rows.

Normalize \(e=1\). Row three is dirty: if clean,
\(V_3=0\) forces its tap to the only dirty predecessor to vanish,
and then \(C(2)\) forces clock zero and the literal origin row.
Let \(y\ne0\) denote this second dirty value, \(z=-1/2\) the first.
If \(y=z\) these two rows are literal duplicates (only the
initial dirty row could contribute to the nonconstant read),
so \(y\ne z\).
Now \(V_3=z(y-z)\ne0\) and row three gives
\(\lambda=-2/3\).

Before a third dirty row, the first clean nonorigin row has
\(V=0\) and only the two initial dirty predecessors at clock 1.
Their total tap is fixed by \(C(2)\), and their split by \(V=0\)
because \(z\ne y\).
If the clean clock is zero all taps except the origin vanish and
the row duplicates the origin. Otherwise \(C(3)\) is exact by
\(\boldsymbol U=(2/3)\boldsymbol d-(2/3)\boldsymbol V\) and
forces clock \(p=3/2\). At it
\(W_p=-9/32\) (the split equation) and \(G_p=-9/64\)
(the cubic primitive).
On the preceding two dirties
\(\boldsymbol G-\boldsymbol d/2+\boldsymbol V=0\) and
\(\boldsymbol W=0\), by their literal first and second strict rows.
Consequently \(\boldsymbol d,\boldsymbol V,\boldsymbol W\)
are a basis of \(F_5\) whenever this clean row precedes a third dirty,
and comparison at the first three nonorigin rows gives
\[
        \boldsymbol G-\boldsymbol d/2+\boldsymbol V=\boldsymbol W/2 .
\]

If a second clean row occurs before any third dirty, its only live
predecessor sites are that same pair at 1 and the first clean \(p\).
Let \(S\) be the total tap into the two early dirties.
Its condition \(V=0\) fixes the split and gives \(W=-S/4\),
since it only reads \(V_3\ne0\) among those two and the clean
predecessor has \(V_p=0\).
Writing \(a\) for its tap into \(p\), its moments at clock \(q\)
then read
\[
 S+pa=q^2/2,\quad (2p/3)S+p^2a=q^3/3,\quad
 (p^2/2)S+p^3a=q^4/4 ;
\]
here \(p=3/2\) and the last identity uses \(G=W/2\).
The [exact singleton pressure](../erk10-rank-three-port-two-labels/README.md)
forces \(q=0\) or \(q=p\). In either case the actual first two
linear equations give \(a=0\), and give precisely the old total
dirty tap for the origin or first clean row. The same split and
row sum then make it an exact duplicate. This excludes two dirty
rows and any two-clean-before-third chronology with three dirties.

For three dirty rows, if \(\boldsymbol d^2\notin F_4\), then
\(F_5=\operatorname{span}(\boldsymbol d,\boldsymbol V,\boldsymbol d^2)\)
is zero on all clean rows. Both nonorigin clean rows are truly
pure through derivative size five, so by the tall four-tree they
must be physical rows five and six. The first can only read the
origin and the repeated dirty clock, and cannot pay scalar degree
three on just those sites (the two-site gate in the linked packet).
Thus \(\boldsymbol d^2\in F_4\). As the dirty values differ and
\(V_2=0\), this condition is
\[
        V_i=(z/y)d_i(d_i-z)
\]
on the dirties; its constant is calibrated at row three.

If the third dirty precedes the first clean, its predecessors all
have scalar clock 1 or 0. With \(x=d_i\) its new defect, the
rank-four-grade relation on \(\boldsymbol U\) gives
\(V_i=z(x-z)\) and the total dirty tap \(x-z\).
Since the two preceding defects are \(z,y\), the tap into the
second one is therefore zero. Comparison with the previous
display forces \(x=z\) or \(x=y\), and the row exactly duplicates
the corresponding initial one.

The only remaining unequal-defect chronology is dirty, dirty,
clean, dirty, clean after the origin. Its third dirty row sees
the two early dirties and the clean \(p=3/2\). Put \(x=d_i\),
\(v=V_i\), \(S\) the sum of its two dirty taps, \(H\) its tap
into \(p\), and \(a\) the tap to the second dirty. The exact equations
are
\[
\begin{split}
 S+(3/2)H&=1/2+x,\\
 S+(9/4)H&=1/3+(2/3)x-(2/3)v,\\
 -S/2+(y+1/2)a&=v,\qquad 4yv=-x(2x+1),\\
 S+(27/8)H-1/4-x/2+v+(2y+1)a/8&=0 .
\end{split}
\]
The last line is the actual \(\boldsymbol G-\boldsymbol d/2+
\boldsymbol V-\boldsymbol W/2=0\).
The replay gives residual \((x-y)(2x+1)/(16y)\), so \(x=y\)
or \(x=z\). In both cases \(H=a=0\), \(S=x-z\); its literal
row coincides with the corresponding earlier dirty row. This
completes all unequal values.

## Equal nonzero dirty values

With equal dirty values the dirty group aggregate output is zero.
Three distinct nonorigin live sites can only arise from three
clean rows, so there are exactly two dirty physical rows.
Row three cannot be the second dirty: the two dirty clocks and
defects coincide and both rows could read only the origin without
changing that defect. Instead row three is the first clean stage.
Normalize its nonzero clock to 1, keeping the dirty clock denoted
\(e\), and let \(\xi\ne0\) denote the rescaled final horizon.
The dirty defect remains \(d_2=-e^2/2\) at both dirty stages.
Now \(V_3=-e/4\), and evaluating at the first clean row gives
\(\lambda=-2+4/(3e)\).

After incorporating the \(\lambda\boldsymbol V\) term, the
adjusted quadratic input at either dirty clock is \(2e/3\);
all clean entries still have their true squared clocks.
If the second dirty is row four, its linear and adjusted
quadratic read targets at clock \(e\) are both zero (their
ordinary terms cancel their equal-defect terms). If \(T\) is
\(e\) times its first dirty tap and \(U\) its tap into the
first clean stage, this reads \(T+U=(2/3)T+U=0\).
Thus it again duplicates row two. So row four is clean with
nonzero clock \(r\ne1\).

The next chronological use of the size-five flag is the
[fifth clean stage calculation](../erk10-seven-opening-pure-high/README.md):
\(V_4=-e r^2(3-2r)/4\) and
\(a_{43}=r^2(r-1)\).
For \(r\ne3/2\), \(\boldsymbol d,\boldsymbol V,C\boldsymbol V\)
form a basis; the ratios from the first two clean stages give
\[
 W_i=\frac{c_i-1}{3-2r}V_i,\qquad
 G_i=(e^2/2)d_i+
  \left(1/e-2e+\frac{(r-1)(c_i-1)}{e(3-2r)}\right)V_i .
\]
For \(r=3/2\), \(\boldsymbol d,\boldsymbol V,\boldsymbol W\)
instead form the basis, \(C\boldsymbol V=\boldsymbol V\),
and \(G_i=(e^2/2)d_i+(1/e-2e)V_i+W_i/(2e)\).
These formulas follow by comparing also the dirty second row,
where both \(V,W\) vanish and \(G_2/d_2=e^2/2\).
Thus if the fifth row is clean, exactly the same two small scalar
gates in the linked packet force its clock to be among
\(0,1,r\). This contradicts the three distinct live clean sites.

The second dirty is therefore row five. Use
\(T=e a_{52},U=a_{53},J=a_{54}\).
The nonconstant target of the first two equations is zero as
in the row-four case. The pure ordinary cubic term also cancels
against \((e^2/2)d\) at this dirty row. If \(r=3/2\) the
remaining homogeneous system has the three rows
\((1,1,3/2),(2/3,1,9/4),(1/2,9/8,27/8)\);
its determinant is \(3/32\) and the row duplicates the initial one.
If \(r\ne3/2\), the exact system is instead
\[
\begin{split}
 T+U+rJ&=0,\qquad (2/3)T+U+r^2J=0,\\
 (3-2r)(U+r^2(3-2r)J)&=2(e-1)T,\\
 (3-2r)(U+r^3J)+(3-2r+(r-1)(e-1))T/2&=0 .
\end{split}
\]
If \(J=0\), the first two equations force \(T=U=0\), duplicating
the origin-forward dirty row. Otherwise the two checked
homogeneous minors force \(e=(2r^2-r)/3\) and then \(r=2\),
hence \(e=2\).

The remaining clean sixth clock \(z\) is distinct from \(0,1,2\).
Its taps into both dirty rows combine in the linear term \(T_6\)
because both have clock 2 and the same defect. Its additional
singleton clean predecessor at 2 has zero defect and normal inputs.
Its second, adjusted cubic, and cubic-defect equations on these
aggregates are exactly the [last-clock system](../erk10-seven-opening-pure-high/README.md)
with determinant \(2-z\), giving \(T_6=z^2(2-z)/2\).
The true \(\boldsymbol b^\top(C-2I)\boldsymbol V=0\) kills
all physical stages at 2, so reads
\(w_1+z^2(z-2)^2w_z=0\).
Here \(w_1,w_z\) are the aggregate clean output masses of the
scalar degree-four rule on \(0,1,2,z\), since the dirty pair's
aggregate is zero. The same weighted scalar gate gives
\(\xi^3(3\xi^2-15\xi+20)/15=0\), impossible over \(\mathbb Q\).

## Consequence and replay

All one-label multiplicities are excluded at low rank. Together
with the other label cases this proves **every rational strict
six-stage ordinary order-five tableau has \(\dim F_5=4\)**.
The upper bound is immediate: both the origin and the actual
output annihilate \(F_5\), and those two functionals are independent
by the nonzero first moment. As proved in the
[seven-opening pure-high packet](../erk10-seven-opening-pure-high/README.md),
this leaves at least two missing model modes after a true FSAL.
Hence that strongly pure continuation is impossible even without the
original one-starter restriction. A different, non-pure rational15
architecture is not ruled out.

    python -B audit.py
    sha256sum -c sha256.txt

From ai-generated/lean:

    lake env lean RKCert/ReviewedNative/ERK10RankThreePortOneLabel.lean

The two named Lean endpoints pay the homogeneous equal-defect
and third-dirty scalar contradictions. The literal grading, support,
and chronological merges are established mathematically above.
