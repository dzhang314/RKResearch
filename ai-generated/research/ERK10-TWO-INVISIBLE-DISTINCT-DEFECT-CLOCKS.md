# Two distinct invisible quadratic-defect clocks force consecutive ghosts

Work over any characteristic-zero field. Suppose a strict explicit
fourteen-stage order-ten tableau has exactly two zero output
weights and all its original quadratic defects are invisible.
Assume both ghost entries of \(d=Ac-c^2/2\) are nonzero and that
their clocks are distinct. Then those ghosts must be **physical
2 and 3**, the old cubic pure rank is **\(f_3=2\)**, and their
actual outgoing columns on live rows satisfy the specified
proportionality at the end of this note.
This is a necessary normal form, not an exclusion of two
adjacent ghosts or a stronger unconditional stage floor.
Cases with only one nonzero invisible defect clock are outside
the hypotheses.

## 1. The actual ghost indicator axes and early rank

The basic [ERK10 equality ranks](ERK10-FOURTEEN-STAGE-EQUALITY.md)
give \(f_5=5,f_6=7\), strict lower pure growth, genuine old
endpoint exactness through grade four, \(e_{14}\in E_5\),
and \(b_{14}\ne0, c_{14}=1\).
Physical row 2 has \(c_2=\theta\ne0\), since otherwise it
duplicates the origin, and its quadratic error
\(d_2=-\theta^2/2\ne0\). Thus it is a ghost. Denote the
other ghost by \(g>2\).
By the distinct clocks, the two actual pure columns \(d,Cd\)
isolate each individual ghost indicator in grade three.
Let \(G=\langle e_2,e_g\rangle\) be their actual two-dimensional
space. Since \(f_3\le3\), there are two possible ranks.

If \(f_3=2\), then \(F_3=G\), so every live row is original
point exact through grade three, and \(A d\in F_3\) vanishes
on all live sites. If \(g>3\), original physical 3 is live.
Its quadratic equation gives \(A_{32}\theta=c_3^2/2\).
A zero \(c_3\) would be a literal duplicate of origin by that
equation and the row sum. Thus \(A_{32}\ne0\) and
\((A d)_3=A_{32}d_2\ne0\), contradiction.
This proves \(g=3\) in rank two.

Suppose instead \(f_3=3\). Choose **any** genuine old
grade-three pure direction independent of \(G\) and remove its
two ghost coordinates using \(e_2,e_g\); call the resulting
ghost-zero vector \(p\). Then \(p|_I\ne0\) and \(F_3=G+Kp\).
Do not require \((Ad)|_I\ne0\) when the ghosts are adjacent:
the rank-three contradiction below needs only the actual
third pure direction and therefore covers a cubic primitive
as well as a nonzero \(Ad\)-advance.

## 2. Third pure direction: exact profile and actual late removal

Continue with \(f_3=3\) and its chosen live direction \(p\).
Then \(F_3=G+Kp\) by rank. If \(p\) used just one clock,
all these directions would be clock-invariant, so the
original grade-three outgoing Hermite bound would force
\(f_4\ge5\), impossible. Hence \(p,Cp\) give two independent
live directions in the exact
\(F_4=G+\langle p,Cp\rangle\).
If \(p\) had exactly two active labels this space would
again be invariant, giving \(f_5\ge6\).
With at least three labels the exact rank gives
\(F_5=G+\langle p,Cp,C^2p\rangle\).
Exactly three labels would make that invariant and force
\(f_6\ge8\); hence at least four labels occur.

The terminal kernel in \(F_6\) has dimension six:
the genuine \(e_{14}\in E_5\) has zero numerical advance
and a scalar primitive of value \(b_{14}\ne0\) at 1,
so subtracting its clock model gives a nonzero terminal
pure value. The six directions \(G+p\mathcal P_{\le3}(c)\)
are old pure of grade at most six, are independent, and
vanish at the terminal. They therefore fill the kernel.
The actual pure grade-six square \(p^2\) belongs there.
It follows that a literal cubic-or-less \(R\) fits \(p_i\)
at every live \(p\)-active row; the division is only by
that row's nonzero \(p_i\).

For completeness there is already an independent literal
cutoff in this branch. The actual \(A e_g\) is pure grade
four, so it restricts to an affine multiple of \(p\) on
the live set. Two different active \(p\) clocks before \(g\)
would force its two affine coefficients to vanish.
It would then be zero at every live row, and its remaining
ghost entries are zero by strictness (only \(2\) and \(g\)
are ghosts and neither is later than \(g\)).
Thus **every actual outgoing tap** of physical \(g\)
would vanish, and its zero output weight makes it
literally removable. No virtual replacement of a stage
or extrapolation of \(\bar A\) is used.

If \(g\ge5\), physical rows 3,4 are live. At physical 3
we have \((Ad)_3=d_2 A_{32}\ne0\) as in §1, so **for this
optional cutoff** we may choose \(p=Ad\) with its ghost
values removed. Put \(t=c_3\); in the early live positions
\(p_i=d_2 A_{i2}\).
At row 3 we know \(p_3\ne0,t\ne0\).
The original cubic defect \(A c^2-c^3/3\) is in \(G+Kp\);
its coefficient on \(A_{i2}\) at those live rows is
\(\theta^2-2\theta t/3\) by evaluation at physical 3.
The two actual quadratic and cubic equations at row 4
therefore give
\[
                          A_{43}=\frac{c_4^2(c_4-t)}{t^2}.
\]
If \(c_4=0\) or \(c_4=t\), that same system and the row
sum literally duplicate physical 1 or 3, respectively.
So \(A_{43}\ne0\). Then \((Ap)_4=A_{43}p_3\ne0\).
Since \(Ap\in F_4\) projects to an affine times \(p\),
we must have \(p_4\ne0\). The two early active clocks
before \(g\) are distinct, proving the literal cutoff.

## 3. Scalar support, the terminal indicator, and the nonzero-origin exit

For this rank-three column, if the pooled \(bp\) row
is zero, every active clock uses at least two rows and,
by the literal \(R\)-profile, cancels ordinary mass.
At least four active labels would leave capacity at
most \(12-8=4\) ordinary sites, less than six.
The nonzero row has seven zero clock moments, so at
least eight distinct live active clocks occur.
If at least nine physical rows are active, at most
three live dormant rows remain, including 1 and 14.
The true grade-three mask
\[
                 T=R(c)-p-R(c_2)e_2-R(c_g)e_g
\]
and the ordinary \(R\)-weighted quadrature through
degree six give the
[single-middle paid seam](ERK10-INVISIBLE-GHOST-UNBALANCED-AFFINE-CLOSURE.md#2-a-paid-scalar-and-causal-lemma-when-the-literal-response-is-cubic),
contradiction. Both ghost indicators used here are
actually grade three, so every cutoff is unchanged.

Thus exactly eight active singletons and four live
dormant physical rows remain. The mask \(T\) above
has model \(R\) and is supported on those four rows.
Every pure old \(F_5=G+p\,\mathcal P_{\le2}(c)\)
vanishes at the four dormant rows: they are truly old
point exact through grade five.

Use the actual \(e_{14}\in E_5\). If its model is \(P\),
the pure part projects to \(p S(c)\) for \(\deg S\le2\).
At the eight distinct active clocks \(P+RS=0\);
both polynomials have degree at most five, so the
identity holds globally. In particular \(R(1)\ne0\)
and \(S(1)\ne0\), since \(P(1)=1\) at terminal.
For each earlier dormant row with \(R(c_i)\ne0\)
we have \(S(c_i)=0\). Thus there are at most two
distinct such earlier support clocks (none can be 1).

If \(R(0)\ne0\), the scalar \(R\)-weighted quadrature
through degree six is consequently supported at
0, 1 and at most one interior distinct label \(w\).
Without an interior label the anchored Gram is
already impossible. Otherwise \((X-w)R\propto L_4\).
The grade-nine product \(A(CT)(1-C)T\) is still
numerically zero, even if dormant clocks repeat:
at every dormant 0 row the genuine grade-five evaluation
\(A(CT)\) equals \(J(XR)(0)=0\); at the first \(w\)
row it is zero by strictness, hence at **all** \(w\)
rows by their true same grade-five model. Physical 14
is killed by the right factor. This is the nonzero
single-middle scalar seam, contradiction.

## 4. The zero-origin two-middle exit

If \(R(0)=0\), there must be two distinct internal
support clocks besides the effective terminal. Otherwise
the usual anchored test on \((X-w)R\), with at most one
internal factor, gives a Gram contradiction or
\((X-w)R\propto L_4\); the latter is impossible since
\(L_4(0)=1\). The two internal clocks \(w,\omega\)
are the two actual other dormant physical rows, written
in chronological order. Write \(R=X H\) with \(\deg H\le2\).
The \(R\)-weighted quadrature tests
\((1-X)(X-w)(X-\omega)Q\), \(\deg Q\le3\), give
\[
                        (X-w)(X-\omega)H(X)\propto L_4(X)
\]
by the true \(X(1-X)\)-Gram.

The two old grade-four vectors \((C-w)T,(1-C)T\)
are supported from the later internal row onward and
through the later internal row, respectively. In particular
the first is zero at the old origin because **\(R(0)=0\)**.
The actual product of the advance of the first and the
second is zero by strictness (the advancing column is still
zero at the later internal row itself).
Its paid grade is \(4+1+4=9\).
But its scalar integral, up to nonzero scale, is
\[
   \int_0^1 J\!\left[X\,L_4(X)/(X-\omega)\right]\,
          X(1-X)\frac{L_4(X)}{(X-w)(X-\omega)}\,dX .
\]
The polynomial quotients are real formal identities,
not rational singular evaluations. The Lean companion
checks the exact nonzero distinct-root certificate.
In coefficient form the integral matrix at degrees
\(i=0,\ldots,3,\ j=0,\ldots,2\) is
\(1/((i+2)(i+j+4)(i+j+5))\).
Scaling the mixed integral by \(50400/196\) gives an
integer cross polynomial \(I(x,y)\), \(x=w,y=\omega\).
The three remainders of \(7Y^k I(x,Y)\), \(k=0,1,2\),
modulo \(L_4(x)\) and the cubic divided difference
\((L_4(Y)-L_4(x))/(Y-x)\) give the rows of a matrix
killing \((1,y,y^2)\) if both distinct roots give a zero
integral. Its determinant modulo \(L_4(x)\) is
\[
             -126(32130x^3-78855x^2+49995x-5531).
\]
The indicated cubic is coprime to \(L_4\) by the exact
Bézout constant \(45825482250241\).
Thus this final paid product cannot vanish.

## 5. The forced adjacent rank-two normal form

The two scalar exits exhaust \(f_3=3\). Thus
\(f_3=2,\ F_3=G\), and the earlier genuine row-3 argument
gives \(g=3\). The old grade-three pure space is supported
only on these two ghosts, so all live rows are point exact
through grade three. Since \(Ad\in F_3\), its literal
vanishing at every live row gives
\[
                A_{i3}=\kappa A_{i2},\qquad
                \kappa=-d_2/d_3\ne0 .
\]
Let \(\eta=c_3\), \(c_2=\theta\ne0\), and \(p_0=c_4\).
The first live stage after the two ghosts gives the actual
quadratic and cubic constraints
\[
     2 A_{42}(\theta+\kappa\eta)=p_0^2,\qquad
     3 A_{42}(\theta^2+\kappa\eta^2)=p_0^3 .
\]
If \(p_0=0\) and \(A_{42}\ne0\) the two parenthesized
factors would both vanish; subtracting \(\eta\) times
the first from the second gives
\(\theta(\theta-\eta)=0\), contrary to the clock guards.
Thus \(p_0=0\) would force both ghost taps and then the
origin tap zero, a literal duplicate. Consequently
\[
       p_0\ne0,\quad \theta+\kappa\eta\ne0,\qquad
       2p_0(\theta+\kappa\eta)=3(\theta^2+\kappa\eta^2).
\]
No invertibility of the individual ghost clock \(\eta\)
is needed. This is a necessary adjacent normal form, not
a claim that the residual chart has a solution.

[ERK10TwoInvisibleDefectClocksGate.lean](../lean/RKCert/ReviewedNative/ERK10TwoInvisibleDefectClocksGate.lean)
verifies the exact two-middle polynomial quotient, scalar
integral scaling, each determinant-row reduction and the
nonzero Bézout certificate, as well as the adjacent clock
formula. The original graded lifts and actual removal
premise are the mathematical deductions above.
