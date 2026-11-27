# Grade-six moment obstruction for a sharp dense ERK11 prefix

Let an ordinary order-eleven strictly explicit tableau have 17 physical
stages. Over a characteristic-zero field its literal first eleven must
be a dense size-six chart, by
[the rank-free cutoff](ERK11-RANK-FREE-FIRST-ELEVEN-CUTOFF.md).
In the calculations below this means actual polynomial separation
through degree five and full numerical \(E_5^{\rm pre}=K^{11}\).
The conclusions proved **after** that premise hold over paid fields
as indicated, with no positivity requirement.

**Results.** On sixth-degree nominal aliases of this prefix the
four positive shifted moments have rank at most two (and at most
one if the final ordinary clock is not 1). This gives explicit
polynomial rank tests on the *actual* first eleven rows. In the
rank-two branch, the final clock is 1, the midpoint has five pure
directions, and the last five satisfy a tied-clock four-word
exception with all adjacent edges live. Also the **entire family**
with the repaired archive's first eight rows followed by three
uncoupled recipients is excluded, regardless of the three chosen
receiver clocks or their incoming coefficients from the first eight.
There is an exact three-alias certificate for the latter exclusion.

The fixed-family result does not classify every sharp dense chart.
The endpoint and one-mode general continuation cases remain open,
so the ordinary interval remains 17–18.

## A new conditional stage floor for genuine weighted prefixes

Work over a field paying all factorials \( (m+r)!\) used below.
Suppose the literal first eleven rows have full \(E_5^{\rm pre}\).
An actual row \(\rho\), exact for \(\ell_m\) through effective
size \(r\ge8\), has **last support at least \(r+5\)**.
Here the row can be a true tap or a newly reweighted exact row,
not necessarily a combination retaining the original weights.
It can be considered on its genuine truncated physical prefix.

Indeed put \(u=r-7\ge1\). The paid reverse flag \(R_u\) has
dimension at least \(u+\epsilon_\rho\), where \(\epsilon_\rho\)
records a nonzero first seed \((m+1)\rho A-\rho Y\).
It annihilates \(E_5\), since \(5+u+2=r\). If the row ended
within the first eleven, its actual prefix \(E_5\) would be the
whole coordinate space, impossible since \(R_u\ne0\).
Otherwise \(\dim E_5\ge11\) on that prefix. If
\(\epsilon_\rho=1\), the rank count gives
\(s_\rho\ge11+u+1=r+5\). If the first seed is zero,
strictness at the live terminal coordinate forces clock 1.
The reverse flag then also kills the actual terminal
coordinate direction \(e_{s_\rho}\). Either this direction
is in \(E_5\), already giving dimension at least twelve
since it is zero through the first eleven, or it adjoins
an extra dimension. Again \(s_\rho\ge12+u=r+5\).
This is a paid weighted count with **literal dense prefix**
as a premise, not a new unconditional weighted floor.

In particular an ordinary order-eleven extension of the
sharp first-eleven chart has
\[
       \operatorname{last}(bA)\ge15,\qquad
       \operatorname{last}(bA^2)\ge14,\qquad
       \operatorname{last}(bA^3)\ge13 .
\]
These are separate from the sharper restrictions in individual
terminal branches, and apply without a sign assumption.

## A finite rank test of arbitrary prefix data

Let \(\mathcal A_6^{\rm pre}\) be the nominal polynomials \(P\)
of degree at most six for which an actual rooted combination
through grade six is zero on the first eleven. These are actual
aliases, not just any polynomial satisfying some scalar tests.
Let
\[
   r_+=\operatorname{rank}\left(P\longmapsto
          (\ell_1(P),\ell_2(P),\ell_3(P),\ell_4(P))
                  \quad\text{on }\mathcal A_6^{\rm pre}\right).
\]
In the full tableau \(E_6^{\rm late}\) is its actual grade-six
subspace zero through row 11. Every alias has a lift into this
space, with the indicated read equal to
\((bA v,bA^2v,bA^3v,bA^4v)\) by paid order. Conversely an
actual late vector has such an alias model. Different nominal
models of the same actual vector have the same moment reads.
This identifies the *image* of the moment map without claiming
model separation in grade six.

Use \(\epsilon=[bA-bY\ne0]\), \(\eta=[c_{17}=1]\),
and \(H_i=E_i+\eta\,K e_{17}\).
The flag \(R_3\) has rank at least \(3+\epsilon\) and
annihilates \(H_6\), so \(\dim H_6\le14-\epsilon\).
First-eleven projection has rank eleven. The optional
auxiliary \(e_{17}\) lies in its kernel and is killed
by every positive tap, and \(\epsilon+\eta\ge1\).
Consequently
\[
                        r_+\le 3-\epsilon-\eta \le2.
\]
Adding the ordinary zeroth moment gives rank at most
\(3-\epsilon\) for \(\ell_0,\ldots,\ell_4\) together,
by counting in \(E_6\). Moreover \(r_+\) is **not zero**:
if all positive taps killed the late space they would
factor through first eleven on grade six. This would give
consecutive shifts 1 and 2 exact through size seven on the
same full grade-five prefix, contrary to the
[vanishing first-seeds obstruction](ERK11-SHARP-PREFIX-PURE-TAIL.md).

This is a finite determinantal condition before any choice of
late coefficients. Let \(V\) consist of the actual first-eleven
numerical columns for all rooted trees through size seven, and
let \(M_+\) be the four rows of their exact shifted moments
above. That numerical \(V\) has rank eleven. Then
\[
                     \operatorname{rank}
                 \begin{pmatrix} V\\M_+\end{pmatrix}
                        =11+r_+\le13 .
\]
This equality follows by selecting eleven domain columns
that give a numerical basis, and subtracting them to see
the rows on the kernel. All 14-by-14 minors must vanish.
The coefficients of these tests are exact paid rational
polynomials in the entries of the actual prefix.
The preceding bound \(r_+\le3-\epsilon-\eta\) already
uses the mixed rooted grading, so it is not a mere count
of different target moment numbers.

## Rank one unless there is a five-slot endpoint exception

Suppose \(r_+=2\). The count above forces
\(\epsilon+\eta=1\) and \(\dim H_6=14-\epsilon\).
Also the full midpoint must have \(\dim F_5=5\):
if its pure rank were six, its one-dimensional late
\(E_5\) kernel under the dense prefix would be pure,
giving one more killed direction in \(H_6^{\rm late}\)
independent of the auxiliary endpoint. Pairing ranks
would then give \(r_+\le1\).

Reanchor the detector proof at \(g=6,r=11,L=4,k=12\),
where the spare is exactly zero. Suppose the
penultimate tap \(bA^3\) is zero on the actual \(H_6\)
vectors zero through row 12. Then the zero-spare
cutoff at this anchor applies: its budget-four proof
is the same as [the audited budget-four step](WEIGHTED-ORDER-NINE-FOUR-TAP.md).
In detail, the exact forward caps are \(\dim H_{6+j}\le
\dim H_6+j\) for \(j\le3\); the short clock closure
has delay at most 2 and leaves one nonendpoint charge
to the paid positive penultimate test; with longer
closure the terminal annihilator at degree nine has
dimension \(\epsilon\in\{0,1\}\). Thus the only long
charts are the single invariant row, the single
noninvariant detector, and the augmented detector.
Their Newton indices are 3 or 4, and all words and
commutator tests stay inside this budget. The only
size guard in the missing-shift/reweighting steps is
\(k+1=13<N_*\) for actual retained sizes ten and nine
at their specified shifts. The just-proved
**conditional weighted floor** pays this, including
the size-nine reweighted row whose prefix still
inherits the literal dense first eleven. There is no
use of a generic budget-four penultimate theorem.

This cutoff through 12 would give rank at most one
on the vectors zero through 11, contradiction.
So there is an actual late vector \(w\) zero through
row 12 with \(bA^3w\ne0\).
The local five-slot [four-word result](WEIGHTED-ORDER-NINE-FOUR-TAP.md)
says its top tap \(bA^4w\) is also nonzero, and the
top-plus-penultimate exception forces \(c_{17}=1\).
Thus a **nonendpoint final stage requires \(r_+=1\)**.

In the surviving rank-two branch write \(y=1-c_{13}\ne0\).
The exact four-word conclusion is
\[
       c_{13}=c_{14}\ne1,\quad c_{15}\ne c_{14},\quad c_{16}\ne1,
       \quad c_{17}=1,\qquad A_{14,13}A_{15,14}A_{16,15}A_{17,16}\ne0.
\]
Here \(w_{13}\ne0\), and its four positive reads obey all the
factorial ratios fixed by \(y\) and its top read.
There must also be a late vector with nonzero coordinate 12.
If all \(\mathcal K=H_6^{\rm late}\) were zero there,
any top-visible vector in \(\mathcal K\) would see the same
tied first two clocks, and the two-coordinate clock quotient
would force its penultimate to be \(4/y\) times its top.
The four-word formulas would then make all four positive
taps proportional to the top row on the entire top-visible
set, hence on \(\mathcal K\) by linear translation. This
would contradict rank two. The two actual pivots 12 and 13
therefore give full \(E_6\) rank thirteen on the literal first
thirteen (adjoining the optional \(e_{17}\) does not affect
these projections). The live four-edge path from row 13 also
forces \(\operatorname{last}(bA^a)=17-a\) for \(0\le a\le4\).
In particular the rank-two case is not a generic large
alias subspace with arbitrary late clocks.

### Anchored alias shape at the maximal allowed dimension

Every \(\mathcal A_6^{\rm pre}\) polynomial has a factor \(X\),
by the actual origin coordinate. On the six-dimensional
space \(X K[X]_{\le5}\) the four positive moments have
rank four by the nonsingular \(X(1-X)\) Gram through
degree three. Thus \(\dim \mathcal A_6^{\rm pre}\le 2+r_+\)
and the actual pure dimension through grade six on the
prefix is \(4+\dim \mathcal A_6^{\rm pre}\le 6+r_+\).
If the alias dimension attains \(2+r_+\), it must contain
the **entire fixed two-dimensional moment kernel**. One
may use the two explicit generators \(X R_4,X R_5\), where
\[
 R_4=42X^4-84X^3+56X^2-14X+1,\qquad
 R_5=132X^5-330X^4+300X^3-120X^2+20X-1 .
\]
Their \(X(1-X)\)-weighted moments against degrees zero
through three are exactly zero, and their degrees are
distinct with paid leading coefficients. This means, for
example, that *any* prefix with five grade-six aliases is
excluded independently of its individual moment values;
with four aliases, an endpoint rank-two extension and
these two specific aliases are both mandatory.

## A paid certificate excluding the repaired dense family

Use the literal repaired first eight rows of
[the archived dense chart](../erk-single-quadratic-defect/REPAIRED-ELEVEN-ROW-DENSE-SIX.md).
Let \(c=A\mathbf1\) for this eight-row block. A convenient
ordered list of rooted stage columns through degree four is
\[
        1,\ c,\ c^2,\ c^3,\ c^4,\ Ac,\ A^2c,\ c\odot A^2c .
\]
The scalar model list is
\(1,X,X^2,X^3,X^4,X^2/2,X^3/6,X^4/6\).

The three witnesses of grade five are \(A^5\mathbf1\),
\(A^3(c^2)\), and \(c^5\).
Subtract, respectively, the lower combinations with
coefficients
\[
\begin{split}
 & (0,-5/192,725/4608,-47/192,37/288,-23/768,-1/3,1/3),\\
 & (0,-1/48,305/2304,-23/96,25/144,-11/384,-5/48,-1/48),\\
 & (0,-1/24,5/12,-35/24,25/12,0,0,0).
\end{split}
\]
Each difference is numerically zero on the first eight
by exact rational multiplication. Their nonzero models are
\[
\begin{split}
 P_1&=X^5/120-53X^4/288+173X^3/576-41X^2/288+5X/192,\\
 P_2&=X^5/60-49X^4/288+37X^3/144-17X^2/144+X/48,\\
 P_3&=X^5-25X^4/12+35X^3/24-5X^2/12+X/24 .
\end{split}
\]
Now append any three rows, each fed only from the first
eight (no link among rows 9–11 themselves). Every unary
lift of these differences is still numerically zero on
all eleven, since every actual incoming row sees only
the zero first-eight data. Their models \(JP_1,JP_2,JP_3\)
are thus actual sixth-degree aliases on the first eleven.

The moment matrix against \(\ell_1,\ell_2,\ell_3\)
is the matrix against \(\ell_2,\ell_3,\ell_4\) on the
unlifted models, by the weighted primitive identity.
Its exact entries are
\[
 \begin{pmatrix}
     11/15120&17/30240&0\\
     1/2304&3/8960&1/10080\\
     2173/7257600&419/1814400&1/8640
 \end{pmatrix},
 \qquad
 \det=-1/(2^{17}3^7 5^4 7^3).
\]
This has rank three over every field paying \(11!\).
Therefore no 17-row order-eleven tableau having a
full first-eleven stage image can have that eight-row
block followed by three uncoupled rows. In characteristic
zero the dense cutoff automatically supplies the needed
full image, so not just the rational example but all
appended choices of that uncoupled family are excluded.
For a general paid ring this same conditional exclusion
passes at any residue in which first-eleven surjectivity
survives (an actual unit minor suffices); no unconditional
ordinary ring-stage improvement is implied.

The Lean-core witness checks all eight-coordinate numerical
cancellations, the model expansions, and the exact
determinant. The generic alias and reverse-rank bridge
above is mathematical, not a new native order-eleven
Lean interface. This uncoupled test alone does not address
internal couplings; the next section treats the calibrated
coupled subclass.

## Excluding calibrated exact receivers even with arbitrary internal coupling

There is a second, disjoint strengthening of the family test.
Keep the same repaired first eight rows, and require that
rows 9, 10 and 11 are actual exact degree-five point receivers
at clocks \(1,u,v\), respectively. Their incoming coefficients
are **not** assumed to avoid earlier receiver rows. This
subclass is still impossible in characteristic zero, and over
paid fields under the indicated numerical certificate guard.
In particular adding arbitrary causal point-evaluation
contrasts to the repaired construction cannot evade the test
if the three exact receiver profiles are preserved.

Take the scaled aliases \(N_1=2880P_1,\ N_2=1440P_2,\
N_3=24P_3\), and put
\[
 H=X(X-1)(3X-1)(4X-1),\qquad K(X)=H(X)/X,\qquad
 F(X)=N_1(X)/X.
\]
Exact identities give \(H=(5N_3+3N_1-8N_2)/10\) and
\(XH=(N_3+H)/2\), so \(N_1,H,XH\) are actual combinations
that are zero on the base eight. They are independent
(\(N_1(1)=24\ne0\)). First-eleven dense separation forces
their three evaluations at \(1,u,v\) to be independent.
Indeed a nonzero combination with all evaluations zero
would be an actual nonzero model alias through grade five.
The determinant is \(24H(u)H(v)(v-u)\); hence all factors
of this expression are nonzero in the field.

Choose base-null polynomials with only one active receiver:
\[
\begin{aligned}
 p_{10}(X)&=H(X)(X-v), &
 p_{11}(X)&=H(X)(X-u),\\
 p_9(X)&=(u-v)K(u)K(v)N_1(X)+H(X)(c_X X+c_0),\\
 c_X&=-K(v)F(u)+K(u)F(v),&
 c_0&=vK(v)F(u)-uK(u)F(v).
\end{aligned}
\]
Their values at the two undesired receivers are zero;
their own receiver values are nonzero by the determinant
guards. The clock lifts
\[
        B=(X-1)p_9,\qquad G=(X-u)p_{10}=H(X)(X-u)(X-v)
\]
are actual grade-six aliases on the first eleven.
The unary lift \(Jp_{11}\) is another: its only early
input was at the last of the eleven rows. Finally the
unary lift \(Jp_{10}\) has only a possible row-11
entry on the first eleven, so
\(Jp_{10}-\lambda p_{11}\) is an alias for some
actual \(\lambda\). No value of that feed coefficient
is assumed.

Write \(\Lambda\) for the four positive clock-weight moments
on grades through six, in the equivalent unnormalized form
\(L_m(P)=\int_0^1(1-X)^mP(X)\,dX,\ 1\le m\le4\).
Since the earlier universal moment rank bound is two,
the three columns \(\Lambda(B),\Lambda(G),\Lambda(Jp_{11})\)
have rank at most two. In particular their 3-by-3 minors
on rows \(123\) and \(124\) vanish. Also
\[
 \det\bigl[\Lambda(B),\,\Lambda(G),\,\Lambda(p_{11}),\,
                                      \Lambda(Jp_{10})\bigr]=0.
\]
The last statement follows by subtracting
\(\lambda\Lambda(p_{11})\) from the last column:
there are then three genuine alias columns of rank at
most two. The three determinants are therefore independent
of all internal coupling coefficients.

Scale the four rows by \(420,2520,10080,138600\).
With \(f=-24(u-1)(u-v)(v-1)\), the first two determinants
factor into \(f p_0(u,v), f p_1(u,v)\), and the last
factors into \(f(3v-1)(4v-1)\,q(u,v)\).
All cancelled factors are already paid or nonzero from
the receiver evaluation determinant. The complete
normalized coefficients and exact factor identities are
in the companion core certificate. The last factor is
\(q(u,v)=a(u)v+b(u)\), where
\[
\begin{aligned}
a(u)&=210276u^4-168402u^3+16533u^2+10093u-697,\\
b(u)&=-194688u^4+196476u^3-51804u^2+216u+516 .
\end{aligned}
\]
Both \(p_i\) are at most cubic in \(v\). Write
\(p_i=\sum_{j=0}^3 p_{ij}(u)v^j\).
In the equation \(a(u)^3p_i(u,v)=0\), replace
each \((a(u)v)^j\) by \((-b(u))^j\), since \(q=0\).
This is a denominator-cleared identity; it does not
require \(a(u)\ne0\). The resulting two explicit
univariate polynomials \(R_0,R_1\) have an integral
Bézout combination \(D_{\rm cal}\ne0\) in the scalar
certificate. Thus they cannot both vanish.

The core file *ERK11CalibratedMomentGate.lean* checks
the row moment constants, all three determinant factors,
the exact denominator-cleared replacements, and the
integer field identity. The additional paid positive
characteristic guard is the nonzero image of its exact
integer *denomGuard* \(=D_{\rm cal}\); the remaining
nonconstant guards are exactly the verified evaluation
factors. This excludes the calibrated coupled subclass,
not all possible arbitrary non-calibrated dense charts.
The preceding uncoupled family exclusion did not need
any extra integer guard beyond \(11!\).
