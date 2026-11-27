# Balanced multiclock reverse defect at the sole invisible ERK10 ghost

Work over an arbitrary characteristic-zero field in the
[single invisible ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md).
The fourteen original stages have one zero output weight at
physical 2. Its indicator \(e=e_2\) is pure of grade two and
\(r=Ae\) is the genuine outgoing column, pure of grade three.
On the thirteen live coordinates let \(u\) be the actual
quadratic defect of the restricted weighted transpose
\(A^\vee\), with reversed chronology. Assume:
* \(r\) is nonzero at at least three different physical clock labels;
* \(u\) is nonzero at at least two different physical clock labels;
* the pooled clock measure with masses \(b_i u_i\) is zero.

Under these gates the only remaining shape has original \(f_4=3\),
exactly four \(u\)-active pairs, and exactly five live \(u\)-dormant
rows. Three pairs have equal nonzero \(u\)-amplitudes and opposite
weights; the exceptional pair has unequal amplitudes, and sits at
the root of the affine clock factor in \(r=L(C)u\).
The fifth physical row is a genuine dormant Simpson stage at a
fixed interior Lobatto node. An exact grade-five contrast splits
**all four pairs** and its four signed masses lie on an explicit
Vandermonde line. This is a necessary chart, not an existence or
nonexistence result for its remaining shape. It does not address
nonzero pooled \(bu\), one-clock \(u\), or multiple ghosts.

## 1. The same dual rooms, without a reverse high-order assertion

Write \(C=\operatorname{diag}(c)\). The exact paid dual rooms
\(W_j=B_I^{-1}(E_{8-j}^{\perp}|_I)\) from the single-ghost ledger
have dimensions \(j=1,2,3\). Here \(B_I=\operatorname{diag}(b_i)_{i\in I}\)
and the perpendicular in this formula is the ordinary row annihilator
of the original numerical space; it is supported entirely on \(I\)
because \(e_2\in E_2\). In particular
\[
 W_1=\langle u\rangle,\qquad
 C W_1\subset W_2,\qquad C W_2\subset W_3,\qquad r_I\in W_2 .
\]
Since \(u,Cu\) are independent, \(W_2=\langle u,Cu\rangle\).
Thus \(r_I=L(C)u\) for a nonzero affine polynomial \(L\).
The assumption on \(r\) gives at least three \(u\)-active labels,
so \(W_3=\langle u,Cu,C^2u\rangle\).
The already earned linear incoming Hermite bound for this
restricted reverse says \(W_3\) is not clock invariant; therefore
at least four such labels occur. This uses only the true reduced
linear primitives recorded in the single-ghost ledger.

Denote the count of \(u\)-active labels by \(q\).
Pooled \(bu=0\) requires at least two active rows at each label.
The true reversed origin is old physical 14, so \(u_{14}=0\).
Hence \(q\le6\). We **do not** assume \(u_1=0\):
if \(q=6\), twelve live rows are \(u\)-active so physical 1 is
active, and \(r_1=0\) forces the root \(L(0)=0\).
In either case the pooled \(bu^2L\) sequence has at most five
possible nonzero labels. Its five tests
\[
                b\,u\,C^k r=0,\qquad 0\le k\le4
\]
are actual: on the live set \(bu\) is in \(E_7^\perp\), and
\(C^k r\in F_{3+k}\). Vandermonde therefore gives
zero pooled \(bu^2\) at every label other than a root of \(L\).

At a nonexceptional label two live active rows are then a uniform
opposing pair: the two power tests \(\sum b_i u_i=0\),
\(\sum b_i u_i^2=0\) make the amplitudes equal and total weight
zero. A group of three or more rows compresses to at most one
ordinary scalar support site. Relative to its physical row count,
each nonexceptional active label therefore saves at least two
ordinary support sites. A root of \(L\) can save only one, but
occurs at most once. Hence ordinary degree-nine scalar support
has size at most \(13-2q+1\). Its lower bound six applies
with just the live endpoint 1. Consequently \(q=4\), an
exceptional active label \(\zeta\) at \(L(\zeta)=0\) must occur,
and the six-site capacity is exact. In particular the root block
has exactly two rows with nonzero ordinary mass, and each of the
other three blocks either has two rows and cancels or has three
rows and nonzero ordinary mass. There is no capacity for a
coincidence between remaining effective ordinary sites.

## 2. The rank-four and nonzero cubic exits

If \(f_4=4\), restriction to the live set removes precisely the
line \(Ke_2\), so \(F_4|_I=W_3\) by paid grade-four duality and
dimension. In particular \(u\) has a real old pure grade-four
lift. The four tests of that lift times \(C^k\) against the dual
row \(bu\), \(0\le k\le3\), are paid inside \(E_7\) and give
zero \(bu^2\) pools at **all four** labels. The exceptional
site would save at least two as well, so at most five ordinary
sites remain. Thus \(f_4=3\).

Then \(F_4=\langle e_2,r,Cr\rangle\) by independence, and the
genuine early forward fourth/fifth calculation of
[the internal ghost contact](ERK10-ZERO-INJECTIVE-INTERNAL-EXCLUSION.md#3-genuine-fifth-contact-and-use-of-the-pure-ghost-direction)
applies to the shape \(s=e_2\). Only its local scalar algebra is
used: grade two has \(e_2\), grade three has \(e_2,r\), grade
four has \(e_2,r,Cr\), and on the first five physical rows the
only carrier is 2. In units \(\theta=c_2=1\), the first active
clock is \(t=c_3\ne0\), \(r_3=t^2/2\).
The true \(Ar\) is proportional to \((C-t)r\).
The fourth noncarrier has nonzero \(r_4\) and \(p=c_4\ne0,t\).
The calibrated quartic \(X^2(X-c_5)(2X-3t)\) then gives
\(6 A_{54}p(p-t)(p-c_5)=0\). In the \(A_{54}=0\)
branch row 5 literally duplicates an earlier row, even with
the invisible row 2. Otherwise \(c_5=p=2t\) and
\[
                         r_5-r_4=3p A_{54}\ne0 .
\]
The doubling \(p=2t\) is invariant under clock normalization.
Both \(t,p\) are nonexceptional \(u\)-active labels, since
\(r_3,r_4\ne0\).

For the three nonexceptional labels define
\[
                   M_x=\sum_{c_i=x}b_i u_i r_i^2.
\]
The exceptional group contributes zero, since \(L=0\) there.
The exact tests \(b u r^2=b u C r^2=0\) use
\(r^2\in F_6\) and \(C r^2\in F_7\) against \(bu\in E_7^\perp\).
Thus the three masses annihilate \(1,X\). Unless all zero,
each is nonzero. Each label then needs three rows: its
two-row alternative is the uniform opposite pair and would
kill this mass. Exact capacity gives three effective triples
plus the exceptional pair and two dormant sites. The ordinary
scalar rule therefore has exactly six distinct sites. Clock 1
is present by the live clean endpoint; clock 0 is either a
dormant site at physical 1 or the exceptional label \(\zeta=0\)
(if \(u_1\ne0\), since \(r_1=0\)). The nonexceptional labels
\(t,p\) are both different from these endpoints and belong to
the four interior roots of
\[
                 L_4(X)=42X^4-84X^3+56X^2-14X+1 .
\]
Indeed this is the unique degree-four orthogonal polynomial
under the anchored \(X(1-X)\) tests on the other four roots.
The exact certificate here is
\[
 (182784X^3-102144X^2+11200X-176)L_4(X)
 +(-11424X^3+17808X^2-7084X+235)L_4(2X)=59.
\]
It forbids simultaneous roots \(t,2t\). Thus all \(M_x\) vanish.

## 3. The surviving marked four-pair shape

Since \(L(x)\ne0\) at the three nonexceptional labels, \(M_x=0\)
adds the third amplitude moment \(\sum_{c_i=x} b_i u_i^3=0\).
With at most three active rows there, the first three power
moments force zero ordinary pooled weight in every amplitude
group. Indeed for each distinct nonzero amplitude one may
isolate its weighted amplitude by a degree-at-most-two
Lagrange polynomial. The exact scalar capacity then forces
**two** rows at each of these three labels, and they are
uniform with opposing weights. The exceptional pair has
nonzero ordinary sum and hence unequal amplitudes. There
are five dormant rows, and their five clocks and the
exceptional clock are the six distinct effective ordinary
sites. The same endpoint argument gives the exact Lobatto rule.

The real contrast \(r_5-r_4\ne0\) at \(c_5=c_4=p\)
now implies \(r_5=0\), since a nonzero second amplitude at \(p\)
would disagree with the uniform pair. Thus \(u_5=0\),
as \(L(p)\ne0\). The old stage 5 is genuinely clean:
the carrier tap \(A_{52}=r_5\) is zero, and the
degree-two and degree-three primitive tests at its old
\(F_4\)-clean profile give the Simpson taps to clocks
\(0,p/2,p\): \(p/6,2p/3,p/6\).
In particular \(p\) is an effective interior Lobatto node.
There is no assertion that \(t\) is effective in this last
case: the active pair at \(t\) cancels ordinary weight.

A further constraint uses the actual pure grade-five vector
\[
                            z=A(C-t)r .
\]
It is zero through physical row 4, by strictness and the
first active clock \(t\). At row 5 it equals
\(A_{54}(p-t)r_4\ne0\). Thus it is independent of
\(e_2,r,Cr,C^2r\), all of which vanish at row 5.
The latter four are already independent because the
three \(r\)-active labels are distinct and the ghost
coordinate separates \(e_2\). Hence these five vectors
are exactly the old \(F_5\).

For a live \(u\)-active pair \(i_x<j_x\) at clock \(x\),
let \(\lambda_x=b_{i_x}u_{i_x}=-b_{j_x}u_{j_x}\ne0\) and
\[
                         Q_x=\lambda_x(z_{i_x}-z_{j_x}) .
\]
Within each of the four pairs the two members agree in the clock and every
old grade-five direction except possibly \(z\): at
nonexceptional labels \(r\) is uniform, and at the
exceptional label \(r=0\). The three exact paid
\(W_3\) tests \(b u C^k z=0\), \(0\le k\le2\),
give \(\sum_x x^k Q_x=0\).
If all \(Q_x=0\), the four disjoint rows
\(\lambda_x(e_{i_x}^{\mathsf T}-e_{j_x}^{\mathsf T})\)
would independently annihilate \(E_5\), impossible
because that annihilator has rank three. Therefore
every \(Q_x\ne0\); writing \(D=\prod_x(X-x)\), there is
one \(a\ne0\) with \(Q_x=a/D'(x)\). In particular every
pair is split at true grade five, including the exceptional
pair, and none can finish before physical row 6 (row 5
is dormant). This is an exact constraint, not a lower
bound certified by the remaining chart.

The [Lean receipt](../lean/RKCert/ReviewedNative/ERK10InvisibleReversePooledGate.lean)
checks the two- and three-amplitude identities, elimination
from the three- and four-label moment systems, the exact Lobatto
doubling identity and the finite physical counts. The graded projection, rooted
moments and chronological application are the mathematical
arguments above.
