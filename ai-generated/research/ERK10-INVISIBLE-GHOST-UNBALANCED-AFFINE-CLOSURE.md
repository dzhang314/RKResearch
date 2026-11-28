# The unbalanced affine outgoing/reverse relation at a sole invisible ghost

Work over a characteristic-zero field in the
[single invisible ghost analysis](ERK10-SINGLE-INVISIBLE-GHOST.md).
The fourteen-stage order-ten tableau has one zero output weight,
at physical 2, and \(d=Ac-c^2/2\) is supported there. Write
\(e=e_2\), \(r=Ae\), and \(u\) for the actual quadratic defect
of the reduced weighted transpose on the thirteen live rows.
Assume the original pure rank **\(f_4=4\)** and the following
three gates:
* \(u\) and \(Cu\) are independent on the live set (at least two
  \(u\)-active clock labels);
* in the exact relation \(r_I=L(C)u\), the affine polynomial
  \(L=a+bX\) has \(b\ne0\);
* the pooled signed measure \(bu\) on active clocks is nonzero.

Here \(I\) is the live index set; an active row means \(u_i\ne0\).
(The symbol \(b_i\) is the tableau output coefficient, distinct
from the scalar slope written \(b\) in \(L\).)
Under these hypotheses, the chart is **impossible if all
active labels are singletons**. More generally the nine-label
case is impossible except possibly for one active triple at a
label off the root of \(L\). Thus only that nine-label triple
and a ten-label single physical repeat remain under the stated
rank and affine gates; branches with \(f_4=3\), constant \(L\),
or one-clock \(u\) are not addressed.

## 1. Six genuinely paid square moments and a mixed cubic moment

Use the exact live dual rooms \(W_1,W_2,W_3\) of ranks \(1,2,3\):
after multiplying their columns by the diagonal live weights,
they are respectively the old row annihilators of \(E_7,E_6,E_5\).
These rows have zero ghost component because \(e\) is an
original pure grade-two indicator.
In particular \(W_1=Ku\), \(W_2=\langle u,Cu\rangle\)
and \(r_I\in W_2\). The independence gives the stated unique
affine \(L\). The nonzero pooled \(bu\) row annihilates clock
degrees through seven, so if \(q\) denotes the number of active
labels, \(q\ge9\). It follows that
\(W_3=\langle u,Cu,C^2u\rangle\).

Projection of original \(F_4\) removes precisely \(Ke\) since
this is the only ghost. With \(f_4=4\) the rank-three projection
equals \(W_3\) by paid orthogonality. Thus \(u\) has a true
original pure grade-four lift \(\tilde u\).
In particular \(u\) vanishes at both live physical endpoints
1 and 14, by original point exactness through four.
At most eleven live rows are active.

Let \(\nu_x=\sum_{c_i=x}b_i u_i\),
\(\mu_x=\sum_{c_i=x}b_i u_i^2\),
and \(\tau_x=\sum_{c_i=x}b_i u_i^3\), over live active rows.
The dual row \(bu\) kills \(E_7\). Testing on
\(C^k \tilde u\), \(0\le k\le3\), and on
\(C^k r\), \(0\le k\le4\), pays
\[
       \sum_x x^k\mu_x=0\ (0\le k\le3),\qquad
       \sum_x x^k L(x)\mu_x=0\ (0\le k\le4).
\]
As the linear coefficient of \(L\) is nonzero, the last two
tests add the unweighted fourth and fifth moments. Thus
\(\mu\) annihilates degrees through five. The additional paid
cubic tests are
\[
        \sum_x x^k L(x)^2 \tau_x=0\ (k=0,1),\qquad
        \sum_x L(x)\tau_x=0.                                  \tag{1}
\]
The first two are \(bu\) against \(r^2,Cr^2\) of old grades
six and seven. The **one-factor** test is \(bu\) against
\(r\tilde u\) of old grade \(3+4=7\).
It is needed when a double barycentric pole coincides with
the root of \(L\); the two-factor tests alone miss that case.

Write \(D(X)=\prod_x (X-x)\) for the monic active clock hull.
Interpolation on these distinct labels gives
\[
       \nu_x=\frac{P(x)}{D'(x)},\quad
       \mu_x=\frac{Q(x)}{D'(x)},\quad
       \deg P\le q-9,\quad \deg Q\le q-7.                    \tag{2}
\]
Indeed for prescribed pooled masses the unique numerator
of degree below \(q\) represents the masses this way.
Lagrange interpolation says \(\sum_x x^k/D'(x)=0\)
for \(k<q-1\), and equals 1 for \(k=q-1\).
The triangular moment equations kill successively the leading
coefficients of the numerator, proving those exact bounds.
At a singleton active label \(P(x)\ne0\) and the literal
\(u_i=Q(x)/P(x)\). In a complete singleton chart
\(L(x)^\ell \tau_x=Q(x)^2 L(x)^\ell/[P(x) D'(x)]\).

## 2. A paid scalar and causal lemma when the literal response is cubic

Suppose on **all live active rows** \(r_i=R(c_i)\)
for a nonzero polynomial \(R\) of degree at most three.
At most three live dormant rows are assumed here, including
the two actual endpoints. The original \(r\) is pure of grade
three, so \(br\) annihilates clock degrees through six.
Consequently the actual dormant scalar sites provide exact
\(R\)-weighted quadrature through degree six.

If there are only the two effective clocks 0 and 1, the
anchored \(X(1-X)\)-Gram against a multiplier of degree at most
four contradicts nonzero \(R\). If there is a third distinct
clock \(w\notin\{0,1\}\), test with
\(X(1-X)(X-w) H(X)\) for all \(\deg H\le3\).
It follows that \((X-w)R\) is a nonzero multiple of the fixed
Lobatto quartic
\[
                   L_4(X)=42X^4-84X^3+56X^2-14X+1 .
\]
If its degree were less than four the same Gram would already
give a contradiction. There is exactly one live physical
dormant row at \(w\), since there are at most three dormant rows.
Here the function \(R\) agrees with actual \(r\) even at a root
of \(L\) on an active row (both must be zero there).

Put \(\theta=c_2\) and
\[
                      T=R(c)-r-R(\theta)e .
\]
This is an actual old grade-three vector with model \(R\),
supported only at physical 1, the dormant row at \(w\),
and physical 14. It is zero at the ghost and all active rows.
The strictly causal product
\[
                      (A(CT))\,(1-C)T
\]
is literally zero: \(CT\) vanishes at the origin, and its first
possible support is at the middle dormant row. So \(A(CT)\)
is zero up to and including that row. The right factor is zero
at the terminal and supported no later than the middle.
The total rooted grade is \((3+1+1)+(3+1)=9\).
Consequently
\[
                \int_0^1 J[XR](X)(1-X)R(X)\,dX=0 .          \tag{3}
\]
No reverse order is used in this seam.

On dividing out its nonzero leading scale take
\(R=L_4/(X-w)\). The coefficients of this cubic in increasing
degree are
\[
  42w^3-84w^2+56w-14,\quad 42w^2-84w+56,\quad 42w-84,\quad 42.
\]
The scalar integral matrix at positions \(i,j=0,\ldots,3\)
is \(1/((i+2)(i+j+3)(i+j+4))\). Thus
\(1800\) times the scalar integral in (3) is, modulo
\(L_4(w)\), \(E(w)=105w^2-105w+56\). The exact checked
identity
\[
                 25 L_4(w)+(-10w^2+10w+2)\,E(w)=137
\]
excludes (3). This proves the cubic-response lemma even if
the dormant clock is not a generic abscissa.

## 3. Nine labels, including two repeats or a triple at the root

Here \(P\ne0\) is constant and \(G=Q/P\) has degree at most
two. At singleton active labels \(u_i=G(c_i)\).
If every active site is a singleton, there are four dormant
live rows with endpoints included. The tests of \(bu\)
give genuine \(G\)-weighted dormant quadrature through degree
seven. When the dormant clocks use at most three distinct values,
the anchored \(X(1-X)\)-Gram applied to \(G\) times their
interior factor contradicts \(G\ne0\). With four distinct
values, degree bounds likewise require \(G\) quadratic.
Its product with the two internal clean factors is the
Lobatto quartic up to scale. In the **true reduced reverse**
the quadratic seed \(u\) has grade two and its grade-four
defect is contained in \(W_3+\langle u^2\rangle\), both
supported on the active rows. Thus every dormant row is
indeed reversed point exact through grade four.
At the first nonzero dormant clock of that reverse
chronology, the grade-three mask \((1-C)(G(c_I)-u)\)
reads zero at all earlier rows, hence its reversed primitive
vanishes there. This is exactly the forbidden four-clean
contact of the [fixed Lobatto scalar analysis](ERK10-FOURTEEN-STAGE-EQUALITY.md#unbalanced-dirty-measure-exact-clean-weight-tests).
In applying it use reflected coordinates \(1-X\) and the
orthogonality invariant under reflection; no reflected square
moment at higher order is invoked.

For nine labels with repeats there are at most two repeated
labels, or one triple. On a singleton
\(\tau_x=\nu_xG(x)^2\). By (1), the difference masses
\[
                       L(x)^2(\tau_x-\nu_xG(x)^2)
\]
annihilate \(1,X\): the baseline is a \(\nu\)-weighted
polynomial of degree at most seven. At most two of these
difference masses can be supported, so all vanish.
At each active **pair** off the root of \(L\) the two
nonzero weights \(b_i u_i,b_j u_j\) have nonzero sum
\(\nu_x\), first moment \(\nu_x G(x)\), and second
moment \(\nu_xG(x)^2\) in the amplitude variable. The
two-point variance identity forces both amplitudes equal
to \(G(x)\), without a positivity assumption.
At the root of \(L\) the true \(r\) is necessarily zero
regardless of internal amplitudes or a triple there.
Thus \(R=LG\) describes literal \(r\) on every active row
except possibly in a triple at a nonroot label. When it does,
at most three dormant live rows remain, so §2 excludes it.

## 4. Ten singleton labels

Here \(\deg Q\le3\) and \(P\) is constant or linear.
In all cases \(P\) is nonzero on the active labels themselves.
For constant \(P\), the \(k=1\) test of (1) is a Lagrange
moment of \(XQ^2L^2/P\). It has degree at most nine,
where \(9=q-1\); if \(\deg Q=3\), its leading term is
nonzero and the moment is nonzero. Thus \(\deg Q\le2\)
and the literal response \(r=LQ/P\) is cubic-or-less.

For a genuine linear \(P\), at its single root \(\xi\) the
possible simple residue of \(Q^2L^2/(P D)\) is
\(Q(\xi)^2L(\xi)^2/(P'(\xi)D(\xi))\).
The polynomial part of \(Q^2 L^2/P\) has degree at most
seven, below \(q-1=9\). The \(k=0\) test therefore forces
the simple residue zero, giving \(P\mid QL\).
For clarity the residue rule here is purely formal partial
fractions: summing the residues at the active \(D\)-roots
gives the Lagrange moment; the only other finite residues
are those of the candidate pole term, and there is no
\(X^{-1}\) term at infinity in this degree range.
Thus \(R=LQ/P\) is again a literal cubic-or-less, including
if \(P\) divides \(L\) rather than \(Q\).
There are exactly three live dormant rows and §2 excludes
both cases.

## 5. Eleven labels: linear, simple-pole and repeated-pole exits

All active rows are distinct, all other live rows are the
endpoints, \(\deg Q\le4\), and \(\deg P\le2\).
Recall: any nonzero polynomial of degree at most three
which agrees with \(r\) on the active rows contradicts
§2 using only the endpoint Gram. The same is true of a
nonzero polynomial of that degree which agrees with \(u\),
using \(bu\) and clock degree through seven instead.

If \(P\) is constant, the zero \(k=0\) Lagrange moment of
\(Q^2L^2/P\) kills its coefficient of degree ten; hence
\(\deg Q\le3\) and \(u=Q/P\) is forbidden.
If \(P\) is linear, its lone residue vanishes first
using \(k=0\): the polynomial part has degree at most
nine. Thus \(P\mid QL\). Now \(k=1\) kills the would-be
degree-ten polynomial coefficient, so \(\deg Q\le3\);
\(r=LQ/P\) is forbidden.

Take \(P\) quadratic, allowing passage to a splitting
field simply to write its roots. The polynomial part of
\(Q^2L^2/P\) has degree at most eight, so after multiplying
by \(1\) or \(X\) it contributes no Lagrange moment.
If the two roots are distinct, the two tests force both
residues zero by the two-root Vandermonde. This gives
\(P\mid QL\), hence forbidden cubic \(r=LQ/P\).
For a repeated root \(\xi\), write the candidate rational
part as \(A/(X-\xi)+B/(X-\xi)^2\). The two residues
at \(\xi\), after division by \(D(X)\), are
\[
      R_0=A/D(\xi)-B D'(\xi)/D(\xi)^2,\qquad
      R_1=\xi R_0+B/D(\xi).
\]
Both vanish, so \(A=B=0\) and \(Q(\xi)L(\xi)=0\).
If \(L(\xi)=0\) but \(Q(\xi)\ne0\), the **one-factor**
moment of (1) instead has \(Q^2 L/P\), with polynomial
part of degree at most seven and a genuine simple pole
of nonzero residue at \(\xi\). This contradicts that
moment. In every case \(Q(\xi)=0\).

Finally write \(U=(X-\xi)Q/P\), now a nonzero polynomial
of degree at most three even if \(u=Q/P\) has a simple
pole. On the active sites \(U(c_i)=(c_i-\xi)u_i\).
The actual seven tests of \(bu\) against \((X-\xi)X^k\),
\(0\le k\le6\), give \(U\)-weighted quadrature supported
only on the two endpoints; the anchored \(X(1-X)\)-Gram
again contradicts nonzero \(U\). This last step does not
assume that \(\xi\) itself lies between the endpoints or
has any sign.

[ERK10InvisibleUnbalancedSingletonGate.lean](../lean/RKCert/ReviewedNative/ERK10InvisibleUnbalancedSingletonGate.lean)
checks the affine moment extension, elementary two-point
variance and residue deductions, and the exact cubic
middle-seam certificate. The genuine low-grade lifts, old
rooted payment, and interpolation arguments are the
explicit mathematical derivations above. No unrestricted
stage bound changes.
