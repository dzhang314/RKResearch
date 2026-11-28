# ERK10: three open pairs cannot close consecutively in the five-row decoder

Let \(F\) be a field with \(10!\ne0\). In the
[five-opening continuation](../erk10-five-opening-nonsplit-kernel/README.md),
suppose the ten physical high rows use seven distinct nonzero forward
clocks, with a unique clock 1 in the first reverse row. Three of the six
other clocks occur twice; three are singletons. In reverse ordinates
\(y=1-x\), suppose the first four rows are \(0,a,b,c\), opening all
three pairs, and the next two rows close any two of those pairs. The
three opening scores and the three pair masses must be nonzero. The
closing-copy scores, endpoint score, and singleton scores are allowed
to be zero. Then the actual order-ten reverse word budget is impossible.
In particular, this excludes all six closure permutations in
\(0,a,b,c,*,*,*,d,e,f\) when the starred rows close the three pairs.
The [zero-score addendum](ZERO-SCORES.md) removes all physical score
restrictions. The [zero-pair-mass addendum](ZERO-PAIR-MASS.md) then
removes all remaining score and pair-total conditions over the rationals
for three consecutive closures. These are architecture-specific
obstructions, not ordinary ERK10 stage floors. No order, positivity,
or algebraic-closure assumption is used in the paid-field proofs.

## Actual profiles and the three-dimensional constraint

Let \(B\) be the strict high block, in forward causality; let \(K=B^T\)
in reverse coordinates, and let \(\boldsymbol w\) be the physical high
scores in those coordinates. Work throughout with **unweighted
transpose acting on score-weighted profiles**, so no division by
physical output scores occurs in the operator. Use
\[
\begin{split}
 \boldsymbol u&=K(\boldsymbol w\odot\boldsymbol y)
                     -\boldsymbol w\odot\boldsymbol y^{\odot2}/2,\\
 \boldsymbol g&=K(\boldsymbol w\odot\boldsymbol y^{\odot2})
                     -\boldsymbol w\odot\boldsymbol y^{\odot3}/3,\\
 \boldsymbol h&=K\boldsymbol u,\\
 \boldsymbol k&=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
                     -\boldsymbol w\odot\boldsymbol y^{\odot4}/4.
\end{split}
\]
The actual reverse grades are \(2,3,3,4\), respectively. Clock marking
and \(K\) each raise a defect's grade by at most one. This follows by
dualizing the forward short word tests and using
\(\int fJg=\int (J_{\rm rev}f)g\), with
\(J_{\rm rev}f(x)=\int_x^1f(t)\,dt\); multiplication by \(y=1-x\)
is the difference of the identity and a forward clock mark.
A positive-grade defect is zero at the first reverse \(y=0\) row by
strict causality. Since grade at most three annihilates the first six
positive forward moments, its column sums over each of the six
interior labels are zero. This is the Vandermonde on six distinct
nonzero forward clocks. Thus every such vector is in the three-
dimensional space \(S\) of opposite pairs: it is supported on the six
paired rows and the entries add to zero in each pair.

Let \(D_4\) be the span of the actual reverse word defects through
grade four. By the
[forward annihilator argument](../erk10-five-opening-two-pair-obstruction/README.md#the-rank-bound-paid-by-actual-forward-errors),
\(\dim D_4\le3\). To recall its two independent bounds: the five
nominal weighted powers through degree four are independent modulo
\(D_4\) by the invertible shifted Hilbert moment matrix on positive
degrees 1 through 5. The first forward high clock and first different
clock give two independent rows of the residual map
\(f\mapsto BEf-EJf\), \(f=X,\ldots,X^4\): if dependent, the nonzero
ratio \(r\ne1\) of the distinct nonzero clocks would make
\(r^2,r^3,r^4\) affine in their integer exponents, contrary to
\(r^2(r-1)^2\ne0\). These residual vectors annihilate **both** the
actual and nominal grade-four observers by the short word tests;
for nominal observers the same conclusion follows by testing
\(BEf-EJf\) against each weighted marked power and integrating by
parts (or writing each such power as an actual pure clock-mark word).
Thus \(5+\dim D_4+2\le10\), also with zero scores.

In what follows a **group mean** at a paired label \(z\) means the
sum of the actual score-weighted entries divided by its total score
\(W_z\); it is not an average of individually divided entries.
For a group mean of \(K(\boldsymbol w\odot f(\boldsymbol y))\),
the effective tap at label \(j\) is the sum of \(K_{i\ell}w_\ell/W_z\)
over targets of label \(z\) and donors of label \(j\). Write \(j_1\)
for the first physical copy of label \(j\).

## Branch 1: every grade-four group sum vanishes

Assume \(D_4\subseteq S\). At the first two closures, group means of
\(\boldsymbol u,\boldsymbol g,\boldsymbol k\) are zero. Thus the
effective taps onto \(a,b,c\) are uniquely prescribed by cubic
interpolation of the primitive moments for \(Y,Y^2,Y^3\).
At target \(x\), with labels \(z,j,k=\{a,b,c\}\), the tap onto
\(j\) is
\[
 R_j(x)=\frac{x^2}{j(j-z)(j-k)}
         \left(\frac{x^2}{4}-\frac{(z+k)x}{3}+\frac{zk}{2}\right).
\]
Indeed the moment source \(Y(Y-z)(Y-k)\) removes the other two
nonzero donors and the origin. A completed pair can already supply
two copies at one label: the formula prescribes the total tap there.

Let the first two closed labels be \(z,j\). Neither available donor
label \(j,k\) has more than its first copy in any row defining those
two group means. Their two-column determinant is
\[
 R_j(z)R_k(j)-R_k(z)R_j(j)
 =\frac{jz^3(z-j)}{24k(j-k)(z-k)}\ne0.
\]
Apply the group vanishing to \(K((\boldsymbol y-z)\odot\boldsymbol u)\)
(actual grade four), which ignores any number of \(z\)-copies.
For each other label only its first copy can contribute, so its
column is multiplied by \((j-z)u_{j_1}/w_{j_1}\) or
\((k-z)u_{k_1}/w_{k_1}\). The determinant forces both of those
first-copy defects zero. The first reverse interior \(a_1\) has
\(u_{a_1}=-w_{a_1}a^2/2\ne0\), hence \(z=a\) and this is the sole
active pair of \(\boldsymbol u\).

Now \(\boldsymbol h=K\boldsymbol u\) vanishes at both \(a\)-copies:
it is zero at the first by causality, and its two entries sum to
zero at the pair. At the opener \(b_1\), \(u_{b_1}=0\) forces
\(K_{b_1a_1}w_{a_1}a=w_{b_1}b^2/2\ne0\). In particular
\(h_{b_1}=K_{b_1a_1}u_{a_1}\ne0\). Apply the same determinant to the
vanishing grade-four group means of \(K\boldsymbol h\). Again the
\(z=a\) donors disappear, and this time both of the other
first-copy entries of \(\boldsymbol h\) must vanish. Contradiction.

## Branch 2: grade-four leakage

Consequently \(D_4\not\subseteq S\), and \(D_4\cap S\) has
dimension at most two. In particular \(\boldsymbol u\) cannot be
active on all three pairs, as its first two clock marks would then
span \(S\).

* If \(\boldsymbol u\) is active on two pairs, it and its clock mark
  span both opposite-coordinate lines. If \(b\) were inactive, the
  argument at \(b_1\) above would give an independent
  \(\boldsymbol h\)-component at \(b\). Therefore the active pairs
  are \(a,b\), and at \(c\) all of \(\boldsymbol u,\boldsymbol g,
  \boldsymbol h\) vanish.
* If only \(a\) is active, \(\boldsymbol h\) vanishes at \(a\) and it
  is nonzero at \(b\) by the same causal formula. Were it nonzero
  at \(c\), \(\boldsymbol h\) and its clock mark would span the
  separate \(b,c\) lines. Thus \(\boldsymbol h\) is supported only
  at \(b\). Now any nonzero \(\boldsymbol g\) at \(c\) would give
  the third direction, so again \(c\) is clean in all three profiles.

In either case there are actual defect vectors of grade at most
three \(\boldsymbol V_a,\boldsymbol V_b\) spanning the separate
\(a,b\) pair lines, normalized so their respective first copies have
values \(w_{a_1},w_{b_1}\). Thus
\[
 D_4\cap S=\operatorname{span}(\boldsymbol V_a,\boldsymbol V_b),
 \qquad \dim D_4=3.
\]
At \(c_1\) the first and second primitive moments are exact, so its
taps \(A=K_{c_1a_1}w_{a_1}/w_{c_1}\), \(D=K_{c_1b_1}w_{b_1}/w_{c_1}\)
satisfy
\[
 Aa+Db=c^2/2,\qquad Aa^2+Db^2=c^3/3.
\]
They are not both zero. Therefore at least one of \(K\boldsymbol V_a,
K\boldsymbol V_b\) is nonzero at \(c_1\), and together with
\(\boldsymbol V_a,\boldsymbol V_b\) spans \(D_4\). Normalize a third
basis vector to have \(c_1\) entry \(w_{c_1}\). Let \(\ell_z\) be
its group mean at a closing label \(z\). Every grade-four defect's
group mean at \(z\) equals its \(c_1\) entry divided by \(w_{c_1}\),
times \(\ell_z\): the other two basis directions have zero group
sums and zero values at \(c_1\).

Use this relation on \(K\boldsymbol V_a,K\boldsymbol V_b,
\boldsymbol k\). If neither \(a\) nor \(b\) has yet closed, the first
two profiles give effective group-mean taps \(A\ell_z,D\ell_z\) onto
the available \(a,b\)-copies. Let \(T\) be the total weighted group-
mean tap at \(c\), allowing either one or two available copies.
No other nonzero predecessor label can occur in the first two
closures. The first two primitive moment equalities are
\[
 c^2\ell_z+2cT=z^2,\qquad c^3\ell_z+3c^2T=z^3.
\]
For \(\boldsymbol k\), its normalized \(c_1\) value is
\(Aa^3+Db^3-c^4/4\). The \(\ell_z\) multiple of this value
at the closing group cancels the \(a,b\) terms there, leaving
\[
                    c^4\ell_z+4c^3T=z^4.
\]
The combination \(c^2\) times the first equation minus \(2c\) times
the second plus the third gives \(z^2(z-c)^2=0\). Thus the first
closure must be \(c\). At the second closure \(a,b\) are still
open and the only added donor label is a second copy of \(c\).
The same relation forces \(z=c\) again, impossible. Both branches
are now excluded.

## Reproduce

From this directory:

    python3 -B audit.py
    # From the repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-three-pair-all-open/sources.sha256

A separate core Lean source is supplied for the fraction-free
interpolation, determinant, two-row kernel and leakage cancellation.
The exact audit in this packet is Python/Sympy; it does not claim a
Lean run. The rank, grouping and chronology adapter is mathematical,
not an end-to-end theorem on a literal Lean tableau.

The [chronology extension](../erk10-five-opening-three-pair-chronology/README.md) permits every continuation once the three pairs open first, and also excludes every ordering when the three opening scores and pair totals are nonzero.
