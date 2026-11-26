# Local paid Leibniz identities in the cancelled-top one-extra-stage chart

Mathematical source-only proof, not kernel-checked. Let
\(A=\gamma I+B\) be a common-diagonal triangular RK tableau over a
characteristic-zero field, with \(s=p+1\) physical stages and rooted
order at least \(p\). Assume the top **paid** scalar
\(\lambda_{p-1}=b^TB^{p-1}e=0\). The actual full product
\[
                  L=b_s\prod_{i=2}^s B_{i,i-1}
\]
is assumed nonzero in the local arguments; the preceding vanishing
chart theorem supplies it for \(p\ge8\). The actual \(L\) is not
assigned any unpaid tall value.

A joint arithmetic run means consecutive physical clocks of nonzero
step \(\alpha\) together with a constant normalized one-hole weight
at all its strictly interior indices. No condition on other clocks
or other normalized skip weights is assumed. The new conclusions are:

* A true four-hole identity gives a nonzero polynomial of degree at
  most four for the step of any joint run of length at least eight.
  The mean step \((1-2\gamma)/(p-2)\) is already excluded on a
  joint run of length six. On length at least seven the same family
  prescribes an exact consistency check for the actual \(L\) once
  a step is chosen; this is not an identification with an unpaid
  scalar formula.
* A joint run of length ten, or two disjoint joint runs of lengths
  at least eight and six, is impossible. They need not have the
  same step or offset.
* Consequently \(s=p+1\) is impossible in this paid-top-zero chart
  for \(p\ge17\). Together with the earlier common-diagonal bound,
  a prescribed \(\gamma\) with \(\lambda_{p-1}(\gamma)=0\) requires
  at least \(p+2\) physical stages for \(p\ge17\).
  This does not concern the paid-top-nonzero chart or give an
  all-\(\gamma\) \(p+2\) bound.

## 1. Actual extra-hole allocation gives a Leibniz rule

Write \(w_H\) for the weight of the actual path omitting \(H\):
the product of its strict entries times its last output weight.
For each contiguous omitted interval \(I\) let \(f_I=w_I/L\).
A path's weight normalized by \(L\) is the product of the
\(f_I\) over its maximal contiguous omitted intervals.
Indeed each such interval replaces its own consecutive adjacent
edges by its physical skip (or a boundary factor); the replaced
edges are disjoint even if they share a retained endpoint.
The denominators are the nonzero full adjacent product factors.
Individual replacement factors may vanish.
The actual one-hole weights, normalized by \(L\), sum to zero,
by the paid \(\lambda_{p-1}=0\).

For marked occupied gaps with positive target hole counts
\(d_1,\ldots,d_q\), let \(D=\sum d_i\) and use paths with
\(h=D+1\) physical holes. A marked link within an arithmetic
run of step \(\alpha\) and actual gap hole count \(g\)
has receiver-minus-donor clock difference \(\alpha(g+1)\).
Use the marked polynomial
\[
                P_{d,\alpha}(w)=\prod_{j=1}^d(w-j\alpha).
\]
This gives \(\alpha^d d!\binom{g}{d}\), and kills gaps with
\(g<d\). The full path uses \(s-h-1=p-D-1\) strict hops
and \(D\) marks, with its initial leaf; the word therefore
pays precisely \(p\), not \(p+1\).
The quantity \(G=D+q\) below is a reverse algebraic grade
counting both the marks and their number of gaps. It is not the
tree order.

In a single arithmetic run of length at least \(G+2\),
place the \(q\) marked links at consecutive occupied slots
starting at the first index of the run. An occupied index is
at most its slot plus \(h\), so every marked endpoint stays
in the run. The two-run placements in Section 5 give an
equivalent conclusion: any one-step overrun is already killed
by a later safe mark. In both settings every path realizing
the exact target counts plus the one extra hole has all
marked endpoints within its designated runs.

First, on each run, a single mark of degree \(d\) shows
that the normalized weights \(f_I\) of contiguous intervals
of size \(d+1\), with both adjacent retained endpoints
inside the run, depend only on size. This is inductive
in \(d\), from the constant singleton factor \(f_1\) of a
joint run. The calculation follows, also for many marks.
Assume the marked intervals of size \(d_i\) have constant
factor \(f_{d_i}\) on their respective runs. A surviving
configuration has exactly one surplus hole beyond the counts
specified by all marks:

* If the surplus lies in marked gap \(i\), its contribution after
  removing the common factorial and step factor is
  \((d_i+1) f_{d_i+1}\prod_{j\ne i} f_{d_j}\).
* Otherwise each marked gap has exactly its target number \(d_i\)
  and the surplus is an isolated singleton in an unmarked
  gap (possibly leading or trailing). To enumerate its
  physical locations, let \(k_i\) be the marked occupied
  links, in increasing order, and let
  \(u_i=k_i+\sum_{\ell<i}d_\ell\) be the primitive donor with
  no surplus yet inserted. If the unmarked gap is \(\ell\),
  its singleton is at
  \(j=\ell+1+\sum_{k_i<\ell}d_i\).
  As \(\ell\) runs from the initial to final unmarked gap,
  these are all indices except the disjoint forbidden blocks
  \(\{u_i+1,\ldots,u_i+d_i+1\}\). This is exact because the
  successive gap-position formula increases by one except
  for the prescribed marked jump, whose occupied gap index
  is itself excluded.
  Each forbidden block lies strictly inside the corresponding
  run: the configuration placing the extra hole in that
  marked gap has endpoints \(u_i,u_i+d_i+2\) there.
  Hence the sum of the allowed normalized singleton weights
  is \(-\sum_i(d_i+1)f_{1,i}\), by the actual zero one-hole
  total. Here \(f_{1,i}\) is the constant singleton factor of
  the run used by mark \(i\). The shifted or unshifted
  size-\(d_i\) marked interval has the same local factor.
  The singleton's interval is separate from all marked
  intervals, even if it shares a retained endpoint, so
  these factors multiply.

Let \(J\) be formal integration from 0 to the variable, \(X\)
multiplication by that variable, and \(T=J-\gamma I\).
Let \(\ell\) denote formal integration from 0 to 1.
The rooted stage model is \((|t|/\rho(t))x^{|t|-1}\);
it sends \(B,C\) to \(T,X\) by unary lifts and additions
of leaves. On a link, \(\mathrm{ad}_C^j(B)\) gives clock
difference to the \(j\)-th power times the strict entry.
Its model is \(j!J^{j+1}\) for \(j\ge1\), and \(T\)
for \(j=0\), since \([X,J^j]=jJ^{j+1}\).
Write the model of \(P_{d,\alpha}\) as
\(d!T^{d+1}F_{d,\alpha/\gamma}(\gamma/T)\), understood after
clearing the powers. For \(t=\alpha/\gamma,\ w=1+y\):
\[
 F_1=w^2-ty,\qquad
 F_2=w^3-\tfrac32ty w^2+t^2y^2,\qquad
 F_3=w^4-2ty w^3+\tfrac{11}{6}t^2y^2w^2-t^3y^3 .
\]
Since the unmarked hops and these factors commute, the
overall formal power is \(T^{p-1}\). Define
\[
 {\cal A}(H)=\ell(T^{p-1}H(\gamma/T)1),\qquad
 \nu(H)={\cal A}(H)/L,\qquad
 \nu_k=\nu(y^k)=\gamma^k\lambda_{p-1-k}/L .
\]
All indices needed in these identities are paid.
In particular \(\nu_0=0,\ \nu_1\ne0,\ \gamma\ne0\).
The adjacent-coefficient scalar recurrence gives the last
two claims, since consecutive paid zeros would force
\(\lambda_0=0\), and the zero-diagonal tall is nonzero.
Put \(\rho_d=\alpha^d f_d\) within a run.

For a single mark the actual calculation gives
\[
  \nu(F_d)=\alpha^d(d+1)(f_{d+1}-f_1 f_d),
       \qquad
  \rho_{d+1}=\rho_1\rho_d+\frac{\alpha}{d+1}\nu(F_d).
 \tag{1}
\]
The first value is position independent throughout the local
run. To calibrate every eligible \(f_{d+1}\), take the occupied
link at its physical donor, and \(d+1\) holes. Its full window up
to donor \(+d+2\) is inside the run. All other contributions
use only the shorter constant factor \(f_d\) and the signed
singleton sum, so (1) proves the induction.
Across several marks the same allocations give the exact rule
\[
       \nu\left(\prod_i F_{d_i,t_i}\right)
           =\sum_i \nu(F_{d_i,t_i})\prod_{j\ne i}\rho_{d_j,j}.
 \tag{2}
\]
The labels indicate the run and its own step. This is a paid
Leibniz rule, not ordinary multiplicativity. The actual
\(L\) is retained in the normalization on both sides.

## 2. Direct three- and four-hole consequences

Put \(n=p-2\), \(M=\lambda_n\ne0\),
\(\epsilon=(1-2\gamma)/n\), and
\(v=\gamma\lambda_{n-1}/M\), \(Q=\gamma^2\lambda_{n-2}/M\),
\(R=\gamma^3\lambda_{n-3}/M\).
Then \(\epsilon/\gamma=v+2\) and
\[
 K=v^3-2vQ+R
        =C_{n+1}(v+2)/((n-1)(n-2))\ne0
\]
by the earlier exact cubic obstruction at the **paid**
\(\lambda_{n+1}=0\) alpha-one Laguerre root.
For a run with \(\alpha=\epsilon\) one has
\(F_1=1-v y+y^2\), so
\({\cal A}(F_1)=0\) but \({\cal A}(F_1^2)=\gamma M K\ne0\).
The grade-four product \(F_1^2\) in (2), on a length-six
run, would give zero. Thus this local step is forbidden.
In particular \({\cal A}(F_1)\ne0\) on any joint run
of length at least six, since
\({\cal A}(F_1)=\gamma M(2+v-\alpha/\gamma)\).

On a joint run of length at least eight, use \(F_1^3\)
as well. These are true three- and four-hole bands,
respectively (marks 2 and 3). Equations (2) give
\[
 \rho_1=\frac{{\cal A}(F_1^2)}{2{\cal A}(F_1)},\qquad
       4{\cal A}(F_1){\cal A}(F_1^3)
                             -3{\cal A}(F_1^2)^2=0.
 \tag{3}
\]
The left quantity is polynomial in \(\alpha/\gamma\)
of degree at most four. It is not the zero polynomial:
at the test step \(\epsilon\) it is
\(-3(\gamma M K)^2\ne0\). Thus there are at most four
possible local steps for a fixed paid diagonal. The
four-hole product \(F_1F_2\), available already at
length seven, and (1) with \(d=1\), also require
\[
 L\left[{\cal A}(F_1F_2)-\rho_1{\cal A}(F_2)
                             -\rho_1^2{\cal A}(F_1)\right]
                       =\frac{\alpha}{2}{\cal A}(F_1)^2 .
 \tag{4}
\]
This constrains the actual seed \(L\). In particular the
bracket must be nonzero; no paid replacement for \(L\) or
claim of sufficiency is being made.

## 3. A short paid recurrence incompatibility

Write \(\xi=1/\gamma\). The reverse \(\nu\) sequence obeys
\[
 (p-k)\nu_k=(\xi-2(p-1-k))\nu_{k+1}-(p-2-k)\nu_{k+2}.
 \tag{5}
\]
It cannot also obey a fixed monic quadratic recurrence for
\(k=0,\ldots,3\). This is the fixed-recurrence lemma of
the arithmetic-gap proof, with \(\nu_1\ne0\) as the nonzero
anchor instead of \(m_0=1\). The check is as follows.
For a geometric mode \(r^k\), the residual in (5) is
\(r^k A_k(r)\), where
\[
 A_k(r)=p-(\xi-2(p-1))r+(p-2)r^2-k(1+r)^2 .
\]
It is not the zero affine polynomial, since its slope
only vanishes at \(-1\), with \(A_k(-1)=\xi\ne0\).
For two distinct nonzero quadratic roots in an algebraic
closure, the residual is exponential-affine of recurrence
order four. Four consecutive zeros force it identically
zero; the two exponential-affine components are independent
(by applying the squared shift-minus-other-root).
A repeated nonzero root gives a mode \((a+b k)r^k\);
its residual divided by \(r^k\) is
\((a+b k)A_k(r)+b r\,\partial_r A_k(r)\).
If \(r\ne-1\), the quadratic, then linear coefficient
force \(b=a=0\); if \(r=-1\), use
\(A_k(-1)=\xi,\ \partial_r A_k(-1)=2-\xi\) to get the same.
If a quadratic root is zero, from \(k=1\) onward there is
at most one geometric mode; rows 1 and 2 kill it, or row
1 directly gives \(\nu_1=0\) if only zero roots remain.
Thus all cases contradict \(\nu_1\ne0\).
These arguments need only \(\nu_0,\ldots,\nu_5\).

In particular, a rectangular Hankel
\((\nu_{i+j})_{0\le i\le3,\,0\le j\le2}\)
cannot have rank at most two. Its leading \(2\)-by-\(2\)
block has determinant \(-\nu_1^2\ne0\), so such a rank
would make its \(y^2\) column a combination of \(1,y\)
and give the forbidden monic recurrence directly.

## 4. Single length-ten run; all slopes

A length-ten joint run places all products of reverse
grade at most eight in \(F_1,F_2,F_3\).
To apply (2) to linear combinations, evaluate the abstract
generators by \(\chi(F_d)=\rho_d\) on a free polynomial
algebra. Within the grade budget (2) reads
\[
       \nu(PQ)=\nu(P)\chi(Q)+\chi(P)\nu(Q)
\]
for abstract lifts, with \(\nu\) evaluated on the actual
polynomials in \(y\). No globally well-defined character
on polynomial relations is assumed without a check.

For \(t=\alpha/\gamma\ne1,2\), the earlier explicit
odd-part determinant
\(\tfrac43 k^3(k-1)(2k-1)^2\), \(k=t/2\ne0\), shows
that \(1,F_1,F_2,F_3,F_1^2\) span polynomials through
degree four at grade at most four.
Choose any linear lifts for a basis of these polynomials.
The product rule through grade eight then gives rank at
most two to their bilinear form \(\nu(PQ)\), hence to the
smaller rectangular Hankel. No choice of lifts affects the
actual entries \(\nu(PQ)\); the rank argument needs only a
linear lift, not that its \(\chi\) respect further relations.
This contradicts Section 3.

For the exceptional slopes, \(\nu_2\ne0\) and
\(\nu_1+\nu_2\ne0\). In fact \(\nu_0=0\) in (5) gives
\(\nu_2/\nu_1=(\xi-2(p-1))/(p-2)\).
Either indicated zero would make \(\xi\) rational,
contrary to the alpha-one Laguerre degree \(p-1>1\)
at the paid zero \(\lambda_{p-1}\).

If \(t=2\), write \(z=y^2,w=y^3\), of grades two and three
via \(F_1=1+z,\ F_2=1+z-2w\). Set
\(a=\chi(z), b=\chi(w), A=\nu(z), B=\nu(w)\).
Apply (2) to \(w^2-z^3=0\) (grade six) and to its product
with \(z\) (grade eight). Since \(A=\nu_2\ne0\),
these yield \(2bB=3a^2A\) and \(b^2=a^3\).
If \(a=0\), then \(b=0\) and
\(\nu_4=\nu(z^2)=0,\ \nu_5=\nu(zw)=0\);
(5) backwards gives \(\nu_2=0\), impossible.
Otherwise \(r=b/a\ne0,\ a=r^2,\ b=r^3\).
For \(d=A/(2r)\ne0\) the relation gives \(B=3r^2d\),
and the product rule on \(z,w,z^2,zw,z^3\) gives
\(\nu_j=d j r^{j-1}\) for \(2\le j\le6\).
This is a nonzero single derivative mode. Rows \(k=2,3,4\)
of (5) make its residual polynomial of degree at most
two vanish, impossible by the repeated-root calculation
of Section 3.

If \(t=1\), write \(z=y+y^2,\ w=yz\), from
\(F_1=1+z,\ F_2=1+\tfrac32z-\tfrac12w\).
Use the same \(a,b,A,B\), now \(A=\nu_1+\nu_2\ne0\).
Apply (2) to \(w^2+zw-z^3=0\) and its product with \(z\)
to get
\[
  (2b+a)B+(b-3a^2)A=0,\qquad b^2+ab=a^3 .
\]
If \(a=0\), also \(b=0\). Consequently
\(\nu(zy)=B,\ \nu(zy^2)=-B,\ \nu(zy^3)=B\),
by \(y^2=z-y\) and the product rule.
These force \(\nu_j\) for \(2\le j\le5\) to be affine
in \(j\) times \((-1)^j\). Rows 2 and 3 of (5) make
its linear residual vanish, and the repeated-\(-1\)
calculation forces \(\nu_2=0\), impossible.
Otherwise \(r=b/a\) satisfies \(a=r(r+1)\ne0\) and
\(r\ne0,-1\). The derivative relation reduces to
\((2r+1)B=r(3r+2)A\).
If \(2r+1=0\), its right coefficient is nonzero,
contradicting \(A\ne0\).
Otherwise set \(d=A/(2r+1)\ne0\). On the algebra
generated by \(z,w\) in the paid grade, \(\chi\) takes
their values at \(r\) and \(\nu\) acts as \(d\) times
derivative at \(r\). This follows by the Leibniz rule
and the displayed generator derivatives.
The polynomials \(z y^k\) for \(0\le k\le4\) are lifts
of grade at most \(k+2\) in \(z,w\): start with \(z,w\)
and use \(zy^{k+2}=z(zy^k)-zy^{k+1}\).
Thus \(\nu_j=d j r^{j-1}+\eta(-1)^j\) for \(1\le j\le6\),
by subtracting the derivative and using the alternating
recurrence on adjacent moments.
Rows \(k=1,\ldots,4\) of (5) say that a degree-at-most-two
polynomial times \(r^k\), plus \(\eta\xi(-1)^k\), has
four consecutive zeros. This residual has fixed order
at most four, with factors \((Z-r)^3(Z+1)\).
The two modes are independent, and the quadratic
coefficient of the \(r\) mode is nonzero because
\(d\ne0\) and \(r\ne-1\). This is impossible.
Both exceptional slopes are thereby excluded.

## 5. Two joint runs of eight and six clocks

Use disjoint subruns \([a,a+7]\) and \([b,b+5]\) of the
indicated lengths. First suppose the longer run is earlier,
so \(b\ge a+8\). If it is later, reflect the physically indexed
retained lists to choose slots, as in the earlier split-run
proof. A reflected clock difference and step both change sign,
so \(P_d\) changes by a harmless factor \((-1)^d\) in that
placement argument. The actual marked operators use original
directed differences and actual steps; no RK tableau is reversed.

The following placements cover every reverse-grade-at-most-eight
monomial in \(F_1,F_2,F_3\) if the steps are the same.
For a fixed tuple with \(q\) marks, \(h=\sum d_i+1\).
Place the earlier marks consecutively starting at \(a\);
if their total target holes is \(D_A\), place the later
marks consecutively starting at occupied slot \(b-D_A\).
After any possible surviving earlier marks, at least \(D_A\)
holes have passed. The later group of \(q_B\) marks then
uses only physical indices from \(b\) through
\(b+h-D_A+q_B\). The ranges below ensure the slots exist.

* A single mark of degree at most three fits in either run,
  with window length \(d+3\le6\).
* For two marks put one on each run. The only possible
  first receiver outside \([a,a+7]\) is \(a+8\) for
  \((d_1,d_2)=(3,3)\), when \(h=7\).
  This means all holes have passed; it is killed by the
  later arithmetic mark. In every case the later window
  has length \(h-D_A+2=d_2+3\le6\).
* For three marks put two on the long run and one on the
  short. Here \(h\le6\), and the only possible overrun is
  the second first-run receiver \(a+8\) at \(h=6\).
  Again all holes have passed and the later mark kills.
  Since \(D_A\ge2\) the later window has length at most
  \(6-2+2=6\).
* Four marks of grade at most eight must all have target
  one. Split two and two; \(h=5,\ D_A=2\).
  The earlier length-eight and later length-six windows
  fit with no overrun.

In the dead overrun cases the bounds still hold for later
slots, since passing all holes includes the required lower
count. Every desired allocation meeting all target counts
must have marked endpoints inside their designated runs:
an overrun would leave the required later positive count
impossible. This also proves the interior placement of the
forbidden singleton blocks used in Section 1, by putting
the extra hole in that marked link. Thus the derivation
formula is valid for these split placements.

If the two steps coincide, local \(F_1^2\) on each run
(length at least six) and \(\nu(F_1)\ne0\) force identical
\(\rho_1\). The calibration (1) then forces identical
\(\rho_d\) through size four, since both runs can calibrate
\(d\le3\). Hence a single set of generator values applies
to any of these placements. All grade-eight arguments
of Section 4 follow without change.

If the steps differ, attach separate generator labels
for the long and short runs. The quadratics \(F_{1,A}\)
and \(F_{1,B}\) have the same leading \(y^2\) coefficients
but different \(y\) coefficients. Along with 1 they span
degree at most two. For a cubic serving the long run,
choose \(G=F_{2,A}\) if its cubic coefficient
\(1-3t_A/2\) is nonzero. Otherwise \(t_A=2/3\) and
choose \(G=F_{3,A}-u F_{1,A}^2\), with \(u\) cancelling
its degree-four coefficient. The coefficient of the
odd cubic in the shifted variable \(y+1-t_A/2\)
is \(4/81\) for \(F_{3,A}\), while \(F_{1,A}^2\) is even
there; hence \(G\) is a genuine cubic.
Thus \(\{1,F_{1,A},F_{1,B},G\}\) spans degree at most three.

All products of this row basis with the column basis
\(\{1,F_{1,A},F_{1,B}\}\) are paid with their own labels.
Within the long run the maximum needed products are
\(F_{3,A}F_{1,A}\) and \(F_{1,A}^3\), which safely
fit length eight alone. Within the short run only
\(F_{1,B}^2\) is needed, fitting length six alone.
Cross products use the split placements above, with
\(F_{3,A}F_{1,B}\) or \(F_{1,A}^2F_{1,B}\) the largest
needed. These put their long labels in the long run and
their short label in the short run as required.
Consequently (2) with distinct formal generator labels
still gives rank at most two to the rectangular moment
pairing between the two chosen polynomial spaces.
Leading \(2\)-by-\(2\) rank is two as before.
This contradicts Section 3. The two-run exclusion holds
without any relation between the steps.

## 6. Uniform stage consequence in the cancelled chart only

For \(s=p+1,\ p\ge17\) in this vanishing paid chart,
the prior topology theorem gives physical cyclicity and the
three-hole residual yields one of two literal clock shapes.
In the no-split shape the joint arithmetic prefix lasts
through \(s-4=p-3\), at least ten.
In the split shape its two nonzero-step arithmetic runs
cover \(s-3=p-2\) physical clocks and their normalized
one-hole singleton factors are constant strictly inside
each run. If either run has length at least ten it is
excluded. Otherwise both lengths are at most nine and
their sum at least fifteen, so one has length at least
eight and the other at least six. Section 5 excludes that
as well. This proves the claimed chart no-go.
The prior general common-diagonal bound \(s\ge p+1\) for
\(p\ge11\) then proves the narrower prescribed-diagonal
bound \(s\ge p+2\) when \(\lambda_{p-1}(\gamma)=0,\ p\ge17\).

Frozen inputs used here: the cyclic cancelled-top run structure
(CYCLIC-CANCELLED-TOP-RESIDUAL.md, SHA-256
af7cfc1ce1bef36e55345c98322593b56f744fd512e33cf08706d2dba318d5fc);
the vanishing-top topology (VANISHING-TOP-PAID-CYCLIC.md, SHA-256
5d4e96b5aa6ede275eec6aa8f6959cc4a4b23967956d40cc8184fd3b19447eeb);
the arithmetic polynomial coefficients and fixed-recurrence
rejection (PAID-ARITHMETIC-GAP-EXCLUSION.md, SHA-256
0ec9a1ff481ec6b8c7946e86d7afe79c3ea9991e88c4aba1315a8ef6285b12ed);
the paid cubic exclusion (COMMON-DIAGONAL-PAID-NONLINEAR.md,
SHA-256 0d7890b60dcf139637a7f9dc148d12b75a854f47f0005c74b6fd1ed1ebaea86b);
and the earlier stage floor (SPLIT-ARITHMETIC-RUNS-FLOOR.md,
SHA-256 f07bbac5c2006f3b3029d6dd653f87410a3a0307e1000cd67ed5109f59f64b0a).

The bound is conditional on the paid top moment vanishing, and the exceptional-slope proof needs the irrationality of the corresponding root of the literal associated Laguerre polynomial, as in the [common-diagonal proof](../../lower-bounds/characteristic-zero/sdirk-common-diagonal-nonlinear-cap.md). It does not claim a bound at other prescribed diagonals.
