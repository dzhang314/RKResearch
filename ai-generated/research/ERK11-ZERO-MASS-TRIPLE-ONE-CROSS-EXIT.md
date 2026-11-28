# Exclusion of the remaining one-cross zero-mass triple

**Scope.** Continue
[the six-group triple cross-pair reduction](ERK11-SIX-GROUP-TRIPLE-CROSS-PAIR.md):
the maximal all-live half-clock ERK11 chart, exactly two carriers, both
first-middle boundaries new, six active noncarrier labels, thirteen
active stages, zero pooled first response, and the unique active
triple having zero ordinary scalar mass. The earlier reduction forces
exactly one cross-front pair and a finite clock atlas. This excludes
that remaining case over any ordered field. The six-active-pair
case, nonzero scalar mass at the triple, nonzero first pools, repeated
boundaries, and ordinary 17-stage impossibility are not asserted.

The [finite Lean certificate](../lean/RKCert/Research/ERK11SixTripleOneCrossGate.lean) uses
only outward rational interval operations. Its exact parameter
root completeness is from the preceding cross-pair packet. No
reverse order eleven and no square of a reverse pure fifth-grade
vector are used.

## 1. One cross-front pair fixes both response profiles

Use the same physical notation as in the preceding reduction.
The six active labels are the five pair clocks, monic hull \(H_5\),
and the omitted zero-mass triple clock \(p\), so \(D_6=(X-p)H_5\).
The pair scalar weights are \(B_x\), and the second response pools
are \(\mu_x=k/D'_6(x)\). Let \(a,d=1-b\) be the plateau clocks,
and \(F,G=\kappa F\) the two physical response scales.

The one-cross chronology ensures every active pair clock occurs
on at least one of the fronts and that the triple has two observed
front responses. The actual calibrated response of the left front
at an active clock \(x\) is
\[
 F_L(x)=\begin{cases}-a^2/2,&x=a,\\ x^2(a-x)/a,&x\ne a.\end{cases}
\]
At \(a\) this reads physical 4, not the other plateau stage.
The right scaled response is similarly
\[
 G_R(x)=\begin{cases}-b^2/2,&x=d,\\ (1-x)^2(x-d)/b,&x\ne d,\end{cases}
\]
where the exceptional read is physical 14.
All these are nonzero for the actually observed responses,
and follow from the true three-, four-, sixth- and seventh-row
calibrations. They do not assert that an unseen pair member has
the same response.

At the unique cross pair \(x_*\), put
\[
                  C_*=-B_{x_*}D_6'(x_*) F_L(x_*)G_R(x_*)\ne0 .
\]
The local pair identity \(-B_xuv=\mu_x\) gives
\(k\kappa=C_*\). For each of the five pair clocks, the sum of
its two physical responses in units \(F\) is \(A_x+B'_x k\),
with
\[
\begin{array}{lll}
 x\ \text{seen on the left}:&
 A_x=F_L(x),&
 B'_x=-1/[B_xD'_6(x) F_L(x)];\\
 x\ \text{seen only on the right}:&
 A_x=-C_*/[B_xD'_6(x)G_R(x)],&
 B'_x=G_R(x)/C_* .
\end{array}
\]
These formulas use the incoming actually known state and the
pair product, not a candidate recombination of state data.

Since the paid cubic moments imply that all pair sums are
values of the cubic-or-lower polynomial \(U_3=\tau/\mu\),
their five values obey the one exact divided difference
\[
         \sum_{\text{pair }x} (A_x+B'_x k)/H'_5(x)=0 .
\]
In every candidate clock chart the coefficient of \(k\)
is checked nonzero. Thus \(k\) and \(U_3\) are determined,
with \(U_3(p)\) obtained by polynomial interpolation.
At the scalar-zero triple its three responses sum to
\(U_3(p)\), by the local cubic-hull identity.
The two observed contributions there are
\[
           F_L(p),\qquad G_R(p)k/C_* ;
\]
the remaining response is their difference from \(U_3(p)\).
This includes the case when the omitted triple is a plateau:
the unknown *second* plateau response is the third number.

For reproducibility the scalar weight formula used by the
calculator is
\[
       B_x=\frac{-1}{13860\,x(x-1)H'_5(x)R_4(x)}
          \quad\text{on a pair clock},\qquad
       b_{17}=\frac{7\lambda+5}{210(\lambda+1)} .
\]
For the first, use
\(R_4(x)\int X(X-1)H_5(X)/(X-x)
 =\int X(X-1)R_4(X)^2/42=-1/13860\)
since \(H_5\) is monic and orthogonal against cubics.
The primitive integrals \(\int_0^1 XR_4=1/30\),
\(\int_0^1 XR_5=1/42\) give the endpoint formula.
No pair mass, Jacobi norm, or endpoint denominator is assumed
zero. These constants are formal polynomial integrals.

## 2. The actual forward scalar fifth direction is determined

Let \(h\) be the coefficient of \(P(a)\) in the actual
left anchored grade-five lift, as in the
[previous pure row argument](ERK11-TWO-CARRIER-OMITTED-PAIR-EXIT.md).
Project off its measured response slopes by subtracting a
quadratic in \(C\) times \(F\). Its result \(h^0\) is still
an **actual forward pure grade-five vector**, and it is
constant on each physical active pair. The analogous scalar
projection on the triple lies in the two-dimensional
space perpendicular to its response line. At the
carrier rows \(h^0\) vanishes (paid product with \(s\)
and strictness at the first carrier), and at physical 1
it vanishes by pure anchoring.

Put \(D_8=X(X-1)D_6\), all its labels distinct in this case.
The pooled scalar row \(b_i h^0_i\) has its six ordinary
moments zero (grades at most ten), and value zero at label
0. Barycentric interpolation therefore gives
\[
                    M_x=\sum_{c_i=x} b_i h^0_i
                              = \frac{U x}{D'_8(x)}
\]
for some scalar \(U\). On a pair clock,
\(h^0_x=U/[B_x(x-1)D'_6(x)]\); at stage 17 it is
\(U/[b_{17}D_6(1)]\).

At the triple, write \(S_p(F)=F^2-U_3(p)F\),
whose ordinary triple read is \(\mu_p\), and write
\(h^0=\alpha+\gamma S_p(F)\) in its local scalar block.
The mean equation gives \(\gamma=U/[k(p-1)]\).
If \(U\ne0\), define the normalized triple
\(h_*=h^0/U=\alpha_*+\gamma_* S_p\) with
\(\gamma_*=1/[k(p-1)]\).
Use the **forward** paid norm of \(h^0\):
if \(\sigma_2\) is the sum of pairwise products of the
three triple responses, then
\(\langle 1,1\rangle_p=0,\ \langle1,S_p\rangle_p=\mu_p\),
\(\langle S_p,S_p\rangle_p=-\sigma_2\mu_p\) as earlier.
The norm therefore fixes
\[
  \alpha_*=
     \frac{\gamma_*^2\sigma_2\mu_p-
             \sum_{\text{outside }p} b_i(h_*)_i^2}
          {2\gamma_*\mu_p}.
\]
The outside terms are the five already constant pair values
and physical 17 (physical 1 and carriers give zero).
This is a grade-ten square of the original \(h^0\);
the use of the local quartic response formula is only
an algebraic expansion of that paid square.

If \(a\ne p\) the left plateau is a complete active pair.
Then \(h^0(a)=-1\) by its literal two-stage calibration,
so \(U=-1/h_*(a)\ne0\).
If \(a=p\), let \(F_4,F_5\) be the first and second
left plateau responses, both nonzero and distinct.
For an anchored lift with \(P(a)\ne0\), its two physical
zero reads at that clock say
\(
(1+h^0_4)/F_4=(1+h^0_5)/F_5
\).
Substituting the local scalar form gives
\(\alpha-\gamma F_4F_5=-1\).
When \(U\ne0\) this determines it from
\(U(\alpha_*-\gamma_*F_4F_5)=-1\).
The required denominator is checked nonzero in every
finite candidate. The case \(U=0\) also has an exact
description: it makes the scalar part zero everywhere
outside the triple, makes \(\gamma=0\), and the same
literal plateau identity fixes \(\alpha=-1\).
The certificate checks **both** choices, without assuming
that the pooled extra mode is nonzero in this last case.

## 3. The literal seventh-row inconsistency

In physical clock variables write
\[
 V_a(X)=X^2(X-a)^2,\qquad
 P_a(X)=J V_a(X)=X^3(6X^2-15aX+10a^2)/30.
\]
The actual grade-four vector with model \(V_a\) used in
the two-front proof is zero through physical 7 in the
new boundary branch. Its literal primitive is therefore
zero at 7 (also at 8), and equals the left anchored
grade-five lift of \(P_a\).
Using \(h^0\) in place of \(h\) merely changes the quadratic
response fit. On a noncarrier this reads
\[
                  P_a(c_i)+F_i T(c_i)+ h^0_i P_a(a) .
\]
The quadratic \(T\) is fixed by the physical zero rows
3,4,6, at the three distinct known active labels
\(a/2,a,z\), as the interpolation of
\(-[P_a(c_i)+h^0_i P_a(a)]/F_i\).
All three are actual nonzero response states.
At physical 7 the label is the other off-plateau front
label \(x\), and its actual \(F_i=F_L(x)\).
The displayed expression must be zero. This uses actual
strictness on \(AV_a\), not a fifth-order condition fitted
at an arbitrary new node.

The certificate checks this value for every one-cross
occurrence assignment. It re-encloses the 42 clock charts
of the preceding proof using tighter rational boxes. For
the one-sided and mixed omitted-label cases it also builds
the reflected **clock charts**, and still uses the literal
forward norm and left row-seven test at each of them.
The both-half family already includes its reflections.
Each front chooses two distinct labels in addition to its
plateau and half-plateau, with occurrence limits two per
pair and three at the triple, and exactly one cross pair.
Both orders of the two remaining left front labels are
tested, because physical 6 and 7 cannot be interchanged
in the primitive argument. The right two orders do not
enter any input value here: both are read by the same
right off-plateau response formula. Nor is an inner
permutation needed to test row 7. There are 396 such
unordered-front assignments and 1,044 seventh-row tests,
including both branches when \(a=p\).

The rational parameter boxes have endpoints on a
\(10^{-36}\) grid and the other root boxes on \(10^{-28}\).
The checker verifies the applicable root endpoint signs
and the distinctness of all boxes. Completeness of the
parameter root counts is in the preceding cross-pair
packet. Each arithmetic quantity is bounded using
integer endpoints on a \(10^{-54}\) grid. Multiplication
and division use all four endpoints and round outward;
every divisor is first checked to exclude zero. Each
final interval strictly excludes zero. These are exact
ordered-field signs, not numerical samples or approximate
solutions. Over a real closure of the coefficient field
they contradict the paid physical seventh-row equality
in every possible remaining chart.

The integer-only [independent replay](erk11-zero-mass-triple-one-cross/replay.py) reads the same literal boxes from Lean and reproduces all 396 assignments and 1,044 separated signs. The numeric receipts check under Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The physical and ordered-field arguments are the mathematical proof above.
