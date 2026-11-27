# Signed cubic census on the normalized thirteen-stage DIRK11 face

This is a reduction of the thirteen-stage face, **not its exclusion**.
Let the literal lower triangular tableau have actual rooted order eleven
over \(\mathbb R\), and work in the normalized representative with
\(C(2),D(1),D(2)\). Use the
[archived normalization](../../lower-bounds/proof-dependencies/dirk_multigrade_confluent_cut_rank_and_weighted_reflection_20261123.md)
and [universal ordinary grade-six surplus](../../lower-bounds/characteristic-zero/dirk_universal_grade_six_surplus_from_genuine_closed_bridges_and_origin_jets_20261123.md)
as mathematical inputs. No native proof of those two full source deductions
is asserted here. The theorem applies whenever these normalization
identities and the surplus hold; this note does not itself prove
that every original thirteen-stage candidate admits such a representative.

Write \(g=Ac^2-c^3/3\), \(r=\#\{c_i:b_i g_i\ne0\}\),
\(d=\#\{c_i:g_i\ne0\}\), and \(z=\#\{i:b_i=0,\ g_i\ne0\}\).
Counts \(r,d\) group distinct numerical labels, whereas \(z\) counts
physical rows. The new necessary alternatives are
\[
 r\in\{0,1,2,9\}.
\]
At \(r=9\), nine interior stages are active dirty singletons at distinct
clocks and the other two interior stages are active clean at distinct
clocks. At \(r=2\), exactly two active equal-defect opposite-weight pairs
and two distinct ghost dirties remain; the two pairs must overlap
chronologically, and both ghosts precede either later pair member.

## Native equality inputs

Let \(E_j,F_j\) denote the true rooted column and zero-profile spaces.
The native uniform floor is \(s\ge13\); the true terminal is live,
since an inactive last row could be removed. Normalization gives
a literal zero origin, terminal clock \(1\), and zero terminal column.
Paid coefficient separation and the terminal reverse budget give
\(\dim E_5=9,\dim F_4=2,\dim F_5=3\).
The grade-six surplus gives \(\dim F_6\ge5\); the six
origin-separated clock columns through degree five and two paid
backward dimensions at \(E_6\) force
\[
 \dim F_6=5,\qquad \dim E_6=11.
\]
The two backward dimensions annihilating \(E_6\) are terminal-zero,
so the terminal indicator \(e_T\) belongs to \(E_6\). Pairing with the
grade-three defect gives \(g_T=0\), since \(b_T\ne0\).
Also \(g_0=0\), and \(g\ne0\) by the first nonzero-clock \(C(2)\) read.

Every \(E_6\) vector has a unique scalar profile of degree at most five
modulo \(F_6\). The profile \(H_T\) of \(e_T\) vanishes at 0 and has
paid moments \(\int_0^1 x^k H_T=b_T\) for \(k=0,\ldots,4\).
Consequently
\[
 H_T(x)=30 b_T x\Phi_4(x),\qquad
 \Phi_4(x)=42x^4-84x^3+56x^2-14x+1.
\]
Indeed the four differences of adjacent moments identify the shifted
\(x(1-x)\)-orthogonal quartic and \(\int x\Phi_4=1/30\).
This profile is not a claim that \(b_T=1/30\) when \(F_6\) may be
nonzero at the terminal.

The native forward strict-growth argument, using the true reflected
quadratic and cubic as seeds in the annihilator, gives \(E_6<E_7\).
The genuine reflected cubic
\(G=\beta(1-C)^2 A-\beta(1-C)^3/3\) is nonzero, since the first
two reflected defects vanish and the two-seed forcing cannot have both
quadratic and cubic zero. Equivalently, at the last active non-unit clock
\(u=1-c_i\ne0\), the reflected \(D(2)\) gives \(A_{ii}=u/2\) and
\(G_i=b_i u^3/6\ne0\).
It annihilates \(E_7\). Hence \(\dim E_7=12\). When \(r\ge1\),
the other nonzero row \(\beta g\) also annihilates \(E_7\) by the paid
ordinary product, so \(G\) is a nonzero multiple of \(\beta g\).
For \(r\ge2\), the independent rows \(\beta g,\beta Cg\) give all
of \(\operatorname{Ann}E_6\).

## Low support

The actual defect products have paid moments
\[
 \sum_i b_i g_i c_i^k=0\ (0\le k\le7),\quad
 \sum_i b_i g_i^2 c_i^k=0\ (0\le k\le4),\quad
 \sum_i b_i g_i^3 c_i^k=0\ (0\le k\le1).
\]
If \(r\le8\), the first moments groupwise vanish by Vandermonde, requiring
at least two active physical rows per dirty label. The two true endpoints
are clean, so \(r\le5\), and the second moments then also vanish per label.
Exactly two active members on a label have equal nonzero defects and
opposite ordinary weights.

Remove two active representatives per dirty label and all \(z\) ghosts.
The remaining labels contain 0, 1 and all possible nonzero ordinary
aggregate masses: any label completely removed lost either only ghosts
or one opposite-weight pair in addition to ghosts. There must be at
least seven possible labels. If there were at most six, the polynomial
\(x(1-x)Q(x)^2\), with \(Q\) the monic nodal product of the possible
labels other than 0 and 1, would have degree at most ten, vanish on the
support, and have strictly positive uniform integral. No positivity of
any tableau weight or ordering of clocks is needed for this argument.
Thus \(7+2r+z\le13\).

The two- and three-physical-label cases \(d=2,3\) are impossible whether
or not their weights are zero. The weighted clock span is all of \(F_4\)
if \(d=2\), and all of \(F_5\) if \(d=3\), by the actual ranks and
Vandermonde. It is clock-invariant by interpolation on the physical dirty
labels. Apply the
[native inclusive Hermite gain](../../lean/RKCert/ReviewedNative/DIRKPrefixHermite.lean)
out of grade four or into grade five; either would cost two dimensions
rather than the actual one. This exactly repeats the native mechanism of
the [order-ten physical support theorem](../../lean/RKCert/ReviewedNative/DIRKOrderTenPhysicalDirtySupport.lean)
with the new equality ranks.

Since \(d\le r+z\), \(r=3\) would have \(z=0,d=3\); impossible.
At \(r=2\) we must have \(z=2,d=4\), and all 13 charged slots are used.
There are exactly two cancelling pairs, and seven active clean rows
at distinct clocks containing 0 and 1. Indeed, if a dirty fiber had a
third active member, the three paid moments in \(g,g^2,g^3\)
on that fiber would kill its ordinary aggregate at each nonzero defect
value, leaving at most six possible labels. The third moment is
itself paid for grouping on the two dirty clock labels. If a dirty
fiber had four or more active members, then the other label either has
two and cancels (at most five clean rows and one dirty label remain), or
has at least three (at most four clean rows and two dirty labels remain). In all cases the ghost
dirty labels are distinct and outside the active dirty labels; they
need not be different from clean numerical clocks.

More precisely, in this \(r=2\) case let \(\ell_1,\ell_2\) be the physical
pair contrasts. Then \(\operatorname{Ann}E_6=\operatorname{span}
(\ell_1,\ell_2)\), and \(G\) is a nonzero combination using both
contrasts. The two rows \(\ell_i A\) annihilate \(E_5\) and vanish at
the terminal. At least one lies outside this contrast plane, or the
pair-equality subspace would be invariant under both \(A\) and
pointwise multiplication, and folding the pairs would preserve whole
rooted order with fewer than 13 stages. Every row outside the plane in
this terminal-zero annihilator has nonzero \(g\)-weighted aggregates
at all four dirty labels: the aggregates kill powers \(0,1,2\) by
\(F_5=g\mathcal P_2(c)\); if one vanishes they all do. In that event the
row is a contrast plus a row on the six distinct nonterminal clean
clocks that annihilates powers \(0,\ldots,5\), hence is in the plane.
Thus at least one \(\ell_i A\) is nonzero at both ghosts and has nonzero
mass on both pairs. Because \(GA\) is in the contrast plane and the two
coefficients of \(G\) are nonzero, the same is true of the other
\(\ell_i A\). Causality puts both ghosts before either closing pair
member, and puts the first member of either pair before the closing
member of the other. This is a chronology restriction, not an
exclusion of the surviving overlap.

## High support, including repeated labels

We have \(9\le r\le11\). On the \(r\) active dirty labels \(x\), let
\(V(X)=\prod_x(X-x)\) and write \(w_i=b_i g_i\). Interpolating the first
and second moments in barycentric form gives
\[
 \sum_{i:c_i=x} w_i=\frac{L(x)}{V'(x)},\quad \deg L\le r-9,\qquad
 \sum_{i:c_i=x} w_i g_i=\frac{P(x)}{V'(x)},\quad \deg P\le r-6.
\]
In these sums only active dirty rows contribute. The residue identity
\(\mu(Q)=\sum_x Q(x)/V'(x)\) kills \(\deg Q\le r-2\) and gives
the leading coefficient at degree \(r-1\), by Lagrange interpolation.

We use a simple masked payment repeatedly. If a nonzero polynomial
\(U\) agrees with \(g\) at all active dirty rows, except possibly
same-clock constant-defect pairs of opposite weights, and there are
\(k\) distinct active clean interior labels, let \(Q_0\) be their monic
nodal product. The ordinary weighted clock reads of
\(x(1-x)Q_0(x)(U(c)-g)\) vanish, including at cancelled pairs, both
physical endpoints, and ghosts. When \(\deg U\ge3\), the grade is at
most \(2+k+\deg U\); more generally use \(2+k+\max(3,\deg U)\).
Thus the paid ordinary scalar moments give
\(\int_0^1 x(1-x)Q_0 U x^j=0\) through the remaining grade. In particular
\(U\) of degree at most three is impossible if \(k\le1\), by testing
against \(Q_0 U\). If \(k=0\), the same test excludes \(\deg U\le4\).
Identical reasoning applies to the relation \((C-u)g=U(c)\)
with \(\deg U\le4\) when \(k=0\); that relation has grade at most four.

**Eleven labels.** Every interior stage is a singleton, so \(g=P/L\)
on those labels and \(L\) is nonzero there. The two cubic moments are
\(\mu(X^k P^2/L)=0\) for \(k=0,1\).
If \(L\) is constant, the \(k=0\) moment kills the leading degree-ten
term of \(P^2\), giving \(\deg g\)-profile at most four.
If \(L\) is linear, the polynomial quotient of \(P^2/L\) has degree at
most nine, so the \(k=0\) moment kills the remainder by the simple
pole identity \(\mu(1/(X-u))=-1/V(u)\). Thus \(L\mid P\) and
\(P/L\) has degree at most four.
If \(L\) is quadratic, both moments kill the polynomial quotient of
degree at most eight. They force \(L\mid P^2\) even if \(L\) has a double
root. Explicitly, for the remainder \(R\), the two residue reads are
minus \(1/\operatorname{lc}(L)\) times the linear coefficients of
\(S=(R V^{-1})\bmod L\) and \(XS\bmod L\); polynomial parts at infinity
and the partial fractions of \(R/(LV)\) give this formula. The inverse
exists because \(V,L\) are coprime. These two coefficients vanish only
if \(S=0\), hence \(R=0\). If \(L\) is squarefree it divides \(P\),
giving a cubic profile. At a double root \(u\), \(X-u\mid P\), giving
the degree-at-most-four profile \((C-u)g=P/[\operatorname{lc}(L)(X-u)]\).
All are excluded by the endpoint-only masks.

**Ten labels.** There is at most one extra active row.
If all labels are singleton, the same division with \(\deg P\le4\)
gives \(P/L\) of degree at most three: for constant \(L\) use \(k=1\)
to kill the degree-nine term; for affine nonconstant \(L\), \(k=0\)
kills the pole remainder. The possible extra clean interior row is
covered by the one-interior mask.

Now suppose the extra row is a duplicate active dirty at \(\xi\).
If \(a=\sum_{\xi}w_i\ne0\), the difference between the actual third
moment mass and its model \(a(P/L)(\xi)^2\) is
\[
 E=\frac{w_1w_2}{w_1+w_2}(g_1-g_2)^2.
\]
For constant \(L\), \(k=0\) isolates \(E=0\), and \(k=1\) again
gives a cubic. For linear \(L\) with root \(u\), the quotient terms
vanish at both moments. The remaining equations are \(t+E=ut+\xi E=0\)
with \(t=-P(u)^2/[L' V(u)]\). As \(u\ne\xi\),
\(E=t=0\), giving a uniform pair and cubic \(P/L\).

Finally \(a=0\) implies \(L=\lambda(X-\xi)\) and \(V=(X-\xi)W\).
Use the paid third read for \(X-\xi\), which removes the pair.
At other labels its sum is
\[
 \sum_{x\ne\xi}\frac{P(x)^2}{\lambda(x-\xi) W'(x)}
   =-\frac{P(\xi)^2}{\lambda W(\xi)}.
\]
The quotient degree is at most seven and disappears on the nine
roots of \(W\). Thus \(P(\xi)=0\), so the pair has equal \(g\) by
the second fiber mass, and opposite \(b\). The other nine labels
follow the cubic \(P/L\). The endpoint-only mask still kills it.
This exhausts \(r=10\), including a cancelling aggregate \(\beta g\)
at the repeated dirty clock.

**Nine labels.** At least one singleton makes the constant \(L\) nonzero.
On each label \(U=P/L\) is the weighted mean of \(g\) with weights \(w_i\)
and \(\deg U\le3\). There can be two extra active physical rows.
For two distinct repeated pairs, the cubic variance excess above
\(a_x U(x)^2\) vanishes at each, since its first two clock moments
vanish and the two labels are distinct. One repeated pair alone
likewise agrees with \(U\). If a single fiber has three members
with heterogeneous \(g\), \(g^2\notin g\mathcal P_3(c)\), so
\[
 F_6=g\mathcal P_3(c)+K g^2.
\]
Apply this to \(e_T-H_T(c)\). At the eight singleton dirty labels
\(H_T+UR+\eta U^2\) is zero for some \(\deg R\le3\).
Its degree is at most six, hence it is identically zero.
For every member of the triple at \(\xi\),
\[
 (g_i-U(\xi))\bigl(R(\xi)+\eta(g_i+U(\xi))\bigr)=0.
\]
If \(\eta\ne0\) or \(R(\xi)\ne0\), this gives at most one non-\(U\)
value. Its \(w\)-sum is zero by the definition of the mean \(U\); the
non-\(U\) members therefore form an opposite-weight pair, so the
endpoint mask again gives a contradiction.

It remains to audit \(\eta=0,R(\xi)=0\), where the factored equation
alone gives no information about the individual triple entries.
Here \(F_6\) vanishes at both clean endpoints, so \(H_T=X\Phi_4\)
and has degree five. The polynomial identity \(H_T=-UR\) gives
\(\deg U\ge2\). If \(U\) is cubic, then \(R\) has degree two, so
\(e_T=H_T(c)+gR(c)\in E_5\); this contradicts the reviewed
\(\mathtt{endpoint\_coordinate\_out\_of\_zero\_row}\) at \(q=5\).
Hence \(U\) is quadratic. Its two roots are simple and real since
they are roots of \(H_T\). Neither can be an active singleton clock,
and \(U(\xi)\ne0\) because the root \(\xi\) of \(R\) is simple in
\(H_T\). The nominal dirty masses \(\kappa/[U(x)V'(x)]\) are now
well-defined on all nine labels and equal the actual singleton masses.
For polynomials of degree at most nine, partial fractions of
\(\kappa f/(UV)\) replace the entire nominal dirty rule by masses
on the two roots of \(U\): the rational function has denominator
degree eleven and no residue at infinity. The actual rule differs
from the nominal one only at the triple clock \(\xi\), so its ordinary
degree-nine quadrature is supported on at most five labels including
0 and 1. The same nonnegative nodal-square test contradicts this.
This disposes of the last heterogeneous triple.

In the remaining \(r=9\) case, the mask forces exactly two active clean
interior rows at distinct clocks \(e,f\). Thus all nine dirty labels
are singleton, and
\[
 (X-e)(X-f)U(X)\in\operatorname{span}(J_4,J_5)
\]
for the monic \(x(1-x)\)-orthogonal polynomials. This follows from
the four remaining masked scalar moments. No division by an individual
inactive output weight, or order assertion on the transposed tableau,
enters the census.
