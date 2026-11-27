# The dependent live-reverse ghost forces original cubic pure rank two

Continue the [late-thirteen dependent ghost chart](ERK10-SINGLE-INVISIBLE-GHOST-DEPENDENT-THIRTEEN.md)
over any characteristic-zero field. There is just one zero output weight
at physical row 2, every quadratic defect is invisible, and the actual
nonzero column \(r=Ae_2\) is supported at one clock \(t=c_3\).
The genuine live-reverse quadratic defect \(u\) is proportional to
\(r|_I\). The dependent late-thirteen proof gives uniform nonzero
\(r\), \(r_{13}\ne0\), \(r_{11}=r_{12}=0\), and
\(s=A^\vee r\) nonzero at physical 11 and 12 with distinct numerical clocks.
Its live rooms are
\[
                  W_2=\langle r,s\rangle,\qquad
                  W_3=\langle r,s,Cs\rangle ,
\]
with \(W_3\) not clock-invariant. All indices are original one-based
physical indices. **This note excludes original \(f_3=3\)**; the
remaining dependent branch has original \(f_3=2\) and the early
contacts at the end of this note. It does not exclude all zero weights.

## 1. Cubic pure rank three pays the full three amplitude moments

If \(f_3=3\), its live projection equals \(W_2\) by rank,
because it contains the actual indicator \(e_2\) of the sole ghost.
So \(s\) extended by zero to physical 2 is genuinely in original \(F_3\):
one can take an old lift and subtract its ghost coordinate times \(e_2\).
Consequently
\[
     b C^j s=0\ (0\le j\le6),\qquad
     b C^j s^2=0\ (0\le j\le3),\qquad b s^3=0.
\]
These are old rooted moments with exact grades \(3,6,9\)
before adding clock powers. In particular they do not
assert rooted order ten of \(A^\vee\).

Call the \(m\) live rows with \(r\ne0\) carriers. They have
one common \(r\)-amplitude \(\rho\ne0\) and one common clock \(t\).
Their ordinary weights sum to zero. The true products
\(r s^j\) for \(j=0,1,2\) pay
\(\sum_{\mathrm{carriers}} b_i s_i^j=0\) (grades \(3,6,9\)).
Thus the displayed first and second \(s\)-moment families
are valid on the noncarriers alone. The endpoints have
\(s=r=0\), as \(W_2\subset F_4|_I\).
The noncarrier \(s\)-active sites include physical 11 and 12
with two distinct clocks, so their distinct label count \(q\)
is at least two. Let \(n\) be their physical count.

If \(m\ge4\), then \(n\le11-m\le7\). The pooled noncarrier
\(bs\) measure must be zero: a nonzero measure annihilating
the seven degree-zero-to-six monomials has at least eight
distinct supporting labels. Each active clock must then
have at least two live occurrences, so \(q\le3\). The four
additional pooled \(bs^2\) moments force that measure to
vanish groupwise too. A two-row active group therefore
has equal nonzero amplitudes and opposing weights, and
has no ordinary pooled weight. For any size-\(\ge3\)
group, it contributes at most one ordinary support label
while consuming at least three physical rows. The effective
ordinary support is therefore at most
\[
                      13-m-2q\le5 .
\]
Indeed the ghost and all carrier ordinary weights are invisible
after pooling; it suffices to include the ordinary clean physical
rows and at most one label from each larger active group.
The ordinary degree-nine quadrature with its endpoint anchors
needs at least six distinct sites, contradiction.

Thus \(m=2\) or 3 (there are at least two carriers because their
nonzero weights cancel). In either case every carrier has \(s=0\).
The three \(s\)-amplitude moments on the carrier group,
with at most three distinct values, require the weight sum to
be zero separately at each value. The value at physical 13
is zero by strictness of \(A^\vee\) and \(r_{14}=0\).
If any other value occurred, both this zero group and that
other group would have at least two rows, impossible for \(m\le3\).
All the cubic moment is therefore also on the noncarriers.

## 2. The pooled-zero and nonzero cases both close

If the pooled noncarrier \(bs\) measure is zero, then
\(q\le\lfloor(11-m)/2\rfloor\le4\), the pooled \(bs^2\) row is
zero by its four moments, and the same ordinary support count
\(13-m-2q\ge6\) forces \(q\le2\). But \(r\) is a clock
eigenvector and \(s\) is now supported altogether on the two
or fewer numerical labels: there is no additional carrier
\(s\)-support. Therefore \(C^2s\in\langle s,Cs\rangle\),
making \(W_3=\langle r,s,Cs\rangle\) clock-invariant.
This is impossible, with no multiplicity or amplitude fork left.

If the pooled noncarrier \(bs\) measure is nonzero,
\(8\le q\le n\le11-m\le9\). We give the precise reuse of the
earlier [eight/nine-clock scalar obstruction](ERK10-THREE-CARRIER-EXCLUSION.md).
The unequally repeated labels and carrier corrections in the
old proof must not be read as a claim of exact reversal here.

* At \(q=8\) every pooled \(\nu_x=(bs)_x\) is
  \(\kappa/D'(x)\ne0\), where \(D\) is the monic active hull.
  The \(bs^2\) moments make the interpolant of
  \(R(x)=(bs^2)_x/\nu_x\) have degree at most three.
  With eight singletons \(s_i=R(c_i)\) at every active site.
  In the \((q,n)=(8,9)\) presentation there is just one
  repeated active pair. Its weighted variance, measured using
  pair weights \(b_i s_i\), is the sole term in
  \(\sum (bs^3)_x-\sum \nu_x R(x)^2=0\).
  All other terms are zero, the second sum is a paid
  leading-coefficient test through degree six, and each
  physical pair \(b_i s_i\) and its pooled \(\nu_x\) is a unit.
  Hence the repeated amplitudes are equal, so \(s_i=R(c_i)\)
  again on every active physical row.
* At \(q=n=9\) every site is a singleton and
  \(\nu_x=P(x)/D'(x)\) with \(\deg P\le1\), \(P(x)\ne0\)
  at every site. Interpolating \(Q(x)=P(x)s_i\) gives
  \(\deg Q\le4\) by the four \(bs^2\) moments.
  If \(P\) is constant, the cubic \(bs^3\) moment kills the
  degree-four option for \(Q/P\) by its highest square
  coefficient. If \(P\) has a root \(\xi\) off the hull,
  the same cubic moment on \(Q^2/P\) leaves a constant
  multiple of \(Q(\xi)^2/ D(\xi)\) by partial fractions at
  that pole. Hence \(Q(\xi)=0\) and \(R=Q/P\) is cubic or less.
  This is the exact same scalar one-pole proof as in the
  cited note, with only the actual \(bs\) moments above needed.

So in all cases one polynomial \(R\ne0\) of degree at most
three describes the actual \(s\)-values on the active sites.
There are at most two physical endpoints and **one** additional
noncarrier dormant site (at \((8,8)\) when \(m=2\)).
If none exists, or its clock is 0 or 1, ordinary scalar
quadrature for \(X(1-X)RQ\), \(\deg Q\le3\), reduces to
the paid \(bs\) moments on active sites (carriers cancel
ordinarily). It yields the nonsingular anchored Gram
contradiction to \(R\ne0\).

If that one dormant site's clock \(\zeta\) is different from
the endpoints, test \(X(1-X)(X-\zeta) RQ\) instead,
still degree at most nine. It gives
\(R(X)(X-\zeta)\propto L_4(X)\), where
\(L_4=42X^4-84X^3+56X^2-14X+1\) is the fixed four-interval
Jacobi polynomial. The **genuine old grade-three mask** is
\[
 T=s-R(c)+R(c_2)e_2+\frac{R(t)}{\rho}\,r .
\]
The added terms remove both the physical ghost and all
carriers at their actual clocks, using \(s=0\) at those
sites. The mask has model \(-R\) and support only at
the two physical endpoints and the one live dormant site.
Thus the actual \(A(CT)\) and \((C-1)T\) have disjoint
support (at the middle dormant site the strict advance
cannot yet see \(CT\)). Their paired total grade is \(5+4=9\),
giving exactly the nonzero cubic Jacobi primitive
contradiction from the cited eight/nine-clock note.
This is entirely an **original** rooted product.

Both measure cases are exhausted. Therefore the forward
pure rank cannot be three.

## 3. Additional old fifth-row guard in the remaining rank-two fork

Now \(F_3=\langle e_2,r\rangle\), and \(F_4\) is spanned by
\(e_2,r,\sigma,C\sigma\), where
\(\sigma=s-(s_3/r_3)r\) is normalized by \(\sigma_3=0\).
Normalize the original \(t=c_3\) to 1. The exact old
quadratic/cubic contact as in the
[fifth row analysis](ERK10-SINGLE-INVISIBLE-GHOST-FIFTH-ROW-EXCLUSION.md)
gives \(r_4=0,\ c_4=p=3/2,\ A_{43}=9/8\).
At row 3 the genuine \(Ar\) vanishes, so it has no pure
\(r\)-coefficient in this normalized basis. Its row-4
value is \((9/8)r_3\ne0\), proving \(\sigma_4=s_4\ne0\).

Let \(q=Ac^3-c^4/4\). The same calibrated expression
\(q+Ar/(8r_3)\) is zero at row 4 and has \(r\)-coefficient
\(\theta^3-\theta/2\) by row 3, with \(\theta=c_2\).
Thus it has form
\[
 \eta e_2+(\theta^3-\theta/2)r+\delta(C-p)\sigma .
\]
At physical 5 write \(y=c_5\) and
\(D=\delta(y-p)\sigma_5\). The preceding fifth-row
quadratic and cubic equations are unchanged. The true
quartic equation has its previous right hand side plus
\(D\). The same exact elimination gives
\[
                      2\theta r_5=y^2(2y-3)^2+16 D .
\]
If \(D=0\), all three possible physical incoming lists are
the already checked literal duplicates. So \(D\ne0\),
\(\sigma_5\ne0\), and \(c_5\ne c_4\).
If \(r_5\ne0\), the one-clock hypothesis gives \(y=1\)
and its already proved uniform amplitude gives
\(2\theta r_5=2\theta r_3=1\). The displayed equation then
forces \(D=0\), impossible. Thus **\(r_5=0\)** and
\(s_5=\sigma_5\ne0\). Also \(c_5\ne0\), since otherwise
the live quadratic/cubic equations with \(r_5=0\) give
a literal duplicate of the origin. Hence the first two
old noncarrier \(s\)-response sites are physical 4 and 5
with distinct nonzero clocks, while the first two reduced
reverse \(s\)-response sites are physical 12 and 11
with the established doubled contact at 10/11.
These are necessary conditions in the remaining fork,
not a complete exclusion of it.

[ERK10SingleGhostDependentRankGate.lean](../lean/RKCert/ReviewedNative/ERK10SingleGhostDependentRankGate.lean)
checks the two-clock stability and residual local algebra.
The barycentric, one-pole and Jacobi scalars are the exact
previously checked tests from the cited carrier note; the
support and grade transport is as audited above.
