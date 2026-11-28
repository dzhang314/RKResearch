# Eight high labels, one triple: a rational order-ten exclusion

**Theorem.** Use the
[literal five-opening reverse word budget](../erk10-five-opening-nonsplit-kernel/README.md)
at order ten. The ten physical high rows have eight distinct nonzero
forward clock labels and unique forward clock 1 at the first reverse
row. Among the seven nonzero reverse ordinates one label \(a\)
occurs three times and the other six are singletons. Then there is
no method over \(\mathbb Q\) in this chart. All chronological orders,
physical output scores and pooled scores are allowed. The proof
does not assume any score or score sum is a unit.

Over an arbitrary field with \(10!\ne0\), the structural proof
forces the beginning \(0,a,b,a,a\), \(a=2b\), and exact scalar
terminal pressure equations. The rational elimination of those
equations does not exclude every such field. This is not an
unrestricted fifteen-stage ERK10 lower bound.

## Word grades, actual low profiles, and early contrast

Use raw reverse \(K=B^T\), weighted by acting on the actual
score vector \(\boldsymbol w\) rather than by inverting it.
Let \(\boldsymbol y=\boldsymbol1-\boldsymbol x\).
The grade \(2,3,3,4\) primitive defects are
\[
\begin{aligned}
 \boldsymbol u&=K(\boldsymbol w\odot\boldsymbol y)
                       -\boldsymbol w\odot\boldsymbol y^{\odot2}/2,\\
 \boldsymbol g&=K(\boldsymbol w\odot\boldsymbol y^{\odot2})
                       -\boldsymbol w\odot\boldsymbol y^{\odot3}/3,\\
 \boldsymbol h&=K\boldsymbol u,\qquad
 \boldsymbol k=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
                       -\boldsymbol w\odot\boldsymbol y^{\odot4}/4 .
\end{aligned}
\]
A clock mark or \(K\) raises the grade by at most one;
grade \(m\le5\) annihilates forward powers \(X,\ldots,X^{9-m}\).
Strict causality and the first reverse endpoint \(y=0\) make
every positive-grade defect vanish at that endpoint.

In particular grade two has zero group sums at all seven
interior labels, by the seven-positive-moment Vandermonde.
Let \(S\) be this two-dimensional group-sum kernel, consisting
of entries supported at the triple and summing to zero there.
For grade three the **aggregate** space is at most a line:
on the seven interior labels its first six positive forward
moments vanish. Any nonzero line element is nonzero at all
seven labels, by the same Vandermonde with one column removed.
It and its first clock mark have independent aggregates.

As in the
[paid forward-annihilator argument](../erk10-five-opening-three-pair-all-open/README.md#actual-profiles-and-the-three-dimensional-constraint),
\(\dim D_4\le3\): the five nominal powers are independent
modulo \(D_4\) by shifted Hilbert \(5\), and the first forward
row and first different forward row give two independent
forward residuals annihilating all grade-four observers.
If \(\dim D_4=3\), a nonzero additional annihilator supported
on an early reverse prefix is impossible whenever at least
two distinct labels follow that prefix in reverse. Indeed
the first two different forward residual rows then both lie
outside that support, so the two residuals remain independent
on the complementary physical coordinates. We use this
**early contrast** principle also for a score-zero coordinate.

The shifted Hilbert support argument guarantees at least five
distinct nonzero pooled high scores. At most two can be the
endpoint and triple, so at least three singleton scores are live.

## No grade-three leakage

If \(D_3\subseteq S\), then \(\boldsymbol u,\boldsymbol g,
\boldsymbol h\) are all supported at the triple and vanish
at every singleton, regardless of its score. The single-label
nilpotent and feedback argument in the
[fourfold chart](../erk10-five-opening-fourfold-interior/README.md)
does not use multiplicity four. Before the first live singleton
only \(a\) is a live scalar donor label; its first two paid
primitives force \(t=3a/2\), and its composed payment forces
two independent old restrictions on the actual \(a\) submatrix.
The grade-four \((K\boldsymbol g)_t\ne0\) then bounds
\(\dim D_3=2\), the invariant nilpotent span yields
\(\boldsymbol h=a\boldsymbol u-3\boldsymbol g/2\) and
\(\boldsymbol k+3K\boldsymbol g/4=3a\boldsymbol g/4\).
Its feedback coefficient kills every intervening read of the
first live singleton from a later \(a\)-copy, and the corrected
third primitive square excludes the second live singleton.
All endpoint, score, and source assumptions of that local
argument hold here.

## Leakage identities and the first live physical row

Assume there is a nonzero grade-three aggregate. Then
\(\boldsymbol u\ne0\): the very first live interior physical
row has \(u_i=-w_i y_i^2/2\ne0\), and so is at \(a\);
all prior interior scores and all prior \(\boldsymbol u\)
entries are zero. By the aggregate line and its mark,
\(\dim D_4=3\) and \(D_4\cap S=\langle\boldsymbol u\rangle\).

In fact \(\boldsymbol h\) itself must leak. Otherwise
\(\boldsymbol h\) is a multiple of \(\boldsymbol u\),
hence zero from its zero entry at that first live row.
Before the first live singleton let \(N\) be the strict
submatrix on the earlier \(a\)-copies and let
\(\boldsymbol w_*\) be their scores. All positive-degree
scalar donors there are at \(a\), so
\[
 \boldsymbol u_*=aN\boldsymbol w_*-a^2\boldsymbol w_*/2,\qquad
 0=\boldsymbol h_*=a(N-aI/2)N\boldsymbol w_*.
\]
Here \(N-aI/2\) is invertible by nilpotence. Consequently
\(\boldsymbol u_*=-a^2\boldsymbol w_*/2\).
The first live singleton needs a nonzero weighted tap at \(a\)
by its first primitive, which makes its \(K\boldsymbol u\)
nonzero. Contradiction.

The aggregate of \(\boldsymbol h\) is therefore nonzero at
each singleton and at the triple. In particular the first
physical interior row cannot be a singleton: it would have
\(h_i=0\) with only the endpoint available. It is the first
\(a\)-copy, and it is live, since otherwise \(w_i,u_i,h_i=0\)
there makes it a blind grade-four coordinate. The early contrast
principle applies, with many later distinct labels.
The actual grade-four space is spanned by
\(\boldsymbol u,\boldsymbol h,\boldsymbol y\odot\boldsymbol h\).
Using its values at the first \(a\)-copy fixes
\[
 \boldsymbol g=(2a/3)\boldsymbol u+\beta\boldsymbol h,\qquad
 \boldsymbol k=(a^2/2)\boldsymbol u+\phi(\boldsymbol y)\odot\boldsymbol h,
 \qquad K\boldsymbol h=\psi(\boldsymbol y)\odot\boldsymbol h
\]
with scalar \(\beta\) and linear \(\phi,\psi\).
For example \(g-(2a/3)u-\beta h\) first subtracts the
grade-three aggregate line, then the first-copy multiple
of \(u\). The \(u\)-coefficient of \(Kh\) is zero by the
same first-copy evaluation. These are raw weighted identities,
not a division by physical output weights.

## Scalar two-read comparisons

In the calculations below a *scalar tap* into an earlier label is
the sum of \(K_{ij}w_j\) over its available copies. The input
\(K\boldsymbol h\) is analogously read off the actual earlier
entries. At a new singleton \(z\), \(u_z=0\) and \(h_z\ne0\),
even if its physical score were zero.

Here is a common calculation for validating the following
determinants. Suppose on the available predecessors
\[
 \boldsymbol h=P\boldsymbol w\odot\boldsymbol y+
       Q\boldsymbol w\odot\boldsymbol y^{\odot2}+D\boldsymbol u.
\]
For two nonzero scalar donor labels \(r,s\), use
\(Y^3=(r+s)Y^2-rsY\) there. Define
\(F_{r,s}(z)=-z^2/4+(r+s)z/3-rs/2\).
The true cubic and composed conditions at the new singleton give
\[
 [\phi(z)-(r+s)\beta]h_z=w_z z^2 F_{r,s}(z),\qquad
 [\psi(z)-Q\beta-D]h_z=w_z z^2(P/2+Qz/3).
\]
If a third prior label is present and
\(\boldsymbol u=\eta\,\boldsymbol w\odot
 \boldsymbol y\odot(\boldsymbol y-r)\odot(\boldsymbol y-s)\)
on all predecessors, the first left coefficient instead subtracts
\(\eta^{-1}\), by using \(K\boldsymbol u=h_z\).
The two scalar right coefficients and the two left
coefficients give a two-by-two determinant. A nonzero
determinant forces \(h_z=0\) regardless of \(w_z\).
The exact replay below validates all substitutions and factorizations.

## Leading two \(a\)-copies are impossible

If the next row after the first \(a\) is an \(a_2\), its
scalar tap \(S\) into \(a_1\) must be nonzero. Otherwise
on those first two copies \(\boldsymbol u=-a^2\boldsymbol w/2\),
\(\boldsymbol h=0\), giving a nonzero early contrast.
At \(a_2\) the primitive identities then give
\(\beta=-2/3,\ \phi(a)=-a,\ \psi(a)=0\).
For any \(a\)-copy before a new interior label, the first
two scalars give \(g=a u+a^3w/6\), hence
\(h=-au/2-a^3w/4\). If the third copy appears before
any new label, the three columns \(\boldsymbol w,\boldsymbol u,
\boldsymbol h\) restricted to the triple are dependent.
This gives early contrast since all those rows are early.

Thus the next different label \(b\) follows exactly two \(a\)-copies.
Using only scalar label \(a\),
\(h_b=w_b b^2(2b-3a)/4\ne0\), so \(b\) is live and
\(2b-3a\ne0\). The linear functions are
\[
 \phi(Y)=-a-\frac{(b-a)(Y-a)}{2b-3a},\qquad
 \psi(Y)=-\frac{a(Y-a)}{2b-3a}.
\]
On the earlier \(a,b\) donors the actual \(h\)-input has
\((P,Q,D)=(-ab/2,(2b-a)/4,-a/2)\). The next singleton
two-read determinant up to nonzero sign is
\(a(z-a)(z-b)^2/[4(3a-2b)]\), so the very next row
must be the final \(a_3\), not a new singleton.

At \(a_3\) put \(T\) for its raw weighted tap on \(b\), and
\(A\) for its total scalar \(a\)-tap. The exact identity at
\(a\), \(k+a^2u/2-3ag/2=0\), gives
\(b(b-a)(b-a/2)T=0\). If \(b\ne a/2\), then \(T=0\).
For \(b=a/2\), put \(R=K_{a_3,a_2} S\), using the nonzero
first scalar tap at \(a_2\). Since \(K h\) at \(a\) is zero,
and \(h_{a_2}=-a^2 S/2,\ h_b/w_b=-a^3/8\), it forces
\(R=-aT/4\). Reading \(K\boldsymbol u\) from the two old
copies gives \(h_{a_3}=-a^2 A/2-a^2 T/4\).
The primitive identity \(h=a u-3g/2\), using the already
available donors \(a,b\), instead gives
\(h_{a_3}=-a^2 A/2+a^2 T/8\). Thus again \(T=0\).
The same \(h=-au/2-a^3w/4\) relation now holds throughout
the three early \(a\)-copies. Early contrast rules this out.

## A first singleton \(b\), then one more \(a\)-copy

The first different row now follows a single \(a_1\).
At a new \(b\), \(u_b=0\), so it has scalar tap
\(w_b b^2/(2a)\) from \(a_1\) and
\(h_b=-a w_b b^2/4\ne0\). Hence \(b\) is live,
\[
 \beta=(4b-6a)/(3a),\quad \phi(b)=b^2/a-2a,\quad \psi(b)=0.
\]
If the next row is \(a_2\), let \(S,T\) be its scalar
taps from \(a_1,b\). Its raw \(h=-a^2 S/2\);
the \(g\) equation gives
\(2a(b-a)S+b(3b-2a)T=0\).
If \(S=0\) it forces \(T=0\) except possibly \(b=2a/3\),
where the \(k\) equation gives \(b(b^2-a^2/2)T=0\)
and again \(T=0\). That would make these two early
\(a\)-rows proportional on the observer columns (one
may have score zero), impossible. Therefore \(S\ne0\),
\(3b-2a\ne0\), and
\(T/S=2a(a-b)/[b(3b-2a)]\).
The \(k,Kh\) identities fix
\[
 \phi(a)=(a+b)\beta-\frac{b(a-2b)}{3(3b-2a)},\qquad
 \psi(a)=\frac{b(a-b)}{3b-2a}.
\]
On all earlier donors the actual \(h\)-input has
\((P,Q,D)=(-a^2/2,a(2a-b)/(4b),-a(3b-2a)/(2b))\).
This can be verified at \(a_2\) by its displayed tap
ratio; no group sum at the unclosed triple is imposed.
The new-singleton determinant up to sign is
\(b(z-a)^2(z-b)/[4(2a-3b)]\). Therefore the next row
is the last \(a_3\).

At \(a_3\) with scalar taps \(A,T'\) from \(a,b\),
respectively, the first two nontrivial identities compare
\[
 \frac{a^2}3 A+b(b-2a/3)T'=\beta h_{a_3},\qquad
 \frac{a^3}2 A+b(b^2-a^2/2)T'=\phi(a)h_{a_3}.
\]
Their two-coefficient determinant is
\(a^2 b(b-a)(2b-a)/6\). Unless \(a=2b\), these taps
are fixed multiples of \(h_{a_3}\), in the same ratio
as on \(a_2\). In particular the \(h\)-input relation on
\(a_1,a_2,b\) just above continues to hold at \(a_3\):
at \(a\) it is \(h=D(u+a^2w/2)\), which follows from
the scalar taps at \(a_2\) and their proportionality
to \(h\) at \(a_3\). The resulting three-coordinate
early contrast rules out this branch. Thus the only
candidate here is \(a=2b\), handled below.

## Two distinct singleton labels before \(a_2\)

If the row after \(b\) is another singleton \(c\), its
\(g\) and \(u=0\) payments using \(a_1,b\) give
\[
  h_c=w_c\,a c^2(2c-3b)/(4b)\ne0,\qquad
  \operatorname{tap}_c(b)=w_c c^2(c-b)/b^2 .
\]
Thus \(c\) is live and \(2c-3b\ne0\). Use
\[
 \phi(c)=\frac{c^2 F_{a,b}(c)}{h_c/w_c}+(a+b)\beta,\qquad
 \psi(Y)=-b(Y-b)/(2c-3b).
\]
On the actual \(0,a_1,b,c\) predecessors,
\(\boldsymbol u=\eta\boldsymbol w\odot
\boldsymbol y\odot(\boldsymbol y-b)\odot(\boldsymbol y-c)\),
where \(\eta=-a/[2(a-b)(a-c)]\).
The actual \(h\)-input has
\((P,Q,D)=(-ac/2,a(2c-b)/(4b),-c+a(2c-b)/(2b))\).
The next singleton determinant up to sign is
\(b(z-b)(z-c)^2/[4(3b-2c)]\). Thus a new singleton is
impossible, so this next row must be \(a_2\).

But the three scalar taps \(A,B,C\) into the first
\(a,b,c\) at \(a_2\) satisfy a homogeneous three-by-three
system. Here \(h=-a^2 A/2\); cancel the target's nominal
weight in \(g-2a u/3\), \(k-a^2 u/2\), and compare \(Kh\).
The coefficient rows are
\[
\begin{pmatrix}
 a^2/3+\beta a^2/2 & b(b-2a/3)&c(c-2a/3)\\
 a^3/2+\phi(a)a^2/2 & b(b^2-a^2/2)&c(c^2-a^2/2)\\
 \psi(a)a^2/2 & -ab^2/4 & a c^2(2c-3b)/(4b)
\end{pmatrix}.
\]
Its determinant is
\(-a^2 b^2 c(a-b)(a-c)^2(b-c)/[4(3b-2c)]\ne0\).
All three scalar taps vanish. Thus on the early
\(a_1,a_2\) coordinates \(u=-a^2w/2,\ h=0\), an early
contrast even if the second score is zero. This is impossible.

All early exits used only actual first and second singleton
scores, which were forced live, and raw scalar taps at all
copies of the triple. There was no division by their scores
or by the triple total.

## Terminal arithmetic for \(0,a,b,a,a\), \(a=2b\)

The remaining first five reverse ordinates are \(0,a,b,a,a\),
with \(a=2b\). Let the subsequent singletons in causal order
be \(c,d,e,f,g\); they are all distinct from each other and
from \(0,a,b,1\), by the high-label guard. The identities
above specialize to
\[
 \beta=-4/3,\quad \phi(Y)=-3a/2-Y/2,\quad
 \psi(Y)=b-Y .
\]
At \(c\) the earlier scalar ordinates are only \(0,a,b\);
the true cubic equation gives \(h_c=w_c c^2(c-a)/2\).
Indeed \(\phi(c)-(a+b)\beta=(a-c)/2\) and
\(F_{a,b}(c)=-(c-a)^2/4\).
As \(h_c\ne0\), \(w_c\ne0\).

Set \(\boldsymbol H=\boldsymbol h/2\),
\(M=Y^2(Y-a)^2\), \(G=Y(Y-b)(Y-a)(Y-c)\), and the
actual donor vector
\[
 \boldsymbol Z=(\boldsymbol y-a)\odot\boldsymbol H
                     -\boldsymbol w\odot M(\boldsymbol y)/4 .
\]
On the first six physical rows, both \(\boldsymbol Z\)
and \(\boldsymbol w\odot G(\boldsymbol y)\) vanish:
at every \(a\)-copy both terms of \(\boldsymbol Z\) vanish
regardless of its score or defect; at \(b\) use
\(H_b=-w_b b^3/4\); at \(c\) use the just-paid scalar.
This is an identity on physical donors, not only pooled values.

Grade five includes the raw quartic primitive error and
\(K(\boldsymbol y\odot\boldsymbol H)\). Modulo lower paid
directions their respective useful tests are
\[
 K(\boldsymbol w\odot G)-\boldsymbol w\odot JG,\qquad
 K\boldsymbol Z+\boldsymbol w\odot JM/4 .
\]
For the first, subtract lower primitive errors from the
quartic. For the second, substitute in \(K\boldsymbol Z\):
\(K(\boldsymbol w\odot M)\) is its quartic error plus the
nominal \(JM\) and lower errors, while \(K\boldsymbol H\)
has grade four. Hence both displayed vectors annihilate
all forward powers through \(X^4\) with no constant.

Define \(\nu=(Y-1)(Y-e)(Y-f)(Y-g)\) and
\(U=(Y-1)(Y-f)(Y-g)\).
Testing with \(\nu\) makes the \(K\)-parts zero by
strict causality on the first six donors (row \(d\) can
only read them), and annihilates all remaining physical
rows. Scalar precision nine integrates the nominal terms,
so \(I(\nu JG)=I(\nu JM)=0\). Here \(I\) is integration
from zero to one and \(J\) its variable upper primitive.

For a separate verification that this directly handles
zero tail scores, write
\[
 P_9=(Y-d)\nu G,\qquad
 \mu_z=I(P_9(Y)/(Y-z)).
\]
The entire scalar quadrature in reverse includes the
opening origin at \(Y=1\). Its merged score at a scalar
site is \(W_z=\mu_z/P_9'(z)\) by degree-eight
cardinal exactness and distinctness. The seven-interior
cofactor line states that the aggregate of \(\boldsymbol H\)
is \(-L z/P_9'(z)\) for a common nonzero \(L\):
pairing against \(X=1-Y\) removes the factor \(1-z\)
and leaves the usual interior interpolation cofactor.
Its actual \(b,c\) values give
\[
 L=b^2\mu_b/4,\qquad c(c-a)\mu_c=-b^2\mu_b .
\]
Test the scalar polynomial \(\nu(Y-d)M\) of degree nine.
Only \(b,c\) contribute, giving
\[
 I(\nu(Y-d)M)
 =\frac{b^2\mu_b+c(c-a)\mu_c}{c-b}=0.
\]
Since \(M'/4=Y(Y-b)(Y-a)\), the polynomial identity
\(4JG=(Y-c)M-JM\) and the blind equations give
\(I(\nu(Y-c)M)=0\). As \(c\ne d\), these yield
\(I(\nu M)=0\). Applying scalar quadrature to this last
polynomial with its three possible sites \(b,c,d\) gives
\[
 0=I(\nu M)
   =\frac{d(d-a)\mu_d-c(c-a)\mu_c}{(d-b)(d-c)}.
\]
Indeed the two numerators at \(b,c\) in the partial
fraction sum agree by the early equation, and the three
basic quadratic interpolation cofactors sum to zero.
Combining these equalities with the raw \(d\)-cofactor
gives
\[
 4P_9'(d)Z_d
 =-d(d-a)\bigl[b^2\mu_b+d(d-a)\mu_d\bigr]=0 .
\]
Thus \(Z_d=0\), independent of the score there. In fact
the nonzero \(\boldsymbol H\) cofactor and \(d\ne a\)
now force \(w_d\ne0\), not the other way around.

Finally test \(K\boldsymbol Z+\boldsymbol w\odot JM/4\)
with \(U\). It kills \(f,g\), and all earlier rows
read zero \(\boldsymbol Z\) including \(d\). Therefore
\(I(U JM)=0\), and the \(\nu=(Y-e)U\) test also gives
\(I(Y U JM)=0\). The two nodal \(M\) conditions just
proved and these two moments are exactly the
[already computed rational nonic system](../erk10-fifteen-two-pair-rational-closure/README.md#the-unconditional-collapse-and-rational-exclusion),
now with its small parameter equal to \(b\) and
its large fixed node \(2b=a\). The same verified quartic
pivot is nonzero over \(\mathbb Q\) (no projective
root modulo 19). The same resulting degree-nine
numerator is projectively rootless modulo 11. Hence
there is no rational solution. No condition on the
individual \(e,f,g\) scores entered the scalar
elimination.

## Replay and proof scope

    python3 -B audit.py
    # From the overlay/repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-eight-label-triple/sources.sha256

The replay checks the original three chronology determinants and
two-read factors, the unweighted tap exception and the algebra
transfers. Reuse the separately archived nonic replay for the
rational arithmetic. The physical rank, chronology and repeated
tap reduction are mathematical, not a full native tableau theorem.

The [portable scalar receipts](LEAN.md) pass on all four target Lean releases; the word-rank and physical tableau transfer remain mathematical.
