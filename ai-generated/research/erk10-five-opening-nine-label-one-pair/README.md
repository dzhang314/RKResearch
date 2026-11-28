# Nine high labels, one pair: a rational order-ten exclusion

**Theorem.** Use the
[actual five-opening reverse word budget](../erk10-five-opening-nonsplit-kernel/README.md)
at order ten. The ten physical high stages have nine distinct
nonzero forward clocks, with unique clock \(1\) at the first
reverse row. The eight interior labels consist of one pair and
seven singletons. Then no such continuation exists over
\(\mathbb Q\), with arbitrary chronological ordering, physical
scores, and pooled score of the pair. This is a fixed
architecture restriction, not an unrestricted ERK10 lower bound.
No new upper bound is asserted.

The prime-field portions of the proof use only \(10!\ne0\).
The final nonic is the same one already analyzed for the
eight-label rational chart; some paid fields can have its
roots, so the whole exclusion is not asserted over every field.

## Actual reverse observers and the grade-two split

As in the
[eight-label raw proof](../erk10-five-opening-eight-label-triple/README.md),
use \(K=B^T\) and \(\boldsymbol y=\boldsymbol1-\boldsymbol x\);
scores are in \(\boldsymbol w\), not inverted. Write
\[
\begin{aligned}
 \boldsymbol u&=K(\boldsymbol w\odot\boldsymbol y)
                        -\boldsymbol w\odot\boldsymbol y^2/2,&
 \boldsymbol g&=K(\boldsymbol w\odot\boldsymbol y^2)
                        -\boldsymbol w\odot\boldsymbol y^3/3,\\
 \boldsymbol h&=K\boldsymbol u,&
 \boldsymbol k&=K(\boldsymbol w\odot\boldsymbol y^3)
                        -\boldsymbol w\odot\boldsymbol y^4/4 .
\end{aligned}
\]
Here vector powers are componentwise. Their grades are \(2,3,3,4\).
The grade-\(m\) defects annihilate \(X,\ldots,X^{9-m}\);
all positive grades vanish at the first reverse endpoint \(y=0\).
The five weighted nominal powers and two independent forward
residuals give \(\dim D_4\le3\) as before. There are at least
five live high scalar sites by shifted Hilbert \(5\).

There are now **eight** interior sites. Thus a nonzero grade-two
aggregate is the single cofactor line, nonzero at all eight
interior sites: seven positive forward tests give dimension one.
Grade-three aggregates have dimension at most two, the same
cofactor multiplied by a scalar linear polynomial. These facts
follow from the Lagrange divided-difference pairing after factoring
\(X\) from the tests. The opposite-pair kernel \(S\) has dimension
one.

We repeatedly use the early contrast consequence of \(\dim
D_4=3\). If two early equal-clock coordinates are proportional
on each of the nominal and \(D_4\) columns, or a single early
coordinate is zero on them, their difference gives an additional
annihilator. The first two different forward residual coordinates
lie later in reverse than those early rows (there are many later
distinct sites), so the two residuals remain independent with the
contrast added. This contradicts the rank-eight observed subspace.
This does not assume physical stage rows are identical.

## If the grade-two aggregate is zero

Here \(\boldsymbol u\in S\) and it is nonzero, since the
first live interior score has nonzero \(u_i=-w_i y_i^2/2\).
If \(D_3\subseteq S\), then \(\boldsymbol g,\boldsymbol h\)
are proportional to \(\boldsymbol u\) and supported only at
the pair \(a\). The first live singleton must pay its first
primitive with a nonzero scalar tap into earlier \(a\)-copies,
while \(K\boldsymbol u=0\) there. On the old \(a\)-copies
\(g=a u+a^3w/6\), so their scalar scores are proportional to
their \(\boldsymbol u\) coordinates. This is impossible.

If \(D_3\) leaks, its aggregate dimension is **one**, not two:
two independent linear cofactor multipliers and their marks
would already span three aggregate directions in \(D_4\),
besides the pure \(\boldsymbol u\) direction. Consequently
\(D_4\cap S=\langle\boldsymbol u\rangle\).
As in the eight-label proof, \(\boldsymbol h\) must leak:
otherwise proportionality to \(\boldsymbol u\) and its
first-live zero entry give \(\boldsymbol h=0\) everywhere.
The strict old \(a\)-block \(N\) before the first live singleton
would then satisfy \((N-aI/2)N\boldsymbol w_*=0\),
so \(N\boldsymbol w_*=0\) and
\(\boldsymbol u_*=-a^2\boldsymbol w_*/2\),
contradicting that singleton's two composed reads.
Thus \(D_4=\langle\boldsymbol u,\boldsymbol h,
\boldsymbol y\odot\boldsymbol h\rangle\) and
\[
 \boldsymbol g=(2a/3)\boldsymbol u+\beta\boldsymbol h,\quad
 \boldsymbol k=(a^2/2)\boldsymbol u+\phi(\boldsymbol y)\odot\boldsymbol h,
 \quad K\boldsymbol h=\psi(\boldsymbol y)\odot\boldsymbol h ,
\]
once the first interior row is the live opener at \(a\).
That first-row guard follows by early blindness, as in the
[raw two-pair proof](../erk10-five-opening-eight-label-pairs-zero/README.md#grade-three-leakage-no-inverse-scores):
a first nonactive or score-zero interior row would have
\(w,u,h=0\).

The raw early head computations of that proof now apply
without asserting the one-dimensional \(\boldsymbol h\)
aggregate is everywhere nonzero. This matters because its
linear cofactor multiplier can have one root. Each step
instead uses the same raw blind-coordinate alternative:

* A leading active closure fixes \(\beta=-2/3\) unless the
  pair has an early contrast. The first other row \(b\) must
  be live, and \(h_b=0\) at \(b=3a/2\) would contradict its
  literal nonzero cubic error. The two-read determinant then
  forces a repetition at \(b\), unavailable with the sole
  pair already closed.
* If a new \(b\) follows one active opener, it is live or
  blind, and \(h_b=-a w_b b^2/4\ne0\). If the pair then
  closes immediately, the raw tap ratio and next two-read
  determinant again demand a repetition at \(b\).
* Otherwise another distinct \(c\) intervenes: \(w_c=0\)
  would be blind, and \(2c-3b=0\) would give \(h_c=0\)
  with nonzero \((K\boldsymbol h)_c\). The delayed active
  closure after \(0,a,b,c\) is ruled out by the same
  invertible \(3\times3\) raw tap system. Any next
  nonactive row is forced to \(b\) or \(c\), each already
  a singleton.

All these determinant factors are archived in the
[one-triple proof](../erk10-five-opening-eight-label-triple/README.md#scalar-two-read-comparisons).
Thus the grade-two aggregate-exact branch is impossible
over every paid field, regardless of the rational argument.

## Leaking grade two: normalized first three interiors

Suppose the aggregate of \(\boldsymbol u\) is nonzero.
Its first two marks have independent aggregates, so they
give the entire \(D_4\):
\[
 D_4=\langle\boldsymbol u,\boldsymbol y\odot\boldsymbol u,
                 \boldsymbol y^2\odot\boldsymbol u\rangle,\qquad
 D_3=\langle\boldsymbol u,\boldsymbol y\odot\boldsymbol u\rangle .
\]
The second equality uses the two-dimensional grade-three
aggregate bound and injectivity of aggregation on \(D_4\).
A first score-zero interior row would have \(w=u=0\), an
early blind coordinate, so its score and \(u\) are nonzero.

For the remaining formulas scale the first interior ordinate
to \(1\). If its original value is \(a_0\), set
\(Y=y/a_0\), rescale \(K\) by \(1/a_0\) and the grade
\(m\) defects by \(1/a_0^m\), and retain the same notation
for the rescaled operator/defects. Then the first row has
\(Y=1,\ u=-w/2\). The scalar integration functional is
now \(I(F)=H^{-1}\int_0^H F(Y)\,dY\), \(H=1/a_0\);
this is formal polynomial integration, no ordering needed.
The opening origin contributes at \(Y=H\), while the first
reverse endpoint remains \(Y=0\). Paid tests span the same
polynomials of bounded degree vanishing at \(Y=H\).

We have
\[
 K\boldsymbol u=\kappa(\boldsymbol Y-1)\odot\boldsymbol u,\quad
 K(\boldsymbol Y\odot\boldsymbol u)=Q(\boldsymbol Y)\odot\boldsymbol u,\quad
 \boldsymbol g=P(\boldsymbol Y)\odot\boldsymbol u,\quad
 \boldsymbol k=R(\boldsymbol Y)\odot\boldsymbol u
\]
with degrees \(1,2,1,2\), where \(Q(1)=0,\ P(1)=2/3,\
R(1)=1/2\). If the next physical row also has \(Y=1\),
the true \(K\boldsymbol u\) equation kills its tap from the
single previous nonzero \(u\); hence its \((w,u)\) look
proportional to the first row, an early contrast.
So the next physical label \(b\) is distinct. If its \(u=0\),
the same equation kills the only previous nonzero-ordinate
tap, so \(w=0\) there too, early blindness. Thus both first
interior \(u\)-values are nonzero.

If \(\kappa=0\), the second interior row reads no previous
nonzero-ordinate source and \(P(b)=2b/3\), hence
\(P(Y)=2Y/3\). Inductively on causality \(u=-wY^2/2\):
this holds on the first row, and then \(K\boldsymbol u=0\)
forces \(K(\boldsymbol w\odot\boldsymbol Y^2)=0\) at the
next row, so its literal \(\boldsymbol g\) and \(P\) reads
enforce the same identity. This contradicts its \(X\) test
since \(-I(XY^2)/2=-1/(24a_0^2)\ne0\).
From now on \(\kappa\ne0\).

For any early physical donor with nonzero \(u_i\)
write \(L_i=w_i/u_i\), which permits \(w_i=0\).
At row \(Y=b\), the definite ratio is
\[
 L_1=-2,\qquad L_b=-2[1+2\kappa(b-1)]/b^2.
\]
The actual \(K\boldsymbol u\) and marked
\(K(\boldsymbol Y\odot\boldsymbol u)\) reads there also
give \(Q(b)=\kappa(b-1)\).
If the third physical interior label is \(1\) or \(b\),
these two reads fix its taps on the old two nonzero-\(u\)
donors, with their two different clocks, by an invertible
\(2\times2\) system. At \(1\) both are zero; at \(b\) its
tap on the old \(b\) is zero, and its tap on the first
\(1\) is proportional to that of the first \(b\). In
either case the primitive into \(\boldsymbol w\odot
\boldsymbol Y\) forces \((w,u)\) proportional to the
earlier row of that label. This holds without dividing by
the new row's \(u\), and contradicts early contrast.
Thus its label \(c\) is distinct from \(1,b\). Its \(u\)
cannot be zero, since the same two reads would then kill
both interior taps and give \(w=0\).

Let \(\Delta=3b\kappa-2c\kappa+c\) and put
\[
 \Lambda=\frac{b\kappa}{(b-1)\Delta},\qquad
 D=-\frac{b\kappa(b\kappa-c\kappa-c+2)}{\Delta}.
\]
The first three actual rows give
\[
\begin{aligned}
 Q(Y)&=\kappa(Y-1)+(b-1)\Lambda(Y-1)(Y-b),\\
 P(Y)&=2Y/3+\kappa(4b/3-2)(Y-1),\\
 R(Y)&=Y^2/2+\kappa(b^2-2)(Y-1)+D(Y-1)(Y-b),\\
 L_c&=-\frac{2(2bc\kappa^2+2bc\kappa-2b\kappa^2+b\kappa-2c\kappa+c)}
                    {c^2\Delta}.
\end{aligned}
\]
For the ingress to these formulas, solve the first two
\(\boldsymbol u\) reads at the third row: its taps on
the old \(\boldsymbol u\) entries, divided by that row's
nonzero \(u\), are
\((c-1)[\kappa-\Lambda(c-b)],\ \Lambda(c-1)(c-b)\).
Eliminating \(L_c\) from the first two scalar primitive reads
forces \((b-1)\Delta\Lambda=b\kappa\), so \(\Delta\ne0\).
Its first and third scalar primitives then give \(L_c,D\)
as shown. The [symbolic replay](audit.py) checks these
equations directly.

## Fourth physical interior: exact 5-by-5 compatibility

For a proposed fourth physical interior label \(z\), use
unknowns for the three earlier taps on \(\boldsymbol u\)
and the target's \(w_z\). The first two equations are the
\(\boldsymbol u\) and marked \(\boldsymbol u\) reads; the
next three are scalar primitive reads. Their right sides
are multiples of \(u_z\). The augmented homogeneous
matrix (last unknown \(-u_z\)) is
\[
\begin{pmatrix}
1&1&1&0&\kappa(z-1)\\
1&b&c&0&Q(z)\\
L_1&bL_b&cL_c&-z^2/2&1\\
L_1&b^2L_b&c^2L_c&-z^3/3&P(z)\\
L_1&b^3L_b&c^3L_c&-z^4/4&R(z)
\end{pmatrix}.
\]
Its determinant is exactly
\[
 -\frac{2b\kappa^3z^2(z-b)(b-1)(b-c)(z-c)^2(c-1)
                 (2\kappa-1)(z-1)}{c\Delta^2}.
\]
If nonzero, \(w_z=u_z=0\) and the coordinate is early
blind. Thus a new distinct \(z\) forces \(\kappa=1/2\).

For a repeated \(z\), the first four columns must have
rank below four to avoid early contrast: an old row of
the same label, with zero taps appended, gives a valid
solution proportional to the new unknown \(u_z\), so a
full column rank would force the same \((w,u)\) ratio.
The replay gives its two relevant four-row minors.
At \(z=1\), one is nonzero unless \(4b\kappa-2\kappa+1=0\).
Under that relation the other contains the nonzero
factors \(2\kappa-1=4b\kappa\) and \(b\kappa(1-c)\).
At \(z=b\), one minor is nonzero unless \(2\kappa+1=0\).
Then the other has nonzero factors \(2\kappa-1\) and
\((c-b)/2\). Neither repetition is possible.
At \(z=c\), the first minor is a nonzero
multiple of \(4b\kappa-2c\kappa+c\). Hence only an
immediate repeat at the third distinct label can remain,
and only with \(c(2\kappa-1)=4b\kappa\).

In fact \(\kappa=1/2\) is entirely impossible. The first
entry satisfies \(wY=-2u\). If this holds on earlier
rows, \(K(\boldsymbol w\odot\boldsymbol Y)=-2K\boldsymbol u
=-(Y-1)\boldsymbol u\) in the current row, while the literal
first primitive already equals \(wY^2/2+u\). Thus
\(wY=-2u\) there also (every interior \(Y\ne0\)).
By induction the \(X\) moment of \(\boldsymbol u\)
would be \(-I(XY)/2=-1/(12a_0)\ne0\).
This contradicts the grade-two test over any paid field.

## The exceptional repeat supplies two actual early-null donors

The only possible physical order now begins
\(0,1,b,c,c,d\), with \(c=4b\kappa/(2\kappa-1)\).
All of \(1,b,d\) are singletons as the sole pair
is at \(c\). Let the remaining singleton labels be
\(e,f,g,h\), chronologically. For the first row \(d\)
after the paired copies, the actual \(\boldsymbol u\)
entry is nonzero by the cofactor (it is a singleton).
At a generic target \(z\ne0,c\) with just that earlier
prefix, group the two \(c\) taps on \(\boldsymbol u\)
together; their scalar-score tap is a separate unknown.
This gives the five unknowns for the
\(\boldsymbol u\)-taps at \(1,b,c\), scalar tap at \(c\),
and \(L_z=w_z/u_z\), after dividing this one row by \(u_z\).
The coefficient matrix is
\[
 \begin{pmatrix}
 1&1&1&0&0\\
 1&b&c&0&0\\
 L_1&bL_b&0&c&-z^2/2\\
 L_1&b^2L_b&0&c^2&-z^3/3\\
 L_1&b^3L_b&0&c^3&-z^4/4
 \end{pmatrix}
\]
with right side \((\kappa(z-1),Q(z),1,P(z),R(z))^T\).
Independence of the two actual \(c\) tap directions is
not assumed: any available literal taps define such
a solution, which must obey the scalar result. Substituting
the special repeat in the determinant gives
\[
 -\frac{2b\kappa z^2(b-1)(2\kappa+1)
        [-4b\kappa+(2\kappa-1)z]^2(4b\kappa-2\kappa+1)}
             {(2\kappa-1)^4}.
\]
This is nonzero at \(d\): \(2\kappa+1=0\) would give
\(c=b\), and \(4b\kappa-2\kappa+1=(2\kappa-1)(c-1)\ne0\).
Cramer's rule gives
\[
 L_d=\frac{N(d)}{d^2(d-c)},\qquad
 N(Y)=\frac{2(4b\kappa^2Y-4b\kappa^2+2b\kappa Y+
                           2b\kappa-2\kappa Y+Y)}{2\kappa-1}.
\]
The same rational expression is exactly \(L_1,L_b\) at
\(1,b\). Moreover
\[
 L_i\,i(i-c/2)=c-2\quad\text{for } i=1,b .
\]
Both identities are independent exact cancellations in
the replay, without dividing by a physical score.

Set \(M(Y)=Y^2(Y-c)^2\) and \(G(Y)=(Y-d)M'(Y)/4\).
The literal grade-five precursor vectors
\[
\begin{aligned}
 \boldsymbol Z&=\boldsymbol w\odot M(\boldsymbol Y)
       -(\boldsymbol Y-c)\odot N(\boldsymbol Y)\odot\boldsymbol u,\\
 \boldsymbol G_*&=\boldsymbol w\odot G(\boldsymbol Y)
         +(2-c)(\boldsymbol Y-c)\odot(\boldsymbol Y-d)\odot\boldsymbol u
\end{aligned}
\]
vanish on the first six **physical** rows, namely \(0,1,b,c,c,d\).
For \(\boldsymbol Z\) use the three ratios at \(1,b,d\) and the
explicit factors at both copies of \(c\); endpoint zero is automatic.
For \(\boldsymbol G_*\) the two factors at \(c,d\), endpoint zero,
and the last ratio at \(1,b\) give the claim. Here
\(M'/4=Y(Y-c)(Y-c/2)\) and the \(\boldsymbol u\) coefficients
have degree at most two. Thus the actual grade-five test space
contains \(K\boldsymbol Z-\boldsymbol w\odot JM\) and
\(K\boldsymbol G_*-\boldsymbol w\odot JG\):
scalar polynomials in \(\boldsymbol w\) use the fourth
primitive, and a degree-two mark of \(\boldsymbol u\) followed
by \(K\) also has grade five.

## Raw cardinal collapse and the common rational nonic

Define \(\nu=(Y-H)(Y-f)(Y-g)(Y-h)\) and
\(U=(Y-H)(Y-g)(Y-h)\). The \(\nu\)-test on both
displayed grade-five profiles gives \(I(\nu JM)=I(\nu JG)=0\)
since the first remaining row \(e\) reads only zero contributors,
and \(f,g,h\) are killed by the test. The degree-five
primitives may be integrated by scalar precision nine;
the omitted opening origin \(Y=H\) is killed by \(\nu\).
The identity \(4JG=(Y-d)M-JM\) then gives
\(I(\nu(Y-d)M)=0\).

A separate nodal equation follows from the actual
coefficients. Write \(P_{10}=Y(Y-H)(Y-1)(Y-b)
(Y-c)(Y-d)(Y-e)(Y-f)(Y-g)(Y-h)\) and
\(\mu_z=I(P_{10}(Y)/(Y-z))\). The cardinal formula
gives grouped score \(W_z=\mu_z/P_{10}'(z)\)
by scalar degree-nine exactness. The aggregate of
\(\boldsymbol u\) is the grade-two cofactor, so
\(U_z^{(2)}=-\ell z/P_{10}'(z)\) for a common
nonzero \(\ell\), by factoring out \(H-Y\) from its
positive forward tests. Thus at \(z=1,b,d\) the
literal \(L_z\) identities give
\[
                   \mu_z z(z-c)=-\ell N(z).
\]
This holds for raw score-zero nodes as well as live ones.

Test the scalar polynomial \(\nu(Y-e)M\), whose only
possible contributions are \(1,b,d\). Each is
\(\mu_z z(z-c)/\prod_{t\in\{1,b,d\}\setminus z}(z-t)\).
These numerators are affine in \(z\); their ordinary
three-site interpolation cofactors annihilate degree at
most one. Thus \(I(\nu(Y-e)M)=0\).
Comparing with the preceding blind identity at \(d\),
\(d\ne e\) gives \(I(\nu M)=I(\nu YM)=0\).
Now test \(\nu M\) itself: only \(1,b,d,e\) contribute,
with the four-site cofactors of the same numerator.
They also annihilate the affine polynomial. Therefore
\(\mu_e e(e-c)=-\ell N(e)\) and hence the **raw** donor
\(Z_e=0\), with no division by \(w_e\).

The \(U\)-test on \(K\boldsymbol Z-\boldsymbol w\odot JM\)
now leaves only rows reading zero donors through \(e\);
it kills \(g,h\) and gives \(I(U JM)=0\).
Because \(\nu=(Y-f)U\) we also have \(I(YU JM)=0\).
These two moments and \(I(\nu M)=I(\nu YM)=0\)
are exactly the
[existing Cramer/nonic equations](../erk10-fifteen-two-pair-rational-closure/README.md#the-unconditional-collapse-and-rational-exclusion)
after rescaling \(Y/H\) back to interval \([0,1]\).
The small parameter in that system is \(c/(2H)\).
Its quartic pivot has no projective rational root
(modulo 19), and the remaining degree-nine numerator
has no projective rational root modulo 11. This excludes
the final rational case without any pooled-score guard.

## Replay

    python3 -B audit.py
    # From the overlay or repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-nine-label-one-pair/sources.sha256

The new early compatibility and raw tail ratios have independent
exact arithmetic. The whole word-budget and chronology bridge is
mathematical; portable scalar Lean receipts are tracked separately.
