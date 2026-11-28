# Rational closure of the five-opening, eight-clock two-pair cut

The ten-high two-pair chart of the
[five-opening rank-four decoder](../erk10-five-opening-nonsplit-kernel/README.md)
cannot give ordinary order ten over \(\mathbb Q\).
More precisely use eight distinct **nonzero** high scalar
clock labels, the unique reverse-first endpoint \(1\), two
physical pairs and all other labels singleton, nonzero physical
scores and nonzero pair aggregate masses, and the actual short
word budget of the five-opening construction. The old output
is supported only at the opening origin. No positivity or
fixed individual split is required. This is a coefficient-field
restriction on one physical architecture, not a general
15-stage rational lower bound. Its known
[15-stage characteristic-17 and 17-adic methods](../erk10-fifteen-17-power/README.md)
are consistent with the obstruction.

The [aggregate-exact and dual-active proof](../erk10-five-opening-two-pair-obstruction/README.md)
rules out everything except one active pair with grade-three
leakage. Its [head classification](../erk10-five-opening-two-pair-leakage-head/README.md)
leaves two possible reverse starts. Below both starts are
shown to give the very same necessary polynomial conditions.
In particular the zero additional donor response \(Z_d=0\)
is **forced**, rather than an optional search subchart of those
conditions.

## First exceptional head: actual necessity of all five equations

In reverse ordinates the first surviving pattern is
\(0,a,a,b,b\), \(b=2a\), the first pair active.
The remaining rows are five distinct singletons \(c,d,e,f,g\).
Write \(\boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2\)
and \(\boldsymbol h=L\boldsymbol u\).
The paid rank-four reverse grades imply, by the previous
head proof and \(b=2a\), the actual raw identities
\[
\begin{aligned}
 L\boldsymbol y^{\odot2}-\boldsymbol y^{\odot3}/3
                    &=(2a\boldsymbol u-2\boldsymbol h)/3,\\
 \boldsymbol k=L\boldsymbol y^{\odot3}-\boldsymbol y^{\odot4}/4
                    &=(a^2/2)\boldsymbol u-\boldsymbol y\odot\boldsymbol h,\\
 L\boldsymbol h&=(a\boldsymbol1-\boldsymbol y)\odot\boldsymbol h .
\end{aligned}
\]
The \(a\) group has weighted normalized mean \(h_a=-a^3/4\),
independently of its split. The raw \(h\) weight sum is the
seven-site cofactor line (it kills \(X,\ldots,X^6\)), hence
\(\mu_z h_z/z=-a^2\mu_a/4\) for every interior label.
Here \(\mu_z\) is the cardinal integral on the nine scalar
sites including \(0,1\), and \(h_z\) is its weighted
group mean. Nonzero scalar weights guarantee \(\mu_z\ne0\)
at all the guarded high sites. At the literal first singleton
\(c\), its earlier nonzero scalar donors are \(a,b\).
Substituting \(Y^3=(a+b)Y^2-abY\) in the true cubic read and
using \(u_c=0\) gives
\[
       (b-c)h_c=-c^2(c-b)^2/4,\quad
       h_c=c^2(c-b)/4,\quad
       c(c-b)\mu_c+a^2\mu_a=0 .
\]
The distinctness guard is \(c\ne b\).
The nine-site precision-nine nodal equation and this early
cardinal equation are the first two geometry equations.

Let \(M=Y^2(Y-b)^2\), \(G=Y(Y-a)(Y-b)(Y-c)\).
On the actual first six reverse rows,
\[
               (\boldsymbol y-b)\odot\boldsymbol h
                      -M(\boldsymbol y)/4-(a^2/2)\boldsymbol u=0 .
\]
At the first \(a\)-copy this follows from \(h=0\) and
\(u=-a^2/2\). Its weighted group mean is zero because
\(h_a=-a^3/4\) and the \(u\) group mean is zero, so the
second physical copy also pays this identity.
It holds at \(b\) by its vanishing factor, and at \(c\)
by the literal \(h_c\) just proved. Define \(\boldsymbol Z\)
by the left side; both \(G(\boldsymbol y)\) and
\(\boldsymbol Z\) vanish on the first six physical rows.

The actual grade-five defects
\(\boldsymbol m=L\boldsymbol y^{\odot4}-\boldsymbol y^{\odot5}/5\)
and \(\boldsymbol R=L(\boldsymbol y\odot\boldsymbol h)\)
kill \(X,\ldots,X^4\) by the true word budget.
In this test pairing the lower directions
\(\boldsymbol u,\boldsymbol h,\boldsymbol y\odot\boldsymbol h\)
also vanish. Substituting the three exact reads above gives,
modulo those lower directions,
\[
 \boldsymbol m=LG(\boldsymbol y)-(JG)(\boldsymbol y),\qquad
 \boldsymbol R-\boldsymbol m/4=L\boldsymbol Z+(JM)(\boldsymbol y)/4 .
\]
These identities use no assumption of individual raw row-sum
exactness.

Write \(T=(Y-e)(Y-f)(Y-g)\), \(\nu=(Y-1)T\).
The degree-four polynomial \(\nu\) is a true test in this
pairing, as in forward coordinates it is a scalar polynomial
vanishing at \(X=0\). It kills the rows \(e,f,g\), whereas
all earlier rows have no available nonzero \(G,\boldsymbol Z\)
input. The two displayed terminal identities therefore give
the exact blind equations \(I(\nu JG)=I(\nu JM)=0\).
The degree-three true test \(E_3=(1-Y)(Y-f)(Y-g)\)
kills \(f,g\); its only remaining response is a single
actual tap from \(d\) into \(e\). Thus the two requested
responses are proportional to \((G(d),Z_d)\). With the
cofactor expression for \(h_d\), this is the fifth
equation of the lift chart,
\[
  Z_d^* I(E_3 JG)+4\mu_dG(d)I(E_3 JM/4)=0 ,
             \qquad Z_d^*=4\mu_d Z_d.
\]
No generic terminal row solve is needed for **necessity**.
In particular this argument allows zero taps into \(e\).

## Second exceptional head: even a delayed active closure

The other surviving head has reverse labels
\(0,\alpha,a,b,b\), \(b=2a\), where \(\alpha\) is the
still-open active pair and the \(a\)-row is a singleton.
Let \(c\) be the very next scalar ordinate (the sixth
physical reverse row). It can be the active closure
\(c=\alpha\), or a distinct singleton with the second
\(\alpha\) occurring later. All four later **physical**
rows have distinct labels \(d,e,f,g\); if \(\alpha\) is
still open, its second copy is one of these four. Together
\(0,1,a,b,c,d,e,f,g\) are the nine distinct scalar labels
in either case. Thus \(c\ne d\) remains true.

Set \(\boldsymbol h^\#=(a/\alpha)\boldsymbol h\).
The actual early chart fixes
\[
 g=(2\alpha/3)u+\frac{4a-6\alpha}{3\alpha}h,\quad
 k=(\alpha^2/2)u+
            [\,2a^2/\alpha-2\alpha-(a/\alpha)y\,]h,\quad
                      Lh=(a-y)h .
\]
These follow from the first singleton \(a\) and the
first dormant copy \(b=2a\) in the prior determinant
proof. In particular \(h^\#_a=-a^3/4\) at the singleton,
so the scaled cofactor rule is again
\(\mu_z h^\#_z/z=-a^2\mu_a/4\).

On the predecessors of the sixth reverse row the
only nonzero \(u\)-coordinate is the first \(\alpha\).
Its actual vector there equals
\[
       -\frac{\alpha Y(Y-a)(Y-b)}{2(\alpha-a)(\alpha-b)} .
\]
Use this in the paid \(L\boldsymbol u\)-read, and
substitute the paid quadratic and cubic reads just
displayed. On a new singleton, or the weighted mean
at a just-completed active pair, the \(u\)-terms of
the targets vanish. This gives
\[
 \frac{a(2a-c)}{2(\alpha-a)(\alpha-b)}h_c
   =-\frac{\alpha c^2(c-2a)^2}{8(\alpha-a)(\alpha-b)} .
\]
The factor \(2a-c\ne0\), since both \(b\)-rows are already
used. It follows that \(h^\#_c=c^2(c-b)/4\), also in the
closure case. Thus the same early cardinal equation holds.

To get the exact terminal tests, use the two literal
donor profiles
\[
 \boldsymbol G_* = G(\boldsymbol y)+\frac{2G(\alpha)}{\alpha^2}
                                                  \boldsymbol u,\qquad
 \boldsymbol Z_* =(\boldsymbol y-b)\odot\boldsymbol h^\#
              -M(\boldsymbol y)/4-\frac{(\alpha-b)^2}{2}\boldsymbol u .
\]
They vanish at the **first six physical rows**. The
correction in \(\boldsymbol G_*\) kills the early
first \(\alpha\); if \(c=\alpha\), then \(G(\alpha)=0\)
and both copies already have the correct label.
For \(\boldsymbol Z_*\), the explicit first
\(\alpha\)-value is zero, and the normalized mean at
\(c=\alpha\) gives zero on the second copy if it is
already present. These checks also cover both dormant
rows since \(Y-b=0\) there. The correction terms have
only \(L\boldsymbol u=\boldsymbol h\) in their
reverse actions, which is a lower paid direction.
Using \(\boldsymbol h^\#\) in place of \(\boldsymbol h\)
therefore gives the same two nominal targets \(JG\)
and \(-JM/4\) for the two donor responses, by the
same scalar expansions. The blind \(\nu,E_3\) arguments
apply verbatim to these actual row actions.

If tail node \(d\) is the deferred second \(\alpha\),
let \(\lambda\) be the first \(\alpha\)'s share of
its grouped mass. Its physical \(u\) is
\(\lambda\alpha^2/(2(1-\lambda))\), and its
physical \(h^\#\) is the group value divided by
\(1-\lambda\) (the first copy has \(h^\#=0\)).
Consequently both actual responses
\((G_{*,d},Z_{*,d})\) are the corresponding scalar
group values \((G(d),Z_d)\) times
\(1/(1-\lambda)\), a unit. Thus the proportionality
constraint and hence the fifth geometry equation are
unchanged. If \(d\ne\alpha\) they are already exactly
the scalar values. If the deferred copy is \(e,f\)
or \(g\), the same blind polynomial kills it, and
also its earlier copy if that is the same label.
The earlier copy has zero response by chronology
regardless. This proves necessity for **all later
closure placements**, not only closure at the
sixth row.

## The unconditional collapse and rational exclusion

Use the simplified scalar identities of the
[pressure-curve derivation](../erk10-fifteen-rational-pressure-curve/README.md):
the first two geometry equations give \(I(\nu(Y-d)M)=0\),
the two blind equations give \(I(\nu JG)=I(\nu JM)=0\),
and the fifth simplifies to
\[
               I(\nu G)I(U JM)-I(\nu M)I(U JG)=0,
               \qquad U=(Y-1)(Y-f)(Y-g).
\]
Here \(Z_d^*=-G(d)I(\nu M)\); this identity uses both
nodal equations and does not require \(Z_d^*\) nonzero.

The derivative of \(M/4\), when \(b=2a\), is precisely
\(G_1=Y(Y-a)(Y-b)\). Therefore
\[
                         4JG=(Y-c)M-JM.
\]
The two blind equations force \(I(\nu(Y-c)M)=0\).
Together with the nodal \(M\)-equation and \(c\ne d\)
this gives the **unconditional**
\(I(\nu M)=0\), and \(Z_d^*=Z_d=0\).
The distinctness and nonzero mass hypotheses guarantee
\(G(d)\ne0,\ \mu_d=I(\nu G)\ne0\) at the actual high
label \(d\), also if it is a late duplicate.
The fifth and blind equations then give
\(I(U JM)=I(Y U JM)=0\).

Write \(U=(Y-1)(Y^2+mY+n)\). The two exact \(JM\)
moment equations determine \(m,n\) by a two-by-two
matrix with quartic determinant factor \(B(a)\).
The [exact scalar replay](../erk10-fifteen-rational-pressure-curve/exact-audit.txt)
checks \(B\) has no projective root mod 19, so this
pivot is paid over \(\mathbb Q\). Then the two nodal
\(M\)-conditions imply
\(I(UM)I(UY^2M)-I(UYM)^2=0\), whose numerator is
\(-a^2 N(a)\) for the degree-nine polynomial \(N\)
in the replay. The exact projective mod-11 certificate
excludes any rational root of \(N\); \(a=0\) is
forbidden. Thus neither exceptional head has any
rational continuation. Together with the previous
grade-three obstruction this closes the full
specified two-pair cut over \(\mathbb Q\), with its
nonzero mass/share guards. Other counts of scalar
sites, dormant zero weights, and other opening
architectures remain separate.
