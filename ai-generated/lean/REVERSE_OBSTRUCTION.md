# Order twelve: one two-site proof of the reverse rank-one obstruction

## Scope

Let a strictly lower Runge–Kutta tableau over a characteristic-zero field
satisfy all rooted-tree order conditions through order twelve. Suppose its
stage count is at most seventeen. Write E_j for the actual stage spaces,
B_n for the zero-based backward spaces, N=Aᵀ, Y=diag(1−c), and v=b as a
column, reading rows in reverse chronological order. The known equality
conditions force 17 stages and dim B_n=n for n=0,…,4, with B_3=ann(E_7),
B_2=ann(E_8), B_1=ann(E_9), and dim E_9=16. The objective here is just
to exclude Y-invariance of B_1, and thereby prove E_10 is the entire
17-dimensional stage space. This lemma itself does not show that there is
no 17-stage tableau. A distinct forward argument is required for that
conclusion. No assumptions on signs, repeated nodes, or individual
nonzero weights are made.

## Reduce the five grade conditions to two feature columns

Write y=1−c componentwise; Y^k v means y^k v. If B_1 is invariant,
d=NYv−Y²v/2 spans B_1 and is supported on one node a. It is nonzero
at the first active yv; evaluated there NYv=0, so d=−a²v/2 and a≠0.
The actual rank recurrence gives g=Nd outside this line. The noninvariance
of B_2 and B_3 from reverse Hermite gain and the exact ranks give
B_2=span(d,g), B_3=span(d,g,Yg), B_4=span(d,g,Yg,Y²g).
The residuals NY²v−Y³v/3 and NY³v−Y⁴v/4 lie in B_2 and B_3 by true
tree-order testing. The vectors Ng and NYg lie in B_3 and B_4.
Comparing at the same first active yv, where g=Ng=NYg=0, eliminates the
d term in the last two vectors and fixes its coefficient at 2a/3 and a²/2
in the two primitive residuals.

Make the linear change of feature

    h=Yv+(2/a)d,       G=g/a.

Since Yd=ad, the d terms cancel. For some field scalars β,q,l,k,e,m,f,r,
all actual rows satisfy

    Nh = Yh/2 + 2G,
    NYh = Y²h/3 + βG,
    NY²h = Y³h/4 + (q+lY)G,
    NG = (k+eY)G,
    NYG = (m+fY+rY²)G.

The first observation is h=0 at y=0. Moreover, h cannot be supported
on just two nodes t,u: outside {0,a,t,u} it equals yv; order twelve has
at least six distinct nonzero original nodes of nonzero aggregate mass,
hence cannot place all nonzero physical weights on these four reflected
nodes. This last step is algebraic over every characteristic-zero field;
one need not integrate a positive square.

## Determine the first two distinct h nodes

Let t be the reflected node of the first nonzero h row. Before it h=G=0;
at it G=−th/4≠0. Put Φ(x)=x(2x−3t)/(4t). Evaluating the next equations
there gives β=4t/3, q+lt=t², k+et=0.

Let u be the first different node with nonzero h. Before it the incoming
h is supported at t. Consequently NYh=tNh up to and including this row.
The first two equations imply G=Φ(x)h throughout this prefix, including
all intermediate rows with h=0. At u the quartic and NG equations read

    t²(uh/2+2G)=u³h/4+(q+lu)G,
    Φ(t)(uh/2+2G)=(k+eu)G.

Their right side in the second equation is −u(u−t)h/4≠0. In particular
G=Φ(u)h≠0 and 3t−2u≠0. With D=t/(3t−2u), solving the equations gives

    k+ex = D(x−t),      q+lx = t²+D(u−t)(x−t).

Also NYG=tNG at u because previous G entries were supported at t; thus
m+fu+ru²=t(k+eu). This is the only special value of the quadratic
coefficient needed.

## One induction, including repeats and weights equal to zero

Assume all earlier h entries are supported on t or u and G=Φ(y)h there.
At the next row let x be its node, H its h value, and g its G value.
Let T,S be N applied to h masked to the t and u fibers and evaluated
in this row. Strict causality and linearity give

    T+S=xH/2+2g,
    tT+uS=x²H/3+(4t/3)g,
    t²T+u²S=x³H/4+(t²+D(u−t)(x−t))g,
    Φ(t)T+Φ(u)S=D(x−t)g.

The first two give g=Φ(x)H−3(u−t)S/(2t). Substitute this and the first
equation into the third and fourth residuals (left minus right). The
third residual minus t/2 times the fourth is exactly

    (3/4)(t−u)(x−u)S.

Hence S=0 if x≠u. If x=u, the shifted equation and the quadratic value
at u give N((Y−t)G)=0 there. From previous support its left side is
(u−t)Φ(u)S; this coefficient is nonzero, so S=0 also at a repeat.
Now g=Φ(x)H. The fourth equation reduces to
−x(x−t)(x−u)H/[2(3t−2u)]=0. Since H vanishes at zero, either x=t or x=u
or H=0. This closes the induction for all physical rows. It contradicts
the support count above. No split according to the original localized
node a was necessary; it can coincide with t or u.

Therefore B_1 is not Y-invariant. If E_9 were C-invariant, its full
annihilator B_1 would be Y-invariant by bilinear transpose. E_10
therefore strictly contains the rank-16 E_9, and is the entire ambient
space. This proof is an algebraic replacement for the three chronology
branches of the earlier Appendix A.
