# One invisible high zero, with nine distinct nonzero high clocks

**Theorem.** In the
[literal five-row decoder](../erk10-five-opening-nonsplit-kernel/README.md),
assume only the opening origin can carry an opening weight, and impose
the actual order-ten short reverse word budget. Among ten physical high
rows suppose exactly one has forward clock \(x=0\), all nine other
forward clocks are distinct, and \(x=1\) is the first reverse row.
Then the budget is impossible over every field with \(10!\ne0\).
No score assumption is made, including at the high zero or at either
origin. The exclusion is for this architecture, not a general
15-stage rational stage floor.

## What survives any number of high zeros

Let \(K=B^T\) in strict reverse causal order, \(y=1-x\),
and \(\boldsymbol w\) the physical high scores. Coordinates at \(x=0\)
are *invisible* to the positive forward-power tests. They are not
invisible to reverse causality or the observer vectors. Let \(D_d\)
be the span of true reverse word defects through grade \(d\).
A defect of grade \(d\) annihilates the actual columns
\(\boldsymbol x,\ldots,\boldsymbol x^{\odot(9-d)}\).
Clock marking by \(x\) or \(y\), and transport by \(K\), raise the
grade by at most one. These facts follow directly by duality from the
short budget, with the nominal reversed primitive \(J_y\), integration
from reverse ordinate zero. The first reverse row \(y=0\) has every
positive-grade defect zero: both the true strict primitive and its
nominal primitive vanish there, and clock marking preserves this.

The five nominal columns
\(\boldsymbol w,\boldsymbol w\odot\boldsymbol y,\ldots,
\boldsymbol w\odot\boldsymbol y^{\odot4}\) are independent modulo
\(D_4\). Their pairings with the first five positive forward powers
are the shifted Hilbert moment matrix (after the invertible basis
change \(Y=1-X\)); its determinant in the \(X\)-basis is
\(1/(2^{12}3^7 5^5 7^4)\).
The opening origin contributes zero to all these pairings. A high
zero, whatever its score, also contributes zero to the pairings,
but is not deleted from the observer columns.
In particular there are at least five distinct **nonzero forward**
labels carrying nonzero pooled high scores, since the moment matrix
factors through that pooled support.

The two forward annihilators use the first actual nonzero forward
high clock \(a_f\) and the first different **nonzero** one \(b_f\).
For \(T(f)=BEf-EJf\), \(f=X^k,\ 1\le k\le4\), their rows are
\[
 T(X^k)_{a_f}=-a_f^{k+1}/(k+1),\qquad
 T(X^k)_{b_f}=S a_f^k-b_f^{k+1}/(k+1),
\]
where \(S\) is the sum of actual taps onto prior \(a_f\)-rows.
Any earlier high zero gives exactly zero in both formulas. If the
two rows were proportional with scalar \(\lambda\), the ratio
\(r=b_f/a_f\) would satisfy
\(r^{k+1}=\lambda+(k+1)S/a_f\).
Second differences give \(r^2(r-1)^2=0\), impossible.
These residual columns annihilate both the nominal columns and
\(D_4\): pairing an actual grade-four observer with \(BEf\) or
\(EJf\) is allowed since the total positive degree plus word
length is at most nine. The two nominal paired values agree by
polynomial integration by parts. Consequently
\(5+\dim D_4+2\le10\).

If \(\dim D_4=3\), no nonzero additional annihilator of the nominal
and actual observers can be supported on an early reverse prefix
after which two different **nonzero forward** labels remain.
Indeed the two witness rows above still occur off that prefix, and
the annihilator space has exactly dimension two. We use this for a
single blind coordinate and for same-clock contrasts, without
requiring positive or nonzero scores.

Aggregate a vector only on distinct nonzero forward labels. The
grade-\(d\) visible aggregate annihilates \(X,\ldots,X^{9-d}\).
If the endpoint is unique, it is zero there and one removes the
endpoint column as well. On \(n\) remaining labels \(x_i\) with \(k\)
positive equations, the kernel is zero if \(n\le k\); otherwise it is
\[
 u_i=\frac{p(x_i)}{x_i\prod_{j\ne i}(x_i-x_j)},\qquad
 \deg p\le n-k-1 .
\]
This is Lagrange's leading-coefficient identity and Vandermonde rank.
Marking multiplies these aggregates by the same \(x_i\) or \(1-x_i\).
In particular with at least one high zero and a first reverse
endpoint, grade one always has zero visible aggregate: at most
eight visible labels, except for a unique endpoint plus eight
others, where the first endpoint defect is already zero. With \(m\)
visible labels, grade two has zero visible aggregate if \(m\le7\),
or if \(m=8\) and the endpoint is unique. In the remaining cases
(\(m=8\) with repeated endpoint, or \(m=9\) with unique endpoint)
its visible aggregate lies in at most one cofactor line on eight
effective visible sites. The pure kernel on vectors zero at the
first endpoint has dimension \(10-m\) if the endpoint is unique,
and \(9-m\) if it repeats. It includes the individual high-zero
coordinates, not just ordinary opposite pairs.

A leading forward run of high zeros may be merged into the
opening origin, with its weights transferred there, without any
assumption that they vanish. Inductively each such row only reads
earlier zero-clock high rows and the opening origin: at \(x=0\),
the decoder formula reduces to minus the high row sum times
opening origin evaluation. Its actual profiles are therefore
identical to the opening origin (and the origin tap absorbs the
retargeted zero-row taps). Subsequent high-to-old rows still have
the same decoder formula with the shortened high block. If all
high zeros occur in this leading run, one can restore width ten
by inserting unscored literal clones of a nonendpoint high row,
with all subsequent taps to each clone zero. The forward gate and
actual rooted order are unchanged, and so the previously proved
[nonzero-high architecture exclusion](../erk10-five-opening-three-endpoint-repeats/README.md)
applies over \(\mathbb Q\).

## Nine distinct visible high labels: grade-two leakage

Use the literal defects
\[
\begin{split}
 \boldsymbol u&=K(\boldsymbol w\odot\boldsymbol y)
                         -\boldsymbol w\odot\boldsymbol y^{\odot2}/2,\\
 \boldsymbol g&=K(\boldsymbol w\odot\boldsymbol y^{\odot2})
                         -\boldsymbol w\odot\boldsymbol y^{\odot3}/3,\\
 \boldsymbol h&=K\boldsymbol u,\qquad
 \boldsymbol k=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
                         -\boldsymbol w\odot\boldsymbol y^{\odot4}/4 .
\end{split}
\]
Their grades are \(2,3,3,4\). At the first live row with \(y\ne0\)
one has \(u_i=-w_i y_i^2/2\ne0\); at least one such row exists
by the support bound.

If \(\boldsymbol u\) leaks visibly, its cofactor is nonzero on all
eight effective visible labels. Therefore
\(D_4=\boldsymbol u\odot{\cal P}_2(\boldsymbol y)\).
And \(D_3=\boldsymbol u\odot{\cal P}_1(\boldsymbol y)\):
marking a genuine quadratic multiplier would give an independent
cubic on these eight labels. These are actual vector identities,
including the invisible coordinate. The physical ordinates are
all distinct, and only the first endpoint has \(y=0\). In
particular the forward zero is a perfectly nonzero reverse
ordinate \(y=1\).

Apply the actual [four-distinct head determinant and causal exit](../erk10-five-opening-nine-label-one-pair/README.md#fourth-physical-interior-exact-5-by-5-compatibility).
Its first three nonendpoint rows cannot be blind by the witness
argument above. In its normalization \(Y=y/a_0\), with first
nonendpoint ordinate \(a_0\ne0\), it first excludes
\(\kappa=0\) by \(u=-wY^2/2\) and the \(X\) moment.
Then the fourth distinct determinant forces \(\kappa=1/2\).
The causal transfer \(wY=-2u\) holds on **all** rows (both sides
zero at the initial endpoint), including the high zero at
\(Y=1/a_0\ne0\). Its \(X\) moment gives
\(-1/(12a_0)\ne0\), a contradiction. The first case's moment is
\(-1/(24a_0^2)\ne0\). The high zero affects neither moment
because its forward \(X\) factor vanishes.

## Nine distinct visible high labels: pure ghost

If \(\boldsymbol u\) has zero visible aggregate, it is a
nonzero multiple of the invisible coordinate. Every grade-two
defect is then pure: a leaking one and its first two marks would
give three independent aggregates, in addition to
\(\boldsymbol u\). The grade-three visible aggregate space is at
most one-dimensional. If it were two-dimensional, it would be
the full affine-cofactor space on eight effective sites; the first
marks would enlarge it to dimension at least three, again leaving
no room for the pure \(\boldsymbol u\) in \(D_4\).

In fact \(\boldsymbol h\) leaks. If pure, it is supported at the
same high zero, where its \(K\boldsymbol u\) entry is zero by
strictness. This is impossible: the first live \(y\ne0\) row must
be that ghost, and the first live normal nonendpoint row must pay
its first primitive through that one earlier live donor with
\(y\ne0\). The old scalar score and its nonzero \(\boldsymbol u\)
are proportional at this donor, so the target's \(h\ne0\).
Intermediate score-zero nonendpoint rows cannot supply a scalar
tap, regardless of their matrix entries. Thus
\[
 D_4=\langle\boldsymbol u,\boldsymbol h,
                     \boldsymbol y\odot\boldsymbol h\rangle .
\]
A nonzero grade-three aggregate is a nonzero affine cofactor
on eight sites, so it and its mark are independent.

The first physical nonendpoint must be the live ghost: if it
had another label then \(u=h=0\), and the first primitive with
only the endpoint available forces \(w=0\), a blind coordinate.
Denote the ghost's reverse ordinate by \(a\) (literally \(1\))
and the next three ordinates by \(b,c,z\), all distinct and
nonzero. From the entries at the ghost and the grade-three
aggregate dimension one, the vector identities are
\[
 \boldsymbol g=(2a/3)\boldsymbol u+\beta\boldsymbol h,\quad
 \boldsymbol k=(a^2/2)\boldsymbol u+\phi(\boldsymbol y)\odot\boldsymbol h,
 \quad K\boldsymbol h=\psi(\boldsymbol y)\odot\boldsymbol h,
\]
with \(\phi,\psi\) affine. The latter two \(\boldsymbol u\)
coefficients are fixed by evaluating at the ghost, since its
\(h=0\). This derivation never inverts another physical score.

The first normal row \(b\) has \(u_b=0\) and only the ghost as
positive-degree scalar donor. Its raw \(a\)-tap is \(w_b b^2/(2a)\);
\(h_b=-a w_b b^2/4\). A zero \(w_b\) would give blindness, so
\(h_b\ne0\), \(\beta=(4b-6a)/(3a)\),
\(\phi(b)=b^2/a-2a\), \(\psi(b)=0\).
At \(c\) the first two primitive equations force the raw \(a,b\)
taps \(w_c c^2(3b-2c)/(2ab)\) and \(w_c c^2(c-b)/b^2\).
Thus \(h_c=-a w_c c^2(3b-2c)/(4b)\);
\(w_c=0\) would again be a blind coordinate.
If \(3b-2c=0\) the composed read is
\((K\boldsymbol h)_c=-a w_c c^2(c-b)/4\ne0\) despite \(h_c=0\),
contradiction. Set \(\delta=3b-2c\ne0\).

On these four old donor rows, with componentwise polynomial
evaluation, the actual input identities are
\[
 \boldsymbol u=\eta\,\boldsymbol w\odot\boldsymbol y\odot
      (\boldsymbol y-b)\odot(\boldsymbol y-c),\qquad
 \boldsymbol h=P\,\boldsymbol w\odot\boldsymbol y+
 Q\,\boldsymbol w\odot\boldsymbol y^{\odot2}+D\,\boldsymbol u ,
\]
where \(\eta=-a/[2(a-b)(a-c)]\), \(P=-ac/2\),
\(Q=a(2c-b)/(4b)\), \(D=-c+a(2c-b)/(2b)\).
They hold component by component from the displayed rows, also at
the first endpoint regardless of its score. Applying \(K\) at
the next row gives two linear equations in \(h_z\) and \(w_z z^2\).
Use \(Y^3=(b+c)Y^2-bcY+Y(Y-b)(Y-c)\) for the cubic primitive
and the actual \(K\boldsymbol h\) equation for the other.
After clearing denominators they are
\[
 4b L h_z=a\delta M\,w_z z^2,\qquad
 4b N h_z=a\delta T\,w_z z^2 ,
\]
where
\[
\begin{array}{ll}
 L=5bc-3bz-4c^2+3cz, & N=bc+3bz-2c^2,\\
 M=-3z^2+4(b+c)z-6bc,&T=(2c-b)z-3bc.
\end{array}
\]
The exact determinant is \(LT-NM=9b(z-b)(z-c)^2\).
Thus \(h_z=0\) since the fourth nonendpoint label is new.
In the original reads, if \(w_z\ne0\) both \(M,T\) would be
zero, also giving zero determinant, so \(w_z=0\). This is a
blind coordinate since \(u_z=0\), contradicting the true off-prefix
forward witnesses. The pure case is therefore closed as well.

There is one further grade-one consequence in this pure case:
\(\boldsymbol v=K\boldsymbol w-\boldsymbol w\odot\boldsymbol y\)
is pure and hence proportional to \(\boldsymbol u\).
If the coefficient were nonzero, \(K\boldsymbol v\) would leak
visibly although every grade-two defect is pure. Therefore
\(\boldsymbol v=0\).

## Reproduce and scope

Run `python audit.py` in this directory (Python with SymPy) and
compare to `exact-audit.txt`. The
[portable core-Lean module](../../lean/RKCert/ReviewedNative/ERK10ZeroHighLargestScalars.lean)
checks the denominator-cleared two-read determinant and its field
exit, the forward second difference, and the scalar repeat factors.
The actual aggregation, shifted-Hilbert rank, and row identities
are established in the mathematical argument, not a Lean theorem
on a full order-ten tableau.
