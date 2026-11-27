# Old-terminal overlap: exact exclusions and remaining stage counts

A real order-15 method in 33 stages is still not constructed. The
[general refund](../real-sdirk-grouped-terminal-refund/README.md)
excluded the wholly paid single-port bridge with the protected
forward port **disjoint** from old reverse terminal means.
This packet covers the change where an old reverse physical
terminal occurrence itself supplies the literal shared stage.
The exact-stage commutator identity below now excludes **all**
meshes at 33 stages, not only the minimum eight-site mesh. The
same proof also closes old-terminal overlap for the analogous
25-stage order-13 chart. The finite eight-site algebraic replay
is an independent exclusion for this fixed order-15 stem.

## Actual overlap and the latest representative

Consider the same fixed real-algebraic 15-row stem, its genuine
size-eight port $v$, and its unique size-seven residual mode $Q$.
Assume the whole physical column $(E_xJ-BE_x)Q=0$ as before.
Instead of merging a fresh reverse representative at $v$ into that
old forward row, suppose an occurrence at an already paid reverse
terminal is the literal protected row. Thus it has nonzero
physical output share and its actual reverse column has only its
unit diagonal. The old reverse prefix precedes all new
representatives in reverse chronology.

The first actual reverse clock is $y=1$ since the common
normalized diagonal is one. Its scalar forward site is $1-\gamma$
in the interval-normalized quadrature. The protected one is
$\gamma v$. If there is any new representative, the last reverse
one has no later physical taps and hence its forward strict tail
is zero off the diagonal. Whole-column payment then requires its
forward normalized clock $w$ to satisfy $(J-I)Q(w)=0$. It is
distinct from $v$, as $v$ is an old terminal. This is a constraint
on the actual first forward suffix row, not freely assigned
quadrature data.

## Fixed eight-site mesh is impossible

An eight-site interpolatory rule of precision fourteen has monic
node polynomial in the span of the shifted Legendre polynomials
$P_8,P_7$: multiply the node polynomial by every polynomial
through degree six and use exact moments. This requires no sign
assumption or interior-node restriction. At every candidate
$\gamma=g$, the three required knots above force
\[
 F(g,v)=F(g,w)=0,\quad
 F(g,u)=P_8(gu)P_7(1-g)-P_7(gu)P_8(1-g).
\]
This necessary cross-product includes all coincidences between
the initial reverse site and either marked site. It does not
divide by $P_7(1-g)$. The exact shifted-root quotient
$R(U)=((J-I)Q)(U)/(U-v)$ has degree six. The fixed port
cross-polynomial $F(G,v)$ has degree fifteen.

The standard-library replay constructs the 90-by-90 matrix for
multiplication by $F(G,U)$ on
\[
 \mathbb R[G,U]\big/(F(G,v),R(U))
\]
in the basis $G^i U^j$, $i<15$, $j<6$. A common zero in any
extension field would give an evaluation homomorphism taking
this element to zero, contradicting its invertibility. The
directed 1024-bit calculation certifies every elimination pivot
nonzero, with smallest absolute pivot at least $2^{-49}$.
It tightens exactly the certified Laguerre/jet branch, not a
new nearby branch. Thus no eight-site precision-fourteen grid,
with any real nonzero common diagonal, can have all three paid
sites. If every site were already terminal, their evaluations
would kill the old top residual and refund eight independent
length-seven responses, requiring $12+8=20$ old reverse rows
and at least $15+20-1=34$ overall.

## The protected old coordinate restricts the other terminal count

Let $s_r$ be the old reverse row count, $N$ the number of scalar
sites, and $t$ the number of old terminals **including** the
protected one. There are $N-t$ new representatives, and just
one literal deletion. The mixed clock frame sees $t-1$ of the
old terminals, so at least $t-N+7$ independent additional
responses are paid there when that number is nonnegative and
$t\le7$. If $t\ge7$, saturation already pays at least seven
responses, and either $N>t$, giving at least 34 stages, or
$t=N\ge8$, when it pays eight. Therefore it suffices to
consider $t\le6$. The old lower packet needs 12 rows, so a
33-stage candidate has $t\ge N-7$. In fact its row count
has to be the exact packet count
\[
 s_r=12+d,\qquad d=t-N+7.
\]
Here $d$ is the rank of the refunded next-grade targets at
disjoint terminals. Higher rank would already have charged an
extra old row.

Let $\mathbf e_*$ be the old protected physical coordinate.
It is a joint right eigenvector of the actual old primitive
and clock matrices $L,C$, with eigenvalues $1,y_*$.
In particular their word commutator satisfies
$\Theta\mathbf e_*=-\mathbf e_*$. The refunded old means
are supported at other sites, so their whole readout vanishes
on $\mathbf e_*$. At the exact count the independent four
commutator blocks are a basis of the old space. Applying the
refunded readout to $\mathbf e_*$ kills the leading block;
the other three are $\Theta$ times the lower paid packet.
Since $\Theta$ is invertible and $\mathbf e_*$ is its
eigenvector, $\mathbf e_*$ is itself in that lower packet,
in particular the actual word span through length five.
This conclusion also holds when $d=0$.

Write $P$ for the model polynomial from this representation,
of degree at most five. At every other terminal $a$ both
$P(a)$ and $(JP)(a)$ are zero, since the means there are
exact through length six and $L\mathbf e_*=\mathbf e_*$.
At $y_*$ both values are the nonzero physical share in its
terminal mean, so $JP$ is nonzero and $y_*\ne0$. The
nonzero polynomial $JP$, of degree at most six, has a
double zero at every other terminal and a zero at 0.

## Two actual top responses force a contradiction

The old protected coordinate obeys ((C-y_*)mathbf e_*=(L-I)mathbf e_*=0).
Apply these operators to its actual lower-word representation.
The two formal polynomial images
[
 K_C=(X-y_*)P,qquad K_L=(J-I)P
]
belong to the genuine **top residual** space $V$: their physical
old vectors are zero, and their polynomial degrees are at most
six. Allowing the lower word terms in these linear combinations
is valid because the old decoder is exact on all lower words.

Let $mathbf m=Mmathbf e_*$ be the vector with one nonzero
coordinate at the protected terminal, and put
$mathbf u=E_yP-mathbf m$. This vector vanishes at **every**
old terminal. The actual column $Lmathbf e_*=mathbf e_*$
and grouped mean identity give
[
 E_y JP=mathbf m+Smathbf u .
]
If $Y$ is the reflected-clock diagonal, then
$E_y K_C=(Y-y_* I)mathbf u$ and
$E_y K_L=(S-I)mathbf u$. Using $JX=XJ-J^2$,
the two next-primitive discrepancies therefore add to
[
 oldsymboldelta(K_C)+oldsymboldelta(K_L)
    =(S^2+SY-YS)mathbf u+mathbf m .
]
The non-port part is supported solely at the fresh representative
sites: terminal rows of $S$ are unit coordinate rows, and
$mathbf u$ is zero there. At 33 stages there are at most seven
fresh representatives since the lower old bank needs at least
12 rows. The seven-dimensional mixed test frame vanishing at
the port can take arbitrary values on those at most seven
distinct live sites, by interpolation. The required mixed
pairing, with each aggregate weight nonzero, now forces
$(S^2+SY-YS)mathbf u$ to vanish there. Its live restriction
is lower triangular with diagonal one, because the live part
of $S$ has these properties and the terminal values stay zero.
Hence $mathbf u=0$.

This would make $P$ vanish at **all** the non-port sites.
There are at least seven such sites, whereas $deg Ple5$.
This contradicts the nonzero share $P(y_*)$ at the
protected terminal. It rules out the literal overlap at
33 stages independently of the eight-site exact arithmetic.

The same argument works with $r=5$ for the coupled
11-row order-13 stem. The generic budget is
$s_r+N-tle L(r)+r+1$, and saturation at $tge r+1$
already exceeds it: if $N>t$ at least one new representative
is needed; if $N=t$ at least $r+2$ exact top evaluations are
available. In the unsaturated case the exact packet count
forces the protected old coordinate into words through
length $r-1$. The live count is at most $r+1$ and the
degree-at-most-$r-1$ model cannot vanish at $N-1ge r+1$
non-port sites. Thus both 25 and 33 are excluded in this
whole-column-paid, single-literal-merge grouped architecture.
None of these arguments exclude different forward stems,
multiple actual merges, a different reverse architecture,
or nonzero signed $Q$ error with ordinary cancellation.

The [native companion](../../lean/evidence/sdirk-protected-terminal-refund-20261127/README.md)
checks the physical eigenvector implication at exactly the
lower packet count, live-site interpolation, the actual
commutator identity and the live lower-triangular solve.

## Exact replay

From this directory, with the two previous research packets
as siblings:

```sh
sha256sum -c sources.sha256
helper="$(mktemp -d)"
stem="$(mktemp -d)"
python3 ../real-sdirk13-joined-interface/refine_ports.py "$helper"
python3 refine_stem15.py "$stem"
PYTHONDONTWRITEBYTECODE=1 python3 check_eight_overlap.py "$helper" "$stem"
PYTHONDONTWRITEBYTECODE=1 python3 check_only_port.py "$helper" "$stem"
```

The matrix entries and pivots are directed dyadics from
exactly the tighter enclosed stem. No floating matrix rank,
approximate roots, or ordinary tree residual containment is
claimed as proof of the nonzero pivots. The separate rooted
replay rules out a second **distinct** size-eight pure row of
the fixed stem: each row other than 14 has a physical rooted
defect of magnitude at least $2^{-2}$ in normalized units.
This does not prohibit several suffix occurrences merging into
the same stem row. The count/overlap proof is separate from
these arithmetic replays.
