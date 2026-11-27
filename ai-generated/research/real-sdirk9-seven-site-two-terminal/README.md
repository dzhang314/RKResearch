# Seven scalar sites and two paid old terminals are impossible in the SDIRK9 twin-port bridge

This excludes the grouped chart $(N,t,s_r)=(7,2,4)$ at thirteen stages, with the same six-row forward family and the same two disjoint literal protected merges. The nominal count is $6+4+5-2=13$. It is independent of the [six-site](../real-sdirk9-six-site-three-terminal/README.md) and [seven-site](../real-sdirk9-seven-site-three-terminal/README.md) three-terminal eliminants.

## Actual chronology and the two genuine residuals

The two old reverse terminal groups require word length three. Neither of the first two physical rows can pay this alone, and a mean of them cannot pay it either. Since there are only four old rows, the terminal groups therefore use one of rows three and four each, possibly with earlier same-site shares. The [first-four-row classification](../real-sdirk9-seven-site-three-terminal/README.md#the-actual-first-four-reverse-rows-are-forced) applies without a fifth row. It excludes these early same-site repeats by testing the literal strict mean on the quadratic clock frame and on the actual quadratic defect. The four old clocks in unit-diagonal coordinates are consequently
$$
 1,\quad a=(1+s_r)/2,\quad s_r,\quad t_r,\qquad
 s_r^3-9s_r^2+18s_r-6=0,\quad t_r^2-(s_r+3)t_r+s_r=0 .
$$
Rows three and four are individually exact through reverse word length three.

The old reverse decoder is exact through length two. Its genuine cubic residual span $V$ at length three vanishes at these two terminal clocks, hence has dimension at most two. It has dimension at least two: the first-excess commutator packet through length three charges $6-\dim V$ rows. To see this in the present length convention, take a complement to the error space in the four-dimensional cubic model, lift its clock words into the actual rows, then add the invertible commutator applied to the two length-one clock columns. In a relation, paid cubic readout modulo the error separates the first block; cancellation of the invertible commutator and the dense linear return separate the last two. Four old rows therefore imply
$$
 V=\operatorname{span}\{K_0,K_1\},\qquad
 K_0(Y)=(Y-\gamma s_r)(Y-\gamma t_r),\quad K_1(Y)=Y K_0(Y)
$$
in the normalized physical reflected variable $Y$ on $[0,1]$. These two tests concern an actual polynomial error space, not arbitrary nominal terminal cubics.

## Causality makes a quartic test exact

Let the three unprotected fresh representatives have physical reflected clocks $b_1,b_2,b_3$ in increasing **reverse chronology**, not necessarily numerical order. The other two fresh representatives are the literal protected ports $1-\gamma v,1-\gamma w$. The protected physical columns force the corresponding grouped columns to be unit coordinates. Inputs at either old terminal vanish on $V$. The only relevant strict corrections among the live sites thus enter at $b_2$ or $b_3$. Set
$$
 G(Y)=(Y-(1-\gamma v))(Y-(1-\gamma w))(Y-b_2)(Y-b_3).
$$
This is a degree-four member of the full forward mixed test space after reflection. It kills both protected output rows and **both** live rows that can contain correction taps. In the ordinary size-five-source mixed identity, its remaining pairings against the literal reverse primitive discrepancies must vanish. They give
$$
 \mathcal I\bigl(G(J-\gamma I)K_0\bigr)
 =\mathcal I\bigl(G(J-\gamma I)K_1\bigr)=0 .
$$
Here $Jf(Y)=\int_0^Y f(Z)\,dZ$, and $\mathcal I=\int_0^1$. The subtraction $-\gamma I$ comes from the common diagonal in physical coordinates and is not dropped. Both integrands have degree at most eight. Quadrature gives the other two equations,
$$
 \mathcal I\bigl(Y^jG(Y-b_1)K_0\bigr)=0,\qquad j=0,1,
$$
because the degree-seven polynomial is the whole node hull. Thus the two cotangent defects produce two actual primitive constraints in addition to the scalar ones.

## All placements of the early reverse clocks are eliminated

The early clocks $\gamma,a\gamma$ are distinct, and neither is a terminal. Each belongs to the set of two ports and three live sites.

- **No early clock is a port (six placements).** Prescribe two of $b_1,b_2,b_3$ to be $\gamma,a\gamma$. The four equations are affine in the remaining live coordinate $z$. Their four coefficient pairs on $(1,z)$ must have all $2\times2$ minors zero. If $b_1$ is free, the two primitive rows are independent of $z$, with degree at most seven in $\gamma$; the scalar rows have degree at most six. The minors have degree at most thirteen. Otherwise one affine clock factor in $G$ is free, and all four rows have degree at most six, so the minors have degree at most twelve. The replay finds two full-degree coprime minors for every placement.
- **Exactly one early clock is a port (twelve placements).** The port equation makes $\gamma$ constant in the branch field. The other clock fixes a live site. If it fixes $b_2$ or $b_3$, the primitive pair is affine in the other late clock, and its $2\times2$ coefficient determinant is nonzero. If it fixes $b_1$, the four equations depend on the two later clocks only through their sum and product. The coefficient matrix on $(1,b_2+b_3,b_2b_3)$ has a nonzero $3\times3$ minor. The choice of which two variables are processed is based on chronology, not on numerical sorting.
- **Both early clocks are ports (two placements).** This would express the forward $w$ as $v+1-a$ or $v+a-1$. The field $\mathbb Q(s_f,v,s_r)$ extends $\mathbb Q(s_f,v)$ by degree at most two, while $w$ has degree three over the latter by the [forward tower proof](../real-sdirk9-six-site-three-terminal/README.md#exact-reduction-covers-every-regular-port-conjugate). Both placements are impossible.

The good-reduction residues and relative irreducibility witnesses are identical to those in the [seven-site three-terminal proof](../real-sdirk9-seven-site-three-terminal/README.md#complete-placement-elimination). At prime $43$ the forward triple is $(s_f,v,w)=(26,16,39)$; the reverse root classes have simple lifts of $(s_r,t_r)=(26,18),(41,2)$. The degree-preserving coprime pairs give nonzero resultants in the characteristic-zero branch fields. The pinned determinant values are units at the same prime. These lift exclusions to every conjugate of both root classes, independently of signs, output fractions, or exterior sites.

## Reproduction

    sha256sum -c sources.sha256
    python3 check.py

The exact SymPy replay uses the shared forward irreducibility helpers from the six-site packet, but builds the two-terminal primitive rows and rank equations anew. The [Lean 4.36.0 audit](../../lean/evidence/sdirk9-seven-site-two-terminal-20261127/README.md) kernel-checks the twelve emitted Bézout identities and twenty-four pinned nonzero residues. The algebraic transfer and ordinary-order necessity proof are mathematical.

The only two-disjoint-port grouped counts not addressed by these three packets are $(6,1,4)$ and $(6,2,5)$. No unrestricted order-nine stage bound changes and no thirteen-stage witness is asserted.
