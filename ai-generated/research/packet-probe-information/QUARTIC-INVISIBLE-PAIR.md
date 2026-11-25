# A proper early quartic packet is not identified by *all* ordinary rooted orders at fixed b and c

**Theorem.** Let $P\in\mathbb Q[X]$ be a nonzero polynomial of degree $d\ge1$ with $P(0)=0$. Fix any list of distinct rational roots beginning with 0 to use as discarded physical clocks. For $p\ge d+3$ there are two same-size rational strictly explicit tableaux, with identical physical clocks and identical individual weights (each nonzero), of **exact** order $p$, such that

1. the prescribed prefix is covered by $P$, the counted suffix contains nonzero $P(c)$, and both tableaux have identical scalar outputs $b^T\Phi(t)$ for **every** finite rooted tree $t$, without a degree bound;
2. for the first tableau $T(P(c))=0$, while for the second it is nonzero; the actual grade-zero masked packet $F_0=\operatorname{span}\{P(c)|_{\rm suffix}\}$ has first-step loss $1$ versus $0$;
3. their native single-output tree contractions, even allowing arbitrarily many holes and arbitrary finite costs with tree-generated fills, cannot identify this packet rank. The *two separately output-weighted, same-coordinate* collision square $\sum_i b_i^2(T(P(c))_i)^2$ does identify the difference.

The examples deliberately use redundant stages with signed cancelling weights at equal clocks. They do **not** assert this impossibility for irreducible tableaux, for all-positive weights, for distinct clocks, or for a counted nonsingular DIRK subblock. The latter has invertible triangular $T_*$ if all its diagonals are nonzero, so the same zero/nonzero first-step pair would be impossible there.

## Construction of a high-order explicit core with $T(P(c))=0$ at every physical stage

Use an initial stage at $c=0$ with zero row. Choose $L\ge\max(p+1,d+2)$ distinct rational interpolation nodes $x_i$, ordered so the desired nonzero discarded roots come first and including two distinct nonroots $u,v$ with $u\ne0$. Make a starter panel $U_i$ with clock $x_i$ by giving its row coefficient $x_i$ on the initial stage and zero elsewhere. The first physical stages are now exactly the desired discarded prefix; it consists also of the initial stage. At the origin and throughout $U$, $AP(c)=0$ and $T(P(c))=0$, because $P(0)=0$.

Make a second panel $V_i$ at the same nodes. For the row at $x$, let $J(x)=\int_0^x P(z)dz$ and take its only nonzero candidate coefficients on the origin and $U_u,U_v$. Write

$$a_u=\frac{J(x)(v-x)}{P(u)(v-u)},\qquad a_v=\frac{J(x)(x-u)}{P(v)(v-u)},\qquad a_0=x-a_u-a_v.$$

These give the target clock, $AP(c)=J(x)$, and $A(cP(c))=xJ(x)$. All referenced previous $AP(c)$ entries vanish. Consequently $T(P(c))=cAP(c)-A(cP(c))-A^2P(c)=0$ on $V$.

Now put $p-1$ further panels after $V$, each with the same nodes, with every row using only the immediately preceding panel. For the row at $x$ use

$$ B_{xi}=\int_0^x \ell_i(z)dz,$$

where $\ell_i$ are the Lagrange cardinal polynomials on the $L$ nodes. These rational rows integrate every polynomial of degree $\le L-1$. Since $P$, $zP(z)$ and $J$ have degree at most $d+1\le L-1$, every new row has $AP(c)=J(x)$, $A(cP(c))=I(zP)(x)$ and, using the preceding panel property, $A^2P(c)=I J(x)$. The polynomial identity $xJ(x)-I(zP)(x)-I J(x)=0$ makes all its $T(P(c))$ entries zero as well. The tableaux are strictly explicit since later panels use only earlier ones, irrespective of how the numerical clocks are ordered.

The final panel has exact **stage expressions** for every tree of order at most $p$: on node $x_i$ its value is $(n/\gamma(t))x_i^{n-1}$. Induct on the height of the tree. Every panel has the correct leaf; a further integration panel advances the permitted height by one, integrating each child monomial exactly and multiplying the resulting branches. Heights of trees of order $p$ are at most $p$. Thus $p-1$ panels after $V$ suffice. There is no claim that the entire tableau has high stage order.

Initially weight only the final panel. For $k<p$ prescribe $\sum b_i x_i^k=1/(k+1)$, and prescribe $\sum b_i x_i^p=0$. Distinct nodes and $L\ge p+1$ make these rational linear constraints consistent. For example on the space of polynomials of degree $<L$ use the functional $f\mapsto\int_0^1f(x)dx-[x^p]f/(p+1)$ on the cardinal basis. All scalar trees through order $p$ are correct by the stage formula; the bush of order $p+1$ fails since its scalar is zero. The core has exact order $p$ and $TP(c)=0$ literally, not merely after the native read.

## A hidden pair that changes literal transport but never changes a scalar rooted tree

Append two terminal stages with the same chosen nonzero clock $y\ne u$ and opposite nonzero output weights $+1,-1$. There are no outgoing dependencies on either stage. Within *each* tableau these two rows are identical. In tableau 0 let the row use only the origin with coefficient $y$. In tableau 1 let it use only the earlier starter stage $U_u$ with coefficient $y$. All other rows, weights and clock coordinates of the two tableaux coincide. The two terminal elementary stage values are identical to each other for every tree within either tableau. They therefore cancel in their signed output for every tree, at any order; the original stages were not altered. The two complete scalar root series are thus identical.

In the first tableau both terminal $TP(c)$ entries vanish. In the second they are

$$y^2P(u)-yuP(u)-y(AP(c))_{U_u}=y(y-u)P(u)\ne0.$$

All other entries are zero. Restriction to the proper suffix preserves this difference, because the mask vanishes on the discarded prefix and the early chronological suffix is $T$-invariant. The seed has rank one in both; its stepped matrix has ranks zero and one. This is *actual packet* nonidentifiability, not merely a change in a hidden whole-side kernel.

Make every formerly zero individual weight nonzero, if desired, without changing the prefix. For each original zero-weight stage $j$, give it weight $+1$ and append a late exact copy of its coefficient row with weight $-1$; later copies never refer to earlier copies. All existing rows are unchanged. Every appended stage has the same clock, each tree column, and $TP(c)$ as the stage it copies; this follows from the identical prior-stage coefficients. All outputs therefore stay equal at all orders; no physical stage now has zero individual weight. Because the terminal pair was already individually weighted, it need not be copied. This modification emphasizes the distinction between individual activity and cancellation over equal-stage groups.

Any multi-hole, single-$b$ expression assembled from ordinary $A$, multiplication, fixed polynomial masks and rooted stage expressions expands into a universal finite linear combination of rooted scalar outputs. The coefficient data are identical in the two tableaux, hence its scalar value agrees. If it has a hole filled with $TP(c)$, that value is zero in the first tableau, so it is also zero in the second. In contrast the collision norm from two independently weighted reads is exactly **zero versus $2[y(y-u)P(u)]^2$**. This proves the promised escape is real, and specifies exactly which extra stage incidence it uses. No ordinary rooted decoration is being passed off as independent data.

## Concrete quartic specialization

Use roots $0,1/8,1/4,3/8$, $u=1/2,v=5/8,y=3/4$. The first four physical stages have precisely the four root clocks. Since $P(1/2)=3/512$, the terminal entries are $9/8192$ each and the nonlinear norm changes from 0 to $81/33554432$. The actual $F_0$ loss changes from 1 to 0. A reproducible exact script gives a 157-stage pair at exact order 8 and an 865-stage pair at exact order 20; all individual weights are nonzero. It evaluates every rooted tree through order 8 directly on the smaller pair. For order 20 it checks the panel integration basis exactly through degree 20, the exact moments, all coordinates of $TP(c)$, identical pair structure, and the collision norms; the order-20 all-tree conclusion follows from the proof, not a claimed enumeration. This result concerns the first packet step, not an assertion about the terminal 34-column rank of these particular cancelled pairs.
