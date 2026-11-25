# Weak-four quartic: rule out every exterior secondary clock

2026-11-25. Standalone exact sign class proof on the raw paid packet, using [crossing and brackets](01-crossing.md) and [the first-root count plus parity](02-first-root-count.md); no diagonal or fixed chart/fibre step. Not compiled.

Let $a,c$ be the reverse first and second and $d,h$ the forward first and second, all in the same reflected numerical coordinate. The precedent uniform root-count theorem gives all four simple $Q$ roots $0<r_1<r_2<r_3<r_4<1$, with $d<r_2<r_3<a$. $F=QZ$ is monic degree eight, paid through $wFT$ with $\deg T\le6$, raw degree 15; there is at most one exterior mark. Here orientation can use $w=X$ or $w=1-X$, reflecting and relabeling $(a,c,d,h)\mapsto(1-d,1-h,1-a,1-c)$. The raw local mask laws are the same in either orientation. It suffices to exclude $c=e>1$ in both, because $c<0$ or $h>1$ already violates the sign of the primitive on the wrong-side exterior interval.

The outward masked integral is $\int_a^e X(X-a)Q=0$ by subtracting the first pair. This forces $r_3<a<r_4$. The equal-tail identity $\int_0^d X(1-X)Q=\int_a^1 X(1-X)Q$ forces $r_1<d$: its right side is strictly negative. Indeed subtract $kX(X-a)Q$ on $(a,1)$ with $k=(1-r_4)/(r_4-a)>0$, and subtract the same polynomial from zero on $(1,e)$. On the first interval the ratio $(1-X)/(X-a)-k$ decreases through zero at $r_4$ while $Q$ increases in sign, and the latter interval is strictly negative. Integrate by the positive affine rule and use the zero masked integral. Thus both stops contain exactly three $Q$ roots and the base order is $r_1<d<r_2<r_3<a<r_4$.

## The whole parameter bound and its abstract references

The same outward masked law has just one root $r_4$ in $(a,e)$, so $r_4$ is the weighted mean for the positive density $X(X-a)\prod_{j=1}^3(X-r_j)$. In coordinates $Y=(X-a)/(e-a)$ the density is a positive constant times $Y\prod_{\ell=0}^3(Y+\delta_\ell)$ with every $\delta_\ell>0$. Its ratio to $Y$ increases strictly, so the mean exceeds $2/3$: multiply $Y(Y-2/3)$ by the ratio minus its value at $2/3$ and use the exact affine mesh. Consequently $e<(3r_4-a)/2$.

Let $t_1<\dots<t_7$ be the remaining strict unit roots of $F$. The outer root $r_4=t_7$ because, when inward, $h$ splits its masked right integral and lies in $(r_2,r_4)$, or else $h<r_1$ if outward. Likewise $a\ge t_5$. For $w=X$, broad $L_7,J_7$ envelopes give $r_4<.978,a>.68155$. For $w=1-X$, broad reflected $K_7,J_7$ envelopes give $r_4<.944,a>.600$. In both cases $1<e<1.13$. Thus a tighter **reference** (not a physical fixed fibre) requires only the seven-node tuples of $X(1.13-X)$ and $X(X+.13)$, computed by subtracting a multiple of $J_7$ from $J_8$ to vanish at $1.13$ or $-.13$, dividing out the known linear factor, and comparing increasing density ratios. In the reflected orientation the old low exterior value is $1-e\in(-.13,0)$, so the upper envelope is the reflection of the abstract reference for $X(X+.13)$. Safe simultaneous root lower/upper arrays are
$$
\begin{array}{c|rrrrrrr}
 X,\ \mathrm{lower}&.050&.161&.318&.500&.68155&.838&.949\\
 X,\ \mathrm{upper}&.0520&.1674&.3302&.5181&.7054&.8653&.9717\\
 1-X,\ \mathrm{lower}&.020&.103&.240&.414&.600&.773&.911\\
 1-X,\ \mathrm{upper}&.0208&.1063&.2480&.4265&.6176&.7947&.9315
\end{array}
$$
The exact verifier below checks all new reference signs and moments.

## Three-root stopped reduction by a signed density positive on the affine space

Normalize the left first interval to $Y=X/a$. Let $u=r_1/a$, $u_2=r_2/a,u_3=r_3/a$, $V=r_4/a>1$. The two stopped orthogonalities make $(Y-u_2)(Y-u_3)$ orthogonal to affine polynomials under the **signed** density
$$
 \mu=Y(V-Y)(Y-u).
$$
The form on affine squares is nevertheless positive definite: in all cases $u\le.2$. The reference $Y(1-Y)(Y-.27)$ already has positive-definite affine Gram by the previous count note, and the monotone ratio $(V-Y)/(1-Y)$ shows $\int Y(V-Y)(Y-.27)L^2>0$. Adding the nonnegative $(.27-u)\int Y(V-Y)L^2$ proves the claim. The usual division and affine cardinal squares now earn a positive two-node rule exact through degree three before $\mu$, even though $\mu$ need not be pointwise positive. Every localizer below is raw degree at most 6. This reduction is reusable for a three-root stop whose smallest root is below the first reference Gaussian node of the remaining positive density.

If $h$ is outward, the precise rank row is $h,r_1,d,r_2,r_3,a,r_4$, so $u=t_2/t_6$ and $u_3=t_5/t_6$. If $h$ is inward and $a=t_6$, $r_1=t_1,r_2=t_3$, giving $u=t_1/t_6,u_2=t_3/t_6$. If inward and $a=t_5$, $r_1=t_1,r_3=t_4$, giving $u=t_1/t_5,u_3=t_4/t_5$. Always $V=t_7/a$. The following enclosures and threshold tests are simultaneous in each rank row:
$$
\begin{array}{c|c|c|c|c|c}
 \mathrm{density}&\mathrm{rank\ row}&[u_{\min},u_{\max}]&[V_{\min},V_{\max}]&
   \mathrm{contrary\ upper\ bound}&\mathrm{Gram\ test}\\
 X&\mathrm{out}&[.186,.2]&[1.096,1.16]&u_3<.842&L=Y-.39\\
 X&\mathrm{in},\,a=t_6&[.057,.063]&[1.096,1.16]&u_2<.395&\mathrm{PD}\\
 X&\mathrm{in},\,a=t_5&[.07,.077]&[1.345,1.426]&u_3<.761&L=Y-.25\\
 1-X&\mathrm{out}&[.129,.138]&[1.146,1.206]&u_3<.8&L=Y-.25\\
 1-X&\mathrm{in},\,a=t_6&[.025,.027]&[1.146,1.206]&u_2<.321&\mathrm{PD}\\
 1-X&\mathrm{in},\,a=t_5&[.032,.035]&[1.475,1.553]&u_3<.711&L=Y-.25
\end{array}
$$
At the indicated threshold $s$, entries of $\int\mu(Y)(Y-s)L^2$ are bilinear in $(V,u)$; the form at every point of the closed rectangle is a convex combination of its four corners. The checker verifies strict positivity along the indicated direction at every corner, or positive definiteness (positive leading principal minors) at every corner, as appropriate. A positive direction implies the larger node $u_3>s$. Positive definiteness implies $u_2>s$ as well, because an affine vanishing at the larger node kills its contribution. This contradicts every row.

Thus the full exterior-secondary sign class is impossible under the actual moment payments. Both secondary marks are strict unit; if a sole exterior mark exists it is $a>1$ or $d<0$. The remaining all-interior and exterior-first charts are not closed here.

## Exact fractional checker

Run [`checks/check_exterior_secondary.py`](checks/check_exterior_secondary.py) with `python3`.
