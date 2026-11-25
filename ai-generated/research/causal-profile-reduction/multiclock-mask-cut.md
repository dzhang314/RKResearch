# Several-clock masks: exact remainder obstruction and uniform cut refunds

Let \(K\) be a field and \(\mu(X^j)=1/(j+1)\) on the paid pure moment band. For a nonzero mask \(P\) of degree \(d\ge1\), consider
\[
 G_w(P)=(\mu(PX^{i+j}))_{0\le i,j<w},\qquad w\ge1,\qquad d+2w-1\le p .
\]
A reviewed order-\(p\) tableau supplies these actual paired moments and every unit \(1,\ldots,p\). For the scalar statement alone, it suffices that integers through \(d+2w-1\) are units. No order on \(K\), restriction on weights, or tableau diagonal hypothesis enters this algebra. Over a positive-characteristic field the paid cast assumption is exactly characteristic greater than the budget, with no additional characteristic restriction.

## 1. The exact obstruction is a small remainder system

Write \(h=\lceil d/2\rceil\), \(t=\lfloor d/2\rfloor\), and \(n=w+t\). Let \(L_j\) be the monic pure orthogonal sequence; the last \(L_n\) in the even-\(d\) case is understood as the one-step recurrence polynomial, without demanding its unpaid final test. Put \(A=L_n\) and \(B=L_{n-1}\). They are coprime. The entire silent space
\[
 E=\{F:\deg F<w+d,\ \mu(X^i F)=0,\ 0\le i<w\}
\]
has the concrete direct description
\[
 E=A\,K[X]_{<h}\ \oplus\ B\,K[X]_{<t}. \tag{1}
\]
Here a coefficient band of dimension zero is the zero space.

To check the minimal budget, the ordinary square on degree \(<w\) is invertible by paid Cauchy, so \(\dim E=d\). In the odd case \(d=2t+1\), \(\mu\) pays \(2n\), giving \(A\) orthogonal to degree \(<n\) and \(B\) to degree \(<n-1\). Multiplication by the two band factors in (1) preserves the \(w\) required tests. In the even case \(d=2t\) only \(2n-1\) is available; \(B\) is genuine, and
\[
 A=(X-\tfrac12)B-\beta L_{n-2},\qquad
 \beta=\mu(B^2)/\mu(L_{n-2}^2)\ne0
\]
is silent through degree \(n-2\). For tests of smaller degree both terms vanish; the test at \(n-2\) is exactly the ratio above. Both lower pure norms are nonzero by the ordinary Cauchy form and orthogonality. This also proves coprimality, by going backwards through the consecutive three-term recurrence to \(L_0=1\). The recurrence itself is obtained by expanding \(XL_j\) in the orthogonal basis: symmetry around \(1/2\) fixes its diagonal coefficient and leaves only the lower norm ratio. The largest tests and all denominators are paid. The displayed two bands are disjoint since \(A\mid BV\) implies \(A\mid V\) but \(\deg V<t<n\). Their dimensions sum to \(d\), proving (1).

Define the \(d\)-square linear map
\[
 T_w:(U,V)\longmapsto AU+BV\bmod P,\qquad
 K[X]_{<h}\oplus K[X]_{<t}\longrightarrow K[X]/(P).
\]
Then
\[
 \boxed{\ \operatorname{nullity}G_w(P)=d-\operatorname{rank}T_w\ }. \tag{2}
\]
Indeed multiplication by \(P\) identifies the masked kernel on degree \(<w\) with \(E\cap(P)\); its inverse is exact polynomial division. Formula (2) is valid even for nonsplit or nonsquarefree \(P\). For \(d\) distinct sites \(\xi_i\in K\), the matrix of \(T_w\) may simply have rows
\[
 [\,A(\xi_i),\xi_i A(\xi_i),\ldots,\xi_i^{h-1}A(\xi_i)
   \mid B(\xi_i),\xi_i B(\xi_i),\ldots,\xi_i^{t-1}B(\xi_i)\,] .
\]
Thus full one-charge rank on any chosen width is exactly this remainder/evaluation matrix's nonsingularity. Its size is the number of discarded clocks, not the counted stage dimension.

The rank of the first block is \(\min(h,d-\deg\gcd(A,P))\), and similarly the second is \(\min(t,d-\deg\gcd(B,P))\): the kernel consists exactly of band polynomials divisible by the corresponding \(P/\gcd\). The two gcds are coprime, so their degrees sum to at most \(d\) and one is at most \(t\). At least one block therefore has rank at least \(t\). For every polynomial mask,
\[
 \operatorname{nullity}G_w(P)\le \min(w,h),\qquad
 \operatorname{rank}G_w(P)\ge (w-h)_+. \tag{3}
\]

**Sharpness is at each width separately, not for a common chronology.** Over the reals, every \(L_j\) has simple roots in \((0,1)\) by ordinary positive orthogonality. If \(w\le h\), choose \(P=L_d\); the entire square is zero since \(2w-2<d\). If \(w>h\), in even degree take any \(d\) roots of \(B\), and in odd degree take any \(d\) roots of \(A\). The vanishing block and the remaining rank-\(t\) weighted Vandermonde give equality in (3). These are distinct nonzero sites; no tableau is claimed. The same examples exist over finite *extensions* in every sufficiently large characteristic, by reducing the relevant rational orthogonal polynomial away from its finitely many bad leading-coefficient, discriminant, and constant-term primes, and splitting there. This does not assert sharpness over every fixed finite field. For a small exact witness, \(d=2,w=3\) and \(P=X^2-X+1/10\) divide \(L_3\); the Hankel rows have first two proportional and the last independent (the last pivot comparison differs by \(1/2800\)). Its roots are \((1\pm\sqrt{3/5})/2\), or \(4,8\) in \(\mathbb F_{11}\), and the same rank \(2=w-h\) holds in both fields at paid order \(7\).

## 2. The worst individual widths cannot repeat freely

Now require the same \(d\) distinct sites at every width, with \(P\) their split squarefree product. Call a width **saturated** when the corank is \(h\). There is a field-uniform rigidity statement, stronger than (3):

* If \(d\) is odd, saturation is equivalent to \(P\mid A\). Distinct saturated widths are at least \(d+1\) apart.
* If \(d\) is even, saturation is equivalent to linear dependence of \(\bar A,\bar B\) in \(K[X]/(P)\). Saturated widths form singletons or adjacent pairs; between consecutive clusters the first width of the next is at least \(d\) larger than the last of the previous.

For rigidity, work in the \(d\) site coordinates. A block of band dimension \(b\) spans all coordinate axes of its nonzero support if that support has at most \(b\) sites; if the support has more than \(b\), its image contains no coordinate axis. This is the elementary distinct-root/Vandermonde count. At saturation the total rank is \(t\), and the supports cover all \(d\) sites by coprimality. In the odd case the \(A\)-block has band dimension \(t+1\), so its support has at most \(t\) sites. The \(B\)-block then has at least \(t+1\) sites and rank \(t\); it can contain no coordinate axis of any nonempty \(A\)-support. Hence \(A\) vanishes at all the sites, and conversely. In the even case, if either support has fewer than \(t\) sites it must be empty by this same argument. Otherwise both blocks have rank \(t\) and their images must equal, forcing each support to be all \(d\) sites. The ratio \(A/B\) is then the evaluation of a polynomial \(g\) of degree \(<t\). Multiplying its values by \(X^{t-1}\) must still be the evaluation of a polynomial of degree \(<t\). Since \(\deg(gX^{t-1})<d\), uniqueness of interpolation forces \(g\) constant. Conversely proportional columns, including one zero residue, give the saturated rank.

The spacing follows by propagating the *same* residues by the monic three-term recurrence. Starting from \(\bar L_n=0\), \(\bar L_{n-1}\) is a unit in the split coordinate algebra; later residues are multiples of it by a polynomial of degree \(k-1\) with nonzero leading coefficient at width increment \(k\ge1\). If the new \(L_{n+k}\) vanishes, then \(k-1\ge d\). This is the odd claim. For even degree, if the first dependent pair has \(\bar L_n\ne0\), divide residues by \(\bar L_n\); the reduced sequence starts at \(1\) with its predecessor a scalar, and subsequent multipliers have degrees \(k\) and \(k-1\) at the next pair. A nonzero linear combination cannot vanish modulo degree \(d\) for \(1\le k<d\). If \(\bar L_n=0\), the next pair is automatically dependent, but for \(k\ge2\) the multipliers have degrees \(k-1,k-2\), so a further saturation needs \(k\ge d+1\). Earlier clusters cannot end with this zero-residue case unless at the range boundary: if more widths are available, it initiates the adjacent pair. This proves the stated inter-cluster gap. All recurrences only traverse widths that are themselves paid; the highest polynomial may be the harmless formal recurrence polynomial in the even case.

**Characteristic audit.** This is a degree argument in the original coefficient field, not specialization of a characteristic-zero coprimality or nonconsecutive resultant claim. The ordinary Cauchy bases use natural sums and nonzero differences within the paid range. The largest lower norm needed to form \(L_n\) is paid at \(2n-1\); for even \(d\) no test of \(X^{n-1}L_n\) is used. The consecutive coprimality uses only the nonzero norm ratios, and the spacing only polynomial leading degrees and distinct-site interpolation. In particular common nonconsecutive roots are allowed: the odd-case argument bounds the degree of a shared divisor by the index gap minus one, rather than excluding all such divisors. Avoiding extra discriminant primes is needed only for the optional construction of splitting witnesses in finite extensions, not for any lower bound.

## 3. Both chronological cuts, including a field-uniform improvement

For a discarded physical prefix or individually active suffix covered by these sites, the same actual mixed-diagonal Volterra proof applies. Explicitly, write \(s\) for the number of stages and cut after the first \(k\), \(0\le k\le s\). If every physical clock in the first \(k\) lies in the chosen site set, the bound below is a lower bound on \(s-k\), with \(z\) from the counted suffix's column kernel. If every clock with nonzero individual weight after the first \(k\) lies in the set, the same bound is a lower bound on \(k\), with \(z\) from the counted prefix's weighted-dual step kernel. Either premise stands alone, and the two directions may use different site sets and \(z\). For lower triangular tableaux, the number of zero diagonals **on the counted side only** bounds the corresponding kernel. Set \(m=p-d>0\) and \(w_m(r)=1+\min(r,m-1-r)\). Use the exact width credit \(c_w=w-d+\operatorname{rank}T_w\) from (2) in the shared clipped recursion
\[
 R_0=c_{w_m(0)},\quad R_1=c_{w_m(1)}\ \text{if present},\qquad
 R_{r+2}=c_{w_m(r+2)}+(R_r-z)_+ .
\]
The counted side has at least \(\max_{r<m}R_r\), and independently \(\mathcal B_z(p-2d)\) when the latter effective order is positive. Take the larger. Both proofs only require the counted invariant target, not all nonzero diagonals or nonzero output weights. A physical prefix must still cover every discarded row, even if that row has zero diagonal; an active suffix covers exactly the discarded rows with nonzero individual output weight. If the counted block has no zero diagonal, take \(z=0\) regardless of the discarded block. Since the actual small-width Hankels are principal submatrices of the large ones, \(c_w\) is nondecreasing; the optimized parity-window formula of the single-clock rule works verbatim.

There is also an explicit improvement without inspecting the chosen sites. Put \(u=p-d-2h-2z\). If \(u>0\), let \(a=\lceil u/2\rceil\) and set
\[
 S_d(a)=
 \begin{cases}
  \lceil a/(d+1)\rceil,&d\ \text{odd},\\
  2\lfloor a/(d+1)\rfloor+\min\{2,a\bmod(d+1)\},&d\ \text{even},
 \end{cases}
 \qquad U=a-S_d(a).
\]
These are upper bounds on saturated widths in any \(a\)-interval: in even degree pack clusters of at most two separated by \(d-1\) unoccupied widths. In the central \(u\) grades, the width is \(h+z+w_u(j)\); its credit after subtracting \(z\) is at least \(w_u(j)\), with one extra at each unsaturated occurrence. All these terms are positive, so either whole inner parity window is paid. Adding the two windows counts each width twice except the peak at odd \(u\). The counted physical side therefore also has at least
\[
 \boxed{\ z+\left\lceil
  \frac{\lfloor (u+1)^2/4\rfloor+2U-[u\ \mathrm{odd},\,U>0]}{2}
 \right\rceil.\ } \tag{4}
\]
This bound is a guarantee, not a claimed optimum for a common set of clocks. The domain of (4) is exactly the guard \(u>0\) with \(p,d,z\) integral, \(d\ge1\), \(z\ge0\), and the same split distinct-site cover at every width. When \(u\le0\) do not apply (4); the guarded old cutoff and the exact per-width rule remain separately available. In particular for **even \(d\) and even \(p\)** (4) is exactly the coarse floor plus \(a-S_d(a)\); this is strictly stronger whenever \(p\ge2d+2z+6\). The argument is shared by both chronological directions and makes no assumption on the signs or positions of the distinct sites or on the discarded diagonal.

Representative pure arithmetic comparisons with the previous mixed nodal cutoff \(\mathcal B_z(p-2d)\):

| \(p\) | \(d\) | counted \(z\) | \(u\) | Previous | Joint (4) |
|---:|---:|---:|---:|---:|---:|
| 8 | 2 | 0 | 4 | 3 | 3 |
| 10 | 2 | 0 | 6 | 6 | 7 |
| 12 | 2 | 1 | 6 | 7 | 8 |
| 14 | 3 | 0 | 7 | 10 | 11 |
| 20 | 4 | 0 | 12 | 21 | 24 |
| 20 | 4 | 2 | 8 | 12 | 14 |

These are **conditional counted-side** inequalities, not new unrestricted stage floors, tableau examples, or data about any fixed candidate. In each row the discarded side must have the specified distinct-site cover and the counted side the given nullity bound.

## 4. A full one-charge certificate when there are ordered exterior sites

Over an arbitrary ordered field, for sites \(\xi\le0\) write each factor as \(X+(-\xi)\), and for sites \(\xi\ge1\) use \((1-X)+(\xi-1)\), absorbing a nonzero overall sign. Their product is a nonzero nonnegative combination of \(X^a(1-X)^t\). Each such paid Jacobi Hankel is positive definite: the adjacent-row determinant recursion gives strictly positive leading minors, and algebraic elimination completes squares over any ordered field. Thus the exterior product has full rank at every ordinary one-charge width, without any positive tableau-weight premise.

More generally let \(e\) discarded sites be exterior (including endpoints) and \(i\) be strictly interior. Multiply the exterior product by the square of the product of the interior factors. Its Hankel is also positive definite: apply the exterior quadratic form to the nonzero interior product times the test polynomial, at exactly the higher paid width. Thus the two cuts get the full \(\mathcal B_z(p-e-2i)\) when this effective order is positive. Each exterior site costs once, each interior site twice. Within a method that demands a one-sign real mask this degree is minimal, because each interior real zero must have even multiplicity. Arbitrary sites can still give full rank more cheaply, precisely when the paid remainder tests in (2) permit it. No extra characteristic or ordering assumption is silently attached to (1)–(4); ordering is only needed for this last positivity substitute.

## 5. If the permitted sites can be selected, full one-charge is generic

For a positive \(p-d\), let \(N=\lfloor (p-d+1)/2\rfloor\). For each paid width \(w\le N\), the determinant of \(G_w(\prod_i(X-\xi_i))\) is a polynomial in the site parameters, nonzero because its value at \(\xi_1=\cdots=\xi_d=0\) is the paid shifted Cauchy determinant for \(X^d\). Multiplying their product by \(\prod_i\xi_i\prod_{i<j}(\xi_i-\xi_j)\) gives a nonzero polynomial of degree at most \(d+N(N+1)/2\) in each parameter. Thus any infinite paid field has a nonempty open set of distinct nonzero choices with full one-charge rank throughout. In a finite paid field, the same statement holds from any permitted set with more than \(d+N(N+1)/2\) elements, or after a large enough finite extension. The finite assertion is just the repeated fact that a nonzero univariate polynomial has at most its degree many roots, applied one coordinate at a time while preserving a nonzero coefficient of the remaining polynomial. This selects valid scalar masks, not realizable tableaux. Prescribed smaller sets still require the exact remainder check or the robust floor.
