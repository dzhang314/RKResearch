# First-provider width and saturated residues in a one-head explicit flag

Let \(K\) be a field, with every integer required by the stated rooted degree budgets invertible. Degree is tree size minus one. Put \(\mathbf c\coloneqq A\mathbf1\) for a strictly lower triangular tableau and let \(C\) be multiplication by its clock vector. Write \(E_j\) for the actual rooted derivative span through degree \(j\), and \(F_j\) for the numerical image of combinations with zero exact stage polynomial. Assume actual model separation
\[
E_j=P_{\le j}(\mathbf c)\oplus F_j.
\]
Unary extension acts on the model by the primitive \(J\coloneqq I_0^X\); multiplication by \(C\) acts by multiplication by \(X\).

Suppose an actual flag has one head, generated at degree \(a\):
\[
F_{a+k}= U\oplus f\,P_{\le k}(\mathbf c),\qquad 0\le k\le j-a,
\]
where \(f\in F_a\) and \(U\) is \(C\)-invariant. Assume \(U\) is also invariant under coordinatewise multiplication \(D_f\) by \(f\), and that the actual complementary head profile is a polynomial \(P(X)\) of degree \(d\le a\): on a complement invariant under \(C,D_f\), the projection \(\bar f\) obeys \(D_f\bar f=P(C)\bar f\). These latter two conditions follow from the previous one-head multiplier argument if \(j\ge2a\) and the endpoint remains noninvariant, with at least \(j-a+2\) effective clock labels.

## Physical compression and the two kinds of read

Chronologically compress on \(E_j\) using independent physical evaluations, redirecting each omitted coefficient only to earlier retained evaluations as in [the clock-invariant rank argument](INVARIANT-DEFECT-HERMITE-PROVIDER-RENT.md). All rooted data through degree \(j\), their ranks, the flag, the invariances and the head relation are preserved. No higher rooted data or old output are needed. The resulting strict triangular tableau has full raw coordinate span \(E_j\).

In each joint \((c,f)\) block choose the earliest coordinate pivots of its part of \(U\). At a nonpivot \(i\), subtract the evaluation on those earlier pivots that agrees with the \(i\)-th read on \(U\), giving a row \(\lambda_i\). This row kills \(U\) and is supported in its own joint block, never after \(i\). Its row sum cannot vanish: it would then kill all model evaluations and all \(f\,P_{\le j-a}(\mathbf c)\), hence all the full coordinate space. Normalize it to have row sum one. Its action on \(f\) is \(f_i\). The head profile then says \(f_i=P(c_i)\) if \(f_i\ne0\). Thus the nonpivot reads, all independent along with the core pivot coordinate rows, have these two forms:
\[
\begin{array}{lll}
\text{clean:}&V(c_i),& f_i=0,\\
\text{head:}&V(c_i)+P(c_i)T(c_i),&P(c_i)\ne0,
\end{array}
\]
on the numerical vector with model \(V\), head polynomial \(T\), and arbitrary core contribution. Within either type every label is distinct (repeated reads would be identical on all of \(E_j\)). A head at clock zero is allowed and is not the clean origin. The literal origin is a clean nonpivot.

There are at least \(j-a+1\) clean labels. Otherwise take a nonzero \(T\) of degree at most \(j-a\) vanishing at all clean labels. The expression with model \(-PT\) and head \(T\) would have all nonpivot reads zero, hence would be in \(U\); separation rules that out. Write \(g\) for the number of clean labels.

At a nonzero clean read \(\lambda_i\) with clock \(x=c_i\), the row \(\lambda_i A\) is supported strictly before \(i\), annihilates \(F_{j-1}\), and is \(I_0^x\) on models through degree \(j-1\). Truncating to that actual prefix and dividing both its matrix and the output row by \(x\) therefore gives an ordinary order-\(j\) explicit method. In particular any stage floor or pure-rank floor for ordinary order \(j\) applies to this prefix. The Hermite argument from the invariant endpoint lemma applies to the first \(M\) nonzero **clean** reads without needing invariance of all \(F_j\). If \(d_j\) is a valid ordinary provider lower bound on \(\dim F_{j-1}\), then for \(M\le\min(\lfloor j/2\rfloor,g-1)\) the compressed tableau has width
\[
 n\ge d_j+M+g.
\]
Here there are \(2M\) independent prefix Hermite rows annihilating \(F_{j-1}\), then the \(M\)-th completion and the remaining \(g-1-M\) completions. No terminal resource or output row was silently assumed.

## Width of the first actual clean provider

Suppose \(P\) is nonconstant and \(a+2\le j\). Let \(i_1\) be the first nonzero clean read, and suppose there is one. Before \(i_1\) let \(x_1,\ldots,x_h\) be its head labels in chronological order, and let \(u\coloneqq\dim U\). The first provider has at most
\[
u+d+3
\]
physical rows. More precisely \(h\le d+2\), and if equality holds then all these preceding head labels are roots of a single, nonzero degree-\((d+2)\) polynomial described next.

For each \(k\ge1\) with \(a+k+1\le j\), put
\[
\mathbf z_k\coloneqq C^k\bigl(P(\mathbf c)-f\bigr).
\]
Choose \(\mathbf u_k\in U\) agreeing with \(\mathbf z_k\) at the core pivots (the pivot coordinate map is an isomorphism on \(U\)). Then \(\mathbf z_k-\mathbf u_k\) is zero *as an actual numerical vector* at every physical coordinate before \(i_1\). Indeed its head reads agree there by definition of the two profiles, its origin read vanishes because \(k\ge1\), and its pivot reads vanish, so the triangular row transform proves the assertion on the original coordinates.

It follows by strict chronology that \(\lambda_i A(\mathbf z_k-\mathbf u_k)=0\) at every head before \(i_1\) and at the first clean provider. This rooted expression has model \(J(X^kP)\) and pure part in \(F_{a+k+1}\), so every preceding head label is a root of a single polynomial
\[
B_k(X)\coloneqq J(X^kP)(X)+P(X)S_k(X),
\qquad \deg S_k\le k+1.
\]
The clean read also gives \(J(X^kP)(c_{i_1})=0\). In particular \(P\) cannot be a monomial, because its \(X\)-weighted primitive at that nonzero clock would then be nonzero. Consequently \(B_1\) cannot be zero as a polynomial. Otherwise \(P\mid J(XP)\). Over an algebraic closure write \(r_0\) for the order of \(P\) at zero. The primitive has order \(r_0+2\) at zero, and at each nonzero root of \(P\) its order would be one larger than that of \(P\), since its derivative is \(XP\). Since \(P\) is not a monomial there is at least one such root, giving more than \(d+2\) roots counted with multiplicity. The degree of the primitive is \(d+2\), which is impossible. The differentiations and multiplicity comparisons use only the indicated paid degrees.

Thus \(h\le\deg B_1\le d+2\). There is one prior clean origin, at most \(u\) core pivots, and \(h\) prior distinct head reads; this gives the row bound on the actual first provider. When \(h=d+2\), \(B_1\) has exactly those simple roots and divides every later available \(B_k\). In the polynomial quotient by \(P\), there is consequently the reusable necessary condition
\[
J(X^kP)\equiv R_{k-1}J(XP)\pmod{P},\qquad
\deg R_{k-1}\le k-1.
\]
The result is a strict separation between a long noninvariant profile and the usual invariant rank rent: many early head nodes are impossible unless low weighted primitives share the same filtered divided-difference quotient. It applies at general \(a,d,j\) and uses no enumeration of rooted shapes, preselected node values, or fixed stage chart.
