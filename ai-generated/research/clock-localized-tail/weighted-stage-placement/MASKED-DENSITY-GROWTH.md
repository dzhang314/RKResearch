# A full-tail rigidity bound from actual output clock labels

Let \(A\) be a lower triangular RK tableau of ordinary order \(p\) over a field in which \(p!\) is a unit. Its actual clock is \(\mathbf c\coloneqq A\mathbf1\), and \(Y\coloneqq I-\operatorname{diag}(\mathbf c)\). Fix a nonempty literal leading prefix and an actual suffix \(S\) of \(L\) rows. Write \(T\coloneqq A_{S,S}\) and \(\boldsymbol\beta\coloneqq\mathbf b|_S\). The suffix clock labels are inherited from the whole matrix. An output-visible label is a value \(y_i=1-c_i\) at a physical suffix row with \(\beta_i\ne0\). Let \(q\) count the distinct visible labels, and let \(\epsilon\) be one if zero is visible and zero otherwise. Thus \(q\) can be smaller than the number of physical clock groups; equal labels separated by other stages are counted once. The case \(q=0\) means \(\boldsymbol\beta=0\), so every paid row functional already has a row on the prefix.

For nonzero \(q\), define the actual mask and the zero-origin primitive by
\[
   \chi(y)\coloneqq\prod_{\alpha\ {\rm visible}}(y-\alpha),
       \qquad (JS)(y)\coloneqq\int_0^y S(z)\,dz .
\]
The row \(\mathbf b\chi(Y)\) is literally supported before the suffix. With \(j\) a tree degree and \(r\coloneqq p-1-j\), if \(r\ge q\) it is exact through \(E_j\) for the scalar functional
\[
                  S\longmapsto\int_0^1 \chi(1-x)S(x)\,dx .
\]
More generally call the first polynomial under the integral the density. Right multiplication of an actual exact row by \(Y\) multiplies its density by \(y=1-x\); right multiplication by \(A\) takes its density to \(J\) of that density, by polynomial integration by parts. Each costs one extra rooted degree. These operations never reintroduce a suffix coefficient after the mask: earlier physical rows do not read any later stage.

## One dimension of missing density is recovered per paid extension

Here is a scalar lemma which also applies to a measured space of several actual exact densities, not just the one mask. Suppose \(V\subseteq K[y]_{\le n}\) is a nonzero subspace, contains a polynomial of degree \(n\), and contains a polynomial with nonzero constant term. For an integer \(e\ge0\), define the weighted primitive
\[
                  J_eP\coloneqq y^{-e}J(y^eP).
\]
The denominator here means the exact polynomial quotient, since the primitive has a factor \(y^{e+1}\). Assume the factorials through \(n+e+1\) are paid. If \(V\ne K[y]_{\le n}\), then
\[
                    \dim(V+yV+J_eV)\ge\dim V+2 .                  \tag{1}
\]
Indeed multiplication by \(y\) adds at least one dimension, by the highest degree. If it only adds one, put \(d=\dim V\) and \(H_i=\{P:y^aP\in V,\ 0\le a\le i\}\). Multiplication by \(y\) injects \(H_i/H_{i+1}\) into \(H_{i-1}/H_i\). The first drop is one, and a nonzero plateau would be invariant under multiplication by \(y\), impossible in finite degree. Thus there is a nonzero \(P\in H_{d-1}\), and \(P,yP,\ldots,y^{d-1}P\) form a basis of \(V\). Here \(P(0)\ne0\) and \(P\) is nonconstant, since \(V\) is not the full polynomial space. The primitive \(J_eP\) cannot be in \(V+yV\), whose members are multiples of \(P\). Otherwise degree and constant term force \(J_eP=\alpha yP\), and the leading coefficient gives \(\alpha=1/(\deg P+e+1)\), while the coefficient of \(y\) gives \(\alpha=1/(e+1)\), a contradiction. This proves (1). If \(V\) is already full, adding \(yV\) makes the next polynomial space full.

Apply this after dividing the initial density \(\chi\) by \(y^\epsilon\). After \(k\) paid extensions from budget \(q\), all densities still have that factor, and their deficiency relative to \(y^\epsilon K[y]_{\le q+k-\epsilon}\) falls by at least one per extension until zero. Consequently at every budget \(r\ge q\) there is a literal-prefix exact density subspace of codimension at most
\[
                     \max(\epsilon,2q-r)
                       \quad\text{in }K[y]_{\le r}.                \tag{2}
\]
In particular it is full at \(r=2q\) when no endpoint is visible, and contains every positive density at \(r=2q-1\) when an endpoint is visible. No hypothesis about cross-clock coupling inside the suffix is needed. If several measured densities are already paid at some budget, let \(n+e\) be their actual largest degree and \(e\) their common minimum vanishing degree. Apply (1) to their **span**, after division by \(y^e\); its actual initial deficiency replaces \(q-\epsilon\). Overlapping densities must not be counted independently. A degree lower than the number of paid word letters is harmless, but may not be charged as if the row had been available earlier.

The rank-growth estimate is sharp for a single mask as an abstract density calculation. Over a field with all \(q\) distinct roots of \(y^q-1\), take \(\chi=y^q-1\). Up to \(k<q\) extensions, its exact generated density span is the span of \(\chi\) and the monomials \(y,\ldots,y^k,y^{q+1},\ldots,y^{q+k}\). At each positive length one can separate the two exponents by \(Y\) versus \(A\); neither operator produces a third exponent from a single one. This has dimension \(2k+1\), exactly the lower rate in (1). The roots can be literal suffix clock labels over an algebraic field; this control does not assert that an ordinary RK method has only these exact prefix reads.

## Width and gap: no visible endpoint needed for the clean formula

Let \(a_j\coloneqq\min(j+1,r+1)\), the exact rank of the full paid scalar moment family at degree \(j\). Restricting to a density subspace of codimension \(c\) loses at most \(\min(a_j,c)\) scalar ranks by the paid factorial Vandermonde test. If \(\epsilon=0\), (2), with the trivial bound for \(r<q\), therefore gives the scalar debit
\[
                 d_r\le\min(a_{p-1-r},\,r+1,\,(2q-r)_+).
\]
For \(r=0,\ldots,2q-1\) the last two terms give the symmetric list \(1,2,\ldots,q,q,\ldots,2,1\). Either parity sum is \(q(q+1)/2\). On a nonsingular leading prefix the actual commutator is invertible. The prefix recurrence in the maximizing whole-tableau parity, followed by adding its disjoint \(L\) suffix rows, gives
\[
 \boxed{\qquad s\ge Q(p)+L-\frac{q(q+1)}2,\qquad
  Q(p)\coloneqq\left\lceil\frac{\lfloor(p+1)^2/4\rfloor}{2}\right\rceil .
        \qquad}                                                    \tag{3}
\]
The finite-budget sum of the actual debits is the sharper statement. A mixed leading diagonal requires the separate prefix kernel losses from TELESCOPING-CUT-NULLITY.md. The value of \(q\) in (3) uses original nonzero suffix weights, not all occupied clocks or all nonzero edges. In particular a single visible nonendpoint label gives the \(L-1\) bonus even if the suffix contains other clocks and genuine cross-clock links.

If zero is visible, once the positive density space has been paid the only remaining loss is the ordinary output. At a given budget it is recovered, for example, if \(\boldsymbol\beta\) lies in the span of the suffix traces of the paid positive functionals. Explicitly, subtract the corresponding zero-model differences between the original positive reads and their physically supported prefix representatives from \(\mathbf b\). That kills its suffix and preserves the scalar density \(1\). If the full positive family \(1,\ldots,r\) has descended and right multiplication by \(T\) is invertible on the row orbit of \(\boldsymbol\beta\), its dimension \(h\) suffices: \(\boldsymbol\beta T,\ldots,\boldsymbol\beta T^h\) span that orbit. Invertibility holds on all nonsingular triangular suffixes. Even without this orbit cancellation, if \(r\ge j+1\) the positive densities alone span the scalar dual at degree \(j\), so the remaining ordinary density does not cost rank there. This recovers the endpoint rank criterion for \(q=1\), and supplies its exact generalization to arbitrary physically interleaved visible clocks. In particular, with an invertible suffix output orbit of dimension \(h\), the additional debit beyond the triangular sum in (3) need only count the even budgets \(r\) with \(2q\le r<h\) and \(2r\le p-1\). At other budgets above the triangle either the ordinary read is recovered by the true orbit or the positive densities already span the needed scalar dual. Thus if \(h\le2q\), (3) holds even with a visible endpoint.

All conclusions apply to an actual cut; neither distinct clock count nor conditional suffix structure has been inferred for every minimizing method. No unrestricted stage table changes.
