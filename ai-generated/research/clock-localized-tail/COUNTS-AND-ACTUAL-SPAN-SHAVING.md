# Exact even and odd families, and a sharper actual-residual test

The paired construction above is strictly smaller than the fixed-frame collocation unrolling, and than the sharp strictly adjacent, terminal-output width in its nonexceptional sign regimes, at sufficiently large order. It is not a change to the unrestricted stage table through order twenty. It permits older output weights and skip edges; it therefore does not challenge that adjacent width theorem.

## 1. Two order families on a minimal scalar grid

Take \(q=\lceil p/2\rceil\), \(m=q\) and \(p\ge3\). A thin decoder through grade \(q-1\) needs \(q(q-1)/2\) rows. To construct it directly, use \(j\) distinct sites at level \(j=1,\ldots,q-1\), with the only first clock \(\gamma\). Strict feeds apply \(J_\gamma\) to the previous cardinal interpolant and evaluate at the sites. All actual row sums are the proposed clocks after adding \(\gamma\). At each level \(j\) its interpolant is the shifted formal polynomial through size \(j\): every child fits the previous grade, and the raw product has degree at most \(j-1\). Interpolation fixes it. Expanding the opposite diagonal shift proves that this is also a decoder for the ordinary exact-flow profiles through size \(q-1\).

- For \(p=2q\), use the \(q\)-node Gauss rule. If \(P_q\) is its monic nodal polynomial, quadrature vanishes on \(P_q^2\), whose integral is positive. Thus the order is exactly \(2q\). The paired method has \(r=q\) added correction levels and total **\(q(q+1)\)**, rather than \((3q^2+q)/2\) at the full owner widths. It saves \(q(q-1)/2\) physical rows.
- For \(p=2q-1\), one may use the \(q\)-node right-Radau rule. Its \(q-1\) internal nodes are the roots of the monic degree-\(q-1\) polynomial \(P\) orthogonal for weight \(1-X\). Division by \((X-1)P\) gives precision \(2q-2\), while \((1-X)P^2\) has degree \(2q-1\), zero quadrature and positive integral. The paired method has \(r=q-1\) and total **\(q^2\)**, rather than \((3q^2-q)/2\), saving \(q(q-1)/2\) physical rows. All correction clocks can be taken from the internal sites: no additional endpoint row is needed in this construction. The ordinary endpoint mass remains at the base layer. This is compatible with the independent late-endpoint counterfamily: it does not claim endpoint aliasing on that counterfamily's fixed terminal prefix or deny its sharp delay.

Real-algebraicity of both rules follows from the rational Gram systems for their node polynomials. Orthogonality with a positive interior measure forces distinct interior roots by multiplying by the product of only the interior sign-changing linear factors. The usual division by the node polynomial then gives the asserted precision. Each later signed pair uses only arithmetic in the field of the prefix, clocks, weights and \(\gamma\). The prefix's free thin sites may be rational even when \(\gamma\) is irrational.

## 2. A sharper all-order real-algebraic stage estimate

The verified dense Laguerre construction in `DENSE-POLYNOMIAL-DONOR-MINIMUM.md` supplies the required \(s_F=\lfloor m^2/4\rfloor\) donor for every nonzero real-algebraic \(\gamma\). In the notation of that proof, its common-diagonal clock polynomial is
\[
 W_j\coloneqq j!J_\gamma^j1,
\]
with real algebraic simple roots; its cached chart through grade \(m-1\) is a linear decoder of the indicated polynomial degree. Substitute this same donor, without changing any prefix row, into (1). For
\[
 q\coloneqq\max(\lceil p/2\rceil,m-1),
\]
the count is
\[
 \left\lfloor\frac{m^2}{4}\right\rfloor
 +\max(\lceil p/2\rceil,m-1)
 +\frac{(p-m)(p-m+1)}2.                                      \tag{9}
\]
For \(q=p/2\) the Gauss rule above gives exactness. For \(p<2q\), let \(P_j\) denote the monic shifted Legendre polynomials and use the nodal polynomial \(P_q+\varepsilon P_{p-q}\) for sufficiently small nonzero rational \(\varepsilon\). It retains distinct interior roots by separation and sign brackets (and positive cardinal weights by continuity from Gauss), is orthogonal to degrees at most \(p-1-q\), and has a nonzero pairing with \(P_{p-q}\). Therefore the interpolatory rule integrates through \(p-1\) and fails at degree \(p\). This gives exact order at every prescribed nonzero diagonal, not only outside the zeros of a shifted tall moment.

Taking \(m=\lceil2p/3\rceil\) in (9) gives \(p^2/6+O(p)\). Minimizing the displayed elementary count gives 75 at \(p=19\) (\(m=12\) or \(13\)) and 82 at \(p=20\) (\(m=13\)). The older sign-regime adjacent counts there are respectively 120 and 130; the sharper unrestricted real-algebraic witnesses in the published table are respectively 54 and 59. No improvement to those unrestricted entries is claimed. No asymptotic priority relative to other unrestricted families is claimed either.

A rational version uses the thin prefix and \(q=p-1\). Choose a monic polynomial \(P\) with \(q-1\) distinct negative rational roots, and use the additional rational root \(a=\ell(XP)/\ell(P)\), in \((0,1)\). The nodal polynomial \((X-a)P\) has zero integral, whereas \(X(X-a)P\) has integral \(\ell((X-a)^2P)>0\). Thus the rule is exact through degree \(p-1\) and first fails at degree \(p\). At any prescribed nonzero rational diagonal, with \(m=\lceil p/2\rceil\), the count is \(m^2+2m-1\) at even \(p=2m\), and \(m^2+m-2\) at odd \(p=2m-1\). These rational counts only improve the older generic prescribed-diagonal quadratic recipe, not the specialized rational succession through twenty.

## 3. What a genuine one-mode first excess buys

This part changes the donor hypothesis, and **not** the count (9). Suppose its first excess is known on actual order-\(m\) trees, namely
\[
 G_t-D\boldsymbol{\Phi}_t(B_F)=\alpha_t W_{m-1}
                      \qquad(|t|=m).                         \tag{10}
\]
The thin prefix from §1 with its layer-\(j\) nodal polynomial \(W_j\) has this property. For the first excess at a layer, either every child fits the preceding exact cap, or the root is unary; in the latter case \(J_\gamma W_{j-1}=W_j/j\) vanishes at the layer's nodes. Thus the only polynomial interpolation loss is in the line of \(W_j\). The cached Laguerre prefix also has (10), **provided its cache is paid through grade \(m\)** and stopped before its layer \(m\). The band at layer \(m-1\) in that proof has the single possible grade \(m-1\) when \(|t|=m\). Expanding the diagonal shift contracts to smaller trees, which are exactly decoded; hence the band assertion stays true for the shifted profiles. Its actual row count is \(L(m)-1\), with \(L(n)=\lfloor(n+1)^2/4\rfloor\), not \(L(m-1)\).

This extra charge is necessary if one wants the entire polynomial first excess to be one fixed line. Indeed the highest coefficient of every \(G_t\) at size \(m\) is the nonzero ordinary leading coefficient \(|t|/t!\); a one-line error for a codomain of degree at most \(m-2\) is therefore an exact decoder of the quotient by one fixed monic degree-\(m-1\) polynomial, through size \(m\). The weighted target version of the invertible commutator lower bound in `DENSE-POLYNOMIAL-DONOR-MINIMUM.md`, with \(q=m\) and this quotient projection, charges \(m-1\) for its first target and all the full ranks \(m-2,m-4,\ldots\) thereafter. This is exactly \(L(m)-1\). The lower bound is for the **polynomial** line hypothesis, not for a line seen only after projecting to owner measurements. In particular a cache paid only through \(m-1\) cannot be silently used to assert (10).

Let \(i\) be a correction layer, and let \(k\coloneqq r-i\) be its remaining test degree. For \(k\ge1\), suppose there are \(k\) distinct earlier stage clocks that can serve as the minus rows. To serve, their literal strict primitive must be correct for the small children of size at most \(k\), as is true at any of the base owners. An arbitrary earlier row is also sufficient when \(k=1\), since the only small child then is the leaf, whose primitive is exactly its true clock minus \(\gamma\). Let \(H_k\) be the monic polynomial with those \(k\) roots. If
\[
                         \ell(H_k W_{p-1-k})=0,               \tag{11}
\]
then those \(k\) clocks suffice instead of \(k+1\). Give each added plus row the strict row of its own earlier minus and the now shorter correction based on the \(k\)-site cardinal basis. Subtract its weight from that same earlier row. The defining difference recurrence uses only identical baseline feeds and exact small factors, so it also holds for these older non-owner baselines.

To prove (11) suffices, apply the exact criterion (8). With \(k\) sites the tap formula pays the remainder of \(g\) modulo \(H_k\). The discarded part is zero whenever \(|u|>m+i-1\), because then \(\deg g\le k-1\). At the one exceptional size \(|u|=m+i-1\), the active branch leading to its first-excess source must be purely unary; otherwise the size would exceed that threshold. Since \(\mathbf V_0\) is exact at size \(m\), its difference at size \(m\) is precisely \(\alpha_t E W_{m-1}\) by (10). Thus \(M\boldsymbol\Delta_{i-1}(u)\) is a scalar multiple of \(M^i E W_{m-1}\). Move the \(i\) primitives to the test using (2), with the degree allowance decreasing by one on the child side at each step. The final degrees still sum to at most \(p-1\), so quadrature then gives the true integral. Moving the primitives back in the integral gives
\[
 \widehat{\mathbf b}\cdot
   \bigl(H_k(\mathbf x)\odot M^i E W_{m-1}\bigr)
       =\ell(H_k J_\gamma^i W_{m-1})
       =\frac{(m-1)!}{(p-1-k)!}\ell(H_k W_{p-1-k}) .         \tag{12}
\]
Consequently the only discarded term is harmless. If other layers meet their corresponding gate, the changes can be made together: each prior layer still supplies every paid pairing (7). This does not assert existence of a simultaneous system of clock hulls. In particular using a new clock that has no valid earlier minus might cost an extra row and lose the saving.

### Explicit two-to-one at the penultimate correction

If \(r\ge2\), the penultimate correction has \(k=1\). When \(\ell W_{p-2}\ne0\), its two tests require only the one clock
\[
                    a\coloneqq\frac{\ell(XW_{p-2})}{\ell W_{p-2}}.
\]
This can be an existing clock without prescribing it on the scalar quadrature. For every \(p\ge4\) there is a positive algebraic \(\gamma\) with \(a=\gamma\), the true first clock of the prefix. Put \(n=p-2\) and let \(L_n^{(\alpha)}\) denote the usual Laguerre polynomials. From the finite coefficient formula,
\[
 W_n(X)=(-\gamma)^n n!L_n^{(0)}(X/\gamma),\quad
 \int_0^z L_n^{(0)}(u)\,du=\frac{z L_n^{(1)}(z)}{n+1},\quad
 \int_0^z u L_n^{(1)}(u)\,du=\frac{z^2L_n^{(2)}(z)}{n+2}.
\]
As a result the condition \(\ell((X-\gamma)W_n)=0\) is, at \(z=1/\gamma>0\),
\[
 0=\int_0^z(u-1)L_n^{(0)}(u)\,du
       =\frac{(z-1)zL_n^{(1)}(z)}{n+1}
        -\frac{z^2L_n^{(2)}(z)}{(n+1)(n+2)}.                  \tag{13}
\]
The derivative of \(z^2 L_n^{(2)}(z)\) is \((n+2)z L_n^{(1)}(z)\). The \(n\) distinct positive roots of \(L_n^{(2)}\) are supplied by its positive orthogonality; together with the root at zero, Rolle's theorem and the degree put the roots of \(L_n^{(1)}\) strictly between successive distinct roots of \(z^2 L_n^{(2)}\). Thus \(L_n^{(2)}\) has opposite signs at the first two roots of \(L_n^{(1)}\). The right side of (13) has a root strictly between them. It is algebraic and does not vanish on \(L_n^{(1)}\), so \(\ell W_n\ne0\). This pays (11) at the first physical clock and saves one row compared with the unshaved construction for the **same paid donor**. It does not save a row beyond the minimal-donor count (9) in general.

### Last correction at an exceptional diagonal

When \(r\ge1\), the final correction only contributes on size \(p\), and only after a unary chain of length \(r\) from a size-\(m\) source. Under (10), (12) with \(k=0\) says that its scalar is a multiple of \(\ell W_{p-1}\). If that value is zero, the entire last receiver and its paired output may be omitted. This is the same shifted tall scalar appearing in the adjacent exceptional construction, now proved sufficient at this specific projected layer, not inferred from the tall tree alone. No simultaneous omission of both late layers is asserted.
