# Delayed clock closure: an actual early output or a new late unary direction

Use ordinary order \(p\) and tree degree \(d=|t|-1\). In an explicit tableau, \(E_d\) is the numerical rooted span through size \(d+1\) and \(F_d\) the span of differences of normalized Butcher weight vectors of the same degree. The coefficient field is paid through \(p!\). Denote the clock diagonal by \(C\), and let \(Y\coloneqqI-C\), \(L\coloneqqp-1-d\) and \(k\coloneqqs-p+d\). The [localized tail theorem](README.md) gives the following cutoff: on any numerical direction in \(E_j\) supported at a single clock other than 1, a nonzero original output forces that direction's first physical position to be at most \(s-p+j\), if \(p-1-j\ge5\). No first reverse equality is assumed.

Let \(W\) be the clock-invariant span of \(E_d\), meaning the span of all its actual images under powers of \(C\). Suppose \(W\subset E_{d+\delta}\) for an integer \(\delta\ge1\), with \(L-\delta\ge5\). Define the actual late kernel
\[
       K_d^{\rm late}\coloneqq\{v\in E_d:v_i=0\text{ for every }i\le k\}.
\]
For \(v\) in it, let \(v_\theta\) be its spectral projection at clock \(\theta\). These are numerical vectors in \(W\subset E_{d+\delta}\), still zero through the cutoff \(k\). If \(\theta\ne1\) and \(b v_\theta\ne0\), the universal causal cutoff forces its first physical nonzero entry into the interval \(k+1,\ldots,k+\delta\). Since distinct clock components have disjoint physical supports, at most \(\delta\) different nonendpoint clocks can have nonzero output on \(v\).

Suppose some \(v\in K_d^{\rm late}\) has \(q>0\) nonendpoint charged clocks and \(L-\delta\ge q\). Write their actual charges as \(\alpha_\theta=b v_\theta\); all are nonzero. The paid adjoint identity gives, for \(\delta\le j\le\delta+q-1\),
\[
             bY A^j v
               =\frac{b Y^{j+1}v}{(j+1)!}
               =\frac{\sum_{\theta\ne1}\alpha_\theta(1-\theta)^{j+1}}{(j+1)!}.
\]
Indeed the repeated upper primitive of \(1-X\) is \((1-X)^{j+1}/(j+1)!\); the word cost \(j+1\) is within \(L\). At least one of these \(q\) responses is nonzero by Vandermonde on the distinct nonzero \(1-\theta\). But for any such \(j\), the actual vector \(A^j v\) vanishes through row \(k+\delta\) by strict chronology. If it were in \(W\), each local component would be an actual level-\((d+\delta)\) direction first seen too late for nonendpoint output. Thus \(bY A^j v\) would vanish. Therefore there is a genuine late rooted direction
\[
                     A^jv\in E_{d+j}\setminus W,
                \qquad \delta\le j\le \delta+q-1,
\]
witnessed by its nonzero paid output. This is a rank increment outside the complete clock closure, not a count inferred from formal names.

Consequently, if \(L\ge\max(\delta+5,2\delta)\), either all the weighted rows \(b Y^m\), \(1\le m\le L\), factor through the first \(k\) physical reads on \(E_d\), or there is such an additional late unary direction by degree \(d+2\delta-1\). Indeed, if the late kernel has no nonendpoint charges, its \(bY^m\) responses all vanish, which is exactly the factorization criterion. If \(A\) preserves \(W\), or merely sends its vectors zero through row \(k\) back into \(W\), the second alternative is impossible. The resulting early cutoff has no \(\delta\) loss.

A single collection of early rows can be used for simultaneous weighted outputs even if \(E_d\) is not clock-invariant. In the first alternative, for each nonendpoint \(\theta\) the functional \(v\mapsto b v_\theta\) on \(E_d\) kills the late kernel, so it factors through early reads; this does not in general place those reads at the same clock. To get a genuine weighted prefix one may use a **separate** early row \(\beta_m'\) for each exact \(b A^m=bY^m/m!\) restricted to \(E_d\). The tableaus are the same actual strict prefix, with this family of output rows. No common factorization \(\beta_m'=b'Y^m/m!\) is necessary or asserted in the noninvariant case.

## Turning simultaneous Beta outputs into a numerical odd-order floor

Suppose these separate early outputs exist. Strict truncation preserves all rooted data through size \(d+1\). At shift \(m\) the moment functional is \(\int(1-X)^mP(X)\,dX/m!\). Thus:
1. A polynomial alias \(P\) on the actual prefix satisfies \(P(0)=0\) and \(\int (1-X)^m P(X)=0\) for \(1\le m\le L\). The weight-\(X(1-X)\) Gram on \(P/X\) gives full separation through degree \(d\) if \(L\ge d\).
2. One can make a genuine **ordinary** exact prefix output through rooted size \(r+1\), where \(r=\min(d,L-1)\). Choose a polynomial \(S\) of degree at most \(r\) by the nonsingular weight-\((1-X)\) Gram so \(\int(1-X)S(X)P(X)=\int P(X)\) for every \(\deg P\le r\). Express \((1-X)S\) in powers \((1-X)^m\) for \(1\le m\le r+1\) and take that linear combination of the actual \(\beta_m'\), multiplying by the respective \(m!\). This uses each exact moment on its actual data, with all factorials through \(p!\).

At \(p=2d+1\), \(d\ge6\), one has \(L=d\). The second point gives an ordinary order-\(d\) prefix. The audited ordinary size-six pure rank and strict growth imply its \(\dim F_{d-1}^{\rm pre}\ge d-1\). Its actual Beta shift-one output is exact through size \(d+1\), so growth continues strictly to degree \(d\): \(\dim F_d^{\rm pre}\ge d\). In detail, if a pure plateau \(F_{j+1}=F_j\) held with \(j\ge2\), then \(A,C\) preserve that pure span. In the quotient, choose earliest coordinate pivots of \(F_j\) within clock blocks. This gives the quotient a physical triangular coordinate frame, with induced \(A\) still strict and \(C\) diagonal. The degree-two relation becomes \(A\bar c=C\bar c/2\) and \(\bar c=C\bar{\mathbf1}\). At the first nonzero coordinate of \(\bar c\), the left side is zero by strictness whereas the clock factor on the right cannot be zero, a contradiction. Hence \(c\in F_j\), incompatible with the Beta exact nonzero first clock moment. This proves the needed last strict step without assuming a size-six theorem on weighted outputs.

Combining the full early separation and pure rank gives \(k\ge 2d+1\), hence
\[
                            s\ge p+d+1 .
\]
For example, early factorization would give 20, 23 and 26 at paid odd orders 13, 15 and 17. These are conditional unless the structural alternative is ruled out by some separate rank constraint.

A particularly sharp split is the one-step closure \(W=E_d+CE_d\) with \(W\) itself clock-invariant. Write \(f=\dim F_d\), \(e=\dim W-\dim E_d\), and let \(\epsilon=1_{bA-bY\ne0}\). If \(e=0\), the original invariant cutoff already gives the early weights. If \(e>0\), the delayed-closure argument with \(\delta=1\) says either early factorization holds or there is a genuine new late \(Av\) outside \(W\). The latter alternative gives \(\dim E_{d+1}\ge \dim E_d+e+1\); the usual paid reverse rank at that degree, of length \(d-2\), yields
\[
               s\ge p-1+f+e+\epsilon .
\]
At a proposed \(s=p+d\), the audited ordinary rank gives \(f\ge d\), and early factorization is impossible by the preceding numerical bound. The only possibility in this one-step-closure profile is therefore \(e=1,f=d,\epsilon=0\), with one real late \(A\)-direction outside \(W\). Larger one-step clock growth already violates the physical stage budget. This does not say that the clock closure must occur in one step for all stage-tight tableaux.

The conclusions are source arguments over paid fields. A ring application's clock and pure rank hypotheses must be verified after specialization; no Lean acceptance or unrestricted odd-order stage table is claimed.
