# The odd-midpoint clock action on the exact model

Let \(p=2d+1\) over a coefficient field paid through \(p!\), with degree \(d\) meaning rooted size through \(d+1\). Use \(E=E_d\), \(F=F_d\), and the polynomial model in which polynomial evaluations are independent modulo the pure space
\[
 \sigma:E\longrightarrow K[X]_{\le d},\qquad
 \ker\sigma=F,\qquad \sigma(P(\mathbf c))=P.
\]
This separation follows from the literal origin and the paid weight-\(X\) moment Gram. Put \(Q=X\pi_d\), where \(\pi_d\) is the monic degree-\(d\) polynomial orthogonal to lower degrees for weight \(X\). This \(Q\) is defined from scalar moments, whether or not its numerical evaluation is yet a pure vector.

The polynomial \(Q\) has distinct roots in a splitting field, includes zero, and has no root 1. Endpoint payment follows by dividing a putative \(\pi_d\) endpoint factor and testing the paid square Gram for \(X^2\) or \(X(1-X)\) on degree \(d-1\). For simplicity away from the endpoints, the formal self-adjoint operator
\[
 {\cal L}\pi=X(1-X)\pi''+(2-3X)\pi'
\]
for weight \(X\) gives \({\cal L}\pi_d+d(d+2)\pi_d=0\). Indeed its leading coefficient at that degree is \(-d(d+2)\), and the remaining polynomial of degree at most \(d-1\) is orthogonal to all lower degrees by integration by parts with the boundary factor \(X^2(1-X)\). Those integrals have degree at most \(2d\), so the Gram is paid. A multiple root away from both endpoints contradicts the lowest-order derivative term of the differential equation. These scalar facts are valid without real-number order.

We use the algebra \(K[X]/(Q)\), identified with polynomials of degree at most \(d\). Whenever \(v,Cv\in E\) one has the exact identity
\[
                  \sigma(Cv)= X\,\sigma(v)\pmod Q .
 \tag{1}
\]
To see this, the two sides have zero constant at the literal origin, since \(C\) vanishes there and \(Q(0)=0\). Their ordinary moments against \(X^j,\ 0\le j\le d-1\), are equal: the order conditions give \(b C^j Cv=b C^{j+1}v\), and subtracting a scalar multiple of \(Q\) does not affect those moments. The difference, divided by \(X\), is killed by the paid weight-\(X\) Gram. This proves (1). In particular the map extends consistently to \(E+CE\) by \(\widehat\sigma(u+Cv)=\sigma(u)+X\sigma(v)\bmod Q\); any ambiguity is precisely covered by (1).

If \(U\subset E\) is any actual clock-invariant subspace, its model image is an invariant subspace for multiplication by \(X\) modulo \(Q\). On the actual clock block \(U_\theta\), a nonzero model must be an eigenvector at \(\theta\); hence \(\theta\) is a root of \(Q\). Over the splitting field, \(\sigma(U)\) is exactly the polynomials whose values vanish at the complement of that subset of roots. This also shows \(U\cap F\) is clock-invariant. A model-bearing clock-local vector can never have zero output: if \(\sigma(u)\ne0\) on one root, its output is that model value times the corresponding nonzero scalar Radau weight. Those weights exist by interpolation at the \(d+1\) roots, are exact through degree \(2d\) by division by \(Q\), and are all nonzero by the paid ordinary Gram. This identifies the visible invariant core without claiming that all of \(E\) is invariant.

## Effective single-clock output, not only physical support

The paid causal tail theorem actually does not require \(C\eta=\theta\eta\) once its normalized pure and mixed scalar responses are already known. In its proof, the formulas
\[
 C\eta_i=i\eta_{i+1}+x_i u_i,\qquad i\ge1
\]
use only the single-clock-factor moments on the shifted vectors \(A^i\eta\); the proof of the jump identity never uses \(i=0\). If \(x_1=x_2=0\), take the two-dimensional invariant quotient of the suffix starting at \(\eta_1\) by the suffix starting at \(\eta_3\). It is a nonzero nilpotent block since \(C\eta_1=\eta_2\) there, regardless of the first physical clock \(x_0\). The terminal block is unchanged. Thus a numerical vector with the same paid scalar responses as a nonzero point output at \(\theta\ne1\) obeys the same causal cutoff, even if its physical support has several clocks.

In particular at the odd midpoint, let \(R_\theta\) be the unique polynomial of degree at most \(d\) with \(\int P R_\theta=P(\theta)\) for all \(\deg P\le d\), by the paid ordinary Gram. If \(\sigma(v)\) is a nonzero multiple of \(R_\theta\), then all adjoint words of remaining cost at most \(d\) are point responses. Such a vector cannot vanish on the early prefix of length \(k=s-p+d\) when \(d\ge5\). At a Radau root \(\theta\), the reproducer is the Lagrange cardinal at \(\theta\) divided by its nonzero quadrature weight. This is because that quadrature is exact through degree \(2d\). Every single nonzero Radau model atom is therefore excluded from the actual late-model image
\[
    \sigma\bigl(E\cap\ker(\text{first }k\text{ physical reads})\bigr).
\]
This image is precisely the model-alias space on that early prefix, by restriction of numerical pure combinations. The criterion does not automatically exclude mixtures of several atoms.

## Exact one-head criterion and its limitation

Suppose \(\dim(E+CE)=\dim E+1\). Then \(E=U+wP_{<h}(\mathbf c)\), a direct sum, with \(U\) the largest invariant subspace in \(E\) and \(h\ge1\). For completeness, consider the decreasing subspaces of \(E\) of vectors whose first \(j\) consecutive clock powers remain in \(E\). Each step drops dimension at most one: the next power's obstruction is measured by the one-dimensional first-step quotient. A step of zero drop is already invariant, so the chain thereafter is constant. Choose \(w\) at the deepest nonconstant step. Its successive powers through the last allowed one are independent modulo \(U\): from a relation take its highest power and advance just enough to put it outside the first-step kernel whereas all lower powers remain inside. The number of powers is the codimension of \(U\), giving the stated form. Its effective head-clock count is at least \(h+1\).

Choose \(w\) to project to zero on earliest coordinate pivots of \(U\) within each clock block. This is a chronological normalization, not a purity assumption. If a vector \(u+wP(\mathbf c)\) vanishes on the first \(k\) rows, then so does \(u\): the earlier selected pivots read \(u\) alone, and all earlier \(U\)-values are already determined by those pivots. Its model is zero because \(U\) decomposes by clocks, all its model-bearing clocks are nonendpoint Radau roots, and the paid local cutoff kills the output on each late component. Thus the late model comes entirely from the normalized head.

Let \(S\) be the distinct labels where the normalized head has a nonzero entry within the first \(k\) rows, let \(a=|S|\), and suppose \(a<h\). Put \(H=\prod_{x\in S}(X-x)\) and \(r=h-a\). If \(a\ge h\) there is no late head contribution. When \(a<h\), (1) shows the late model is exactly the family
\[
                \alpha(x)H(x)T(x)\quad\text{on the roots of }Q,
                \qquad \alpha=\sigma(w),\quad \deg T<r .
\]
Let \(S_*\) be the subset of Radau roots where \(\alpha H\) is nonzero. If \(0<|S_*|\le r\), interpolation in \(T\) isolates a single nonzero Radau atom, impossible by the effective point cutoff. So a genuine tableau has \(S_*=\varnothing\) or \(|S_*|>r\). In the former case all the early Beta outputs factor. In the latter, a particular weighted row factors precisely when its corresponding scalar weighted moments of this displayed family vanish. Thus the missing hypothesis is an exact actual late moment condition, not a guess that the clock closure has already occurred.

If \(h\le d\), the head projection of \(\mathbf1\) is zero: its polynomial would have to carry all its first \(d\) powers in degree \(<h\), on at least \(h+1\) effective labels, which forces it to vanish by successive degree comparisons. Thus \(1\in U\) and the invariant core has all model polynomials. Even so, choosing a globally pure head generator first and then interpolating away its values at arbitrary \(U\)-pivots need not keep it pure. The separate countermodel demonstrates this limitation; no claim that small \(h\) by itself forces early factorization is made. One sufficient, measurable hypothesis is that the chronological interpolant into \(U\) is pure for a pure generator, equivalently that the resulting normalized head has zero model. The delayed closure and actual unary rent in the companion file can provide a different, genuinely rooted route.
