# Formation and chronological prefix rank for common-diagonal RK tails

There are two independent conclusions here. First, a clock-localized, output-visible rooted direction cannot form earlier than the middle of the paid tree degrees. Second, shelling such directions off the last physical rows gives simultaneous weighted outputs on a shorter real prefix, and an explicit rank inequality even when the entire rooted space is not clock-invariant. The sharper cutoff in the second conclusion uses the [mixed-word proof](COMMON-DIAGONAL.md), with the [resonance extension](COMMON-DIAGONAL-RESONANCE.md) handling the remaining nonendpoint case. A cutoff one row longer is established here from the pure words alone.

## Setting

Let \(\mathbb K\) be a field and let \(A,\mathbf b\) be an ordinary order-\(p\) lower-triangular Runge–Kutta tableau on \(s\) stages over \(\mathbb K\). The order equations make \(1,\ldots,p\) units. Set
\[
\mathbf c\coloneqq A\mathbf1,\qquad
C\coloneqq\operatorname{diag}(\mathbf c),\qquad
L\coloneqq p-1-d
\]
for \(0\le d<p\). Write \(E_j\) for the actual span of the Butcher weight vectors \(\boldsymbol\Phi_t(A)\) for \(|t|\le j+1\). Write \(F_j\) for the numerical vectors represented by formal combinations at these grades whose exact polynomial is zero. The exact polynomial of an individual term \(\boldsymbol\Phi_t(A)\) is \(|t|X^{|t|-1}/t!\). In particular
\[
 E_j=F_j+\{P(\mathbf c):\deg P\le j\}.
\]
This uses the bushy trees for the monomials. A chosen formal expression suffices in all arguments; no uniqueness beyond the paid range is assumed.

For each actual clock \(\theta\), let \(E_d(\theta)\) consist of those vectors of \(E_d\) supported only at entries with \(c_i=\theta\). Define
\[
 V\coloneqq\bigoplus_\theta E_d(\theta),\qquad
 \zeta_j\coloneqq\dim E_j-\dim(E_j\cap V) \quad (0\le j\le d).
\]
Thus \(V\) is the largest \(C\)-invariant subspace of \(E_d\): on any invariant subspace, polynomial interpolation in the diagonal operator splits each vector into its physical clock components.

## Independent formation obstruction

Suppose \(\boldsymbol\eta\in E_d(\theta)\) and \(\mathbf b\cdot\boldsymbol\eta\ne0\). Choose an exact polynomial \(P\) for one representation of \(\boldsymbol\eta\); \(\deg P\le d\). For every \(R\) with \(\deg R\le L\) the order equations give
\[
 \int_0^1 P(X)R(X)\,dX
   =\mathbf b\cdot R(C)\boldsymbol\eta
   =(\mathbf b\cdot\boldsymbol\eta)R(\theta).
\tag{1}
\]
The integral denotes its formal polynomial value in \(\mathbb K\). In particular \(P\ne0\). Taking \(R=(X-\theta)S\) gives
\[
\int_0^1 (X-\theta)P(X)S(X)\,dX=0\qquad(\deg S\le L-1).
\tag{2}
\]
If \(L\ge d+2\), the Hilbert matrix on the powers through degree \(d+1\) in (2) is invertible, forcing \((X-\theta)P=0\). This is impossible. Thus
\[
 L\le d+1,\qquad d\ge \left\lceil\frac{p-2}{2}\right\rceil .
\tag{3}
\]
For the Hilbert assertion, \((1/(a+b+1))_{0\le a,b<r}\) has a Cauchy determinant with unit numerators and paid denominators through \(2r-1\). Equivalently, a kernel combination of \(1/(X+b+1)\) has a numerator of degree at most \(r-1\) vanishing at \(0,\ldots,r-1\); at \(X=-b-1\) it forces the corresponding coefficient to vanish. No positivity is used.

At the even midpoint \(p=2d+2\), define \(\Pi_{d+1}\) to be the monic polynomial of degree \(d+1\) orthogonal on \([0,1]\) to all degrees at most \(d\). The same invertible matrix gives its existence and uniqueness. By (2), \((X-\theta)P\) is a nonzero scalar multiple of \(\Pi_{d+1}\). Thus \(\theta\) is a Gaussian node, and \(P\) is the corresponding normalized cardinal polynomial up to a scalar. Neither 0 nor 1 is possible. If 0 were a root, division by \(X\) would give a nonzero vector in the kernel of the shifted Hilbert matrix \(1/(a+b+2)\) through degree \(d\), paid through \(2d+2\); reflection gives the same conclusion for 1.

In particular, below (3), the output is zero on the whole of \(V\). Since \(\mathbf b\cdot\mathbf1=1\) and \(\mathbf1\in E_d\), \(E_d\) cannot be \(C\)-invariant there. This rules out invoking local tail bounds on visible directions in an early clock-invariant space, without any diagonal restriction or numerical bound. At the even midpoint, if every physical clock indicator is in \(E_d\) (in particular if \(E_d\) is invariant), every nonzero aggregate weight occurs at a root of \(\Pi_{d+1}\). There must be at least \(d+1\) such weights by the rank of the ordinary quadrature Hankel matrix, so the contributing clocks are exactly the \(d+1\) distinct Gaussian nodes. Extra physical clocks with zero aggregate weight are not excluded.

## Exact weighted outputs on a prefix

Let \(t\) be the last physical index with \(b_t\ne0\), and suppose \(A_{ii}=\gamma\ne0\) for all \(h\le i\le t\), where \(1\le h\le t\). No assumption is made about the earlier diagonal. For each clock define the unscaled moments
\[
 \Lambda_r(\theta)\coloneqq
 \sum_{a=0}^r \binom ra (-\gamma)^{r-a}\frac{(1-\theta)^a}{a!}
 \qquad(0\le r\le L).
\]
For \(\boldsymbol\eta\in E_d(\theta)\), the same polynomial adjoint used in (1) gives
\[
 \mathbf b\cdot(A-\gamma I)^r\boldsymbol\eta
   = \Lambda_r(\theta)\,(\mathbf b\cdot\boldsymbol\eta).
\tag{4}
\]
In particular \(\Lambda_r(1)=(-\gamma)^r\); the endpoint has a nonzero causal path now, unlike a strict explicit tableau. If \(L\ge1\) the top two moments cannot both vanish. Indeed their binomial translation satisfies
\[
 (n+1)\Lambda_{n+1}
 +\bigl((2n+1)\gamma-(1-\theta)\bigr)\Lambda_n
 +n\gamma^2\Lambda_{n-1}=0 \quad(0\le n<L),
\]
with no final term at \(n=0\). This follows from the finite exponential generating series of \((1-\theta)^a/a!\) by multiplying by \(e^{-\gamma u}\), or directly from the binomial formula. Paid nonzero \(n\gamma^2\) descends a consecutive pair to \(\Lambda_0=0\), a contradiction.

If the first nonzero entry of \(\boldsymbol\eta\) is at \(\ell\ge h\) and the output is nonzero, the strict causal path in (4) needs at least \(L\) later rows when \(\Lambda_L\ne0\) and at least \(L-1\) otherwise. This argument itself is independent of the new mixed-word proof. For \(L\ge4\) that proof improves the uniform requirement to \(L\), and for \(L\ge6\) the resonance extension improves it to \(L+1\) at every \(\theta\ne1\), whether or not \(\Lambda_L(\theta)\) vanishes. On the observed suffix the strict part is literal; weights later than \(t\) are zero and prior inputs before \(\ell\) are zero.

Use any of the resulting verified lower bounds \(r_\theta\) for the required later rows and define the cutoffs
\[
 k_\theta\coloneqq\max(h-1,t-r_\theta),\qquad
 k\coloneqq\max_\theta k_\theta .
\tag{5}
\]
A local vector vanishing through \(k_\theta\) cannot have nonzero output: its first possible nonzero index is at least \(h\) and leaves fewer than \(r_\theta\) later rows. Consequently the local output factors through restriction to physical rows at clock \(\theta\) of index at most \(k_\theta\). Extend these linear functionals on the numerical restriction images and sum them, obtaining one row \(\mathbf b'\) supported through \(k\) such that
\[
 \mathbf b'\cdot f(C)\boldsymbol\eta
   =\mathbf b\cdot f(C)\boldsymbol\eta
 \qquad(\boldsymbol\eta\in V)
\tag{6}
\]
for every polynomial \(f\). The support of each summand is only at its own clock. This is ordinary finite-dimensional factorization, not the inference that any original weight was zero.

For each \(0\le m\le L\), set \(q_m(X)\coloneqq(1-X)^m/m!\). The exact adjoint identity on \(E_d\) gives
\[
 ((A^\mathsf T)^m\mathbf b)\cdot\boldsymbol\eta
    =\mathbf b\cdot q_m(C)\boldsymbol\eta\qquad(\boldsymbol\eta\in E_d).
\]
Hence the single prefix row in (6) simultaneously realizes all these weighted outputs on \(V\), including \(m=0\). In particular if \(V=E_d\), the actual leading \(k\) by \(k\) tableau, with weights \(\mathbf b'\), is an ordinary order-\(d+1\) tableau and has every paid Beta-weighted model through that same tree size. Lower triangularity preserves its Butcher weight vectors under restriction.

The pure-word cutoff from (4) is \(k_0=\max(h-1,t-L+1)\) for \(L\ge1\); at \(L=0\) it is \(t\). The mixed-word proof gives the uniform cutoff \(k_+=\max(h-1,t-L)\) for \(L\ge4\). For \(L\ge6\), every clock other than 1 uses \(k_-=\max(h-1,t-L-1)\) by the resonance extension. If \(k_+>k_-\), just one actual row is gained, and it can be needed by only the clock at that row. Removing it changes the simultaneous vectors of moments by one scalar read times \((q_m(c_{k_+}))_{m=0}^L\). If the row has clock 1, all the positive shifts already ignore it. Multiple Beta shifts do not themselves buy another physical row: their last nonzero index is still \(t\) because \(b_t\gamma^m\ne0\), and using the tail theorem with the shifted output consumes \(m\) of the budget. The useful feature is that (6) pays their outputs jointly, at the original cutoff.

## Prefix rank with a quantified failure of invariance

Let \(E_j^k,F_j^k\) be the actual degree-\(j\) spaces on the leading \(k\) rows, i.e. the restrictions of \(E_j,F_j\). Let \(A_k,C_k\) denote these leading matrices and define
\[
 D_k\coloneqq C_k A_k-A_k C_k-A_k^2,\qquad
 \kappa_j\coloneqq\dim(E_j^k\cap\ker D_k).
\]
For negative \(j\) put \(E_j^k=0,\ \kappa_j=0\). If the prefix has only nonzero diagonals, \(D_k\) is invertible by triangularity and all \(\kappa_j=0\). In general \(\kappa_j\) is at most the number of zero diagonals there, and a known smaller kernel intersection can be used directly.

For every \(0\le j\le d\), the scalar model dimension in the actual prefix satisfies
\[
 \dim(E_j^k/F_j^k)\ge
 \max(0,\min(j+1,L+1)-\zeta_j).
\tag{7}
\]
To prove this, compare the full Beta moment map on \(E_j\) with the simultaneous prefix map from (6). Their error vanishes on \(E_j\cap V\), so its image has dimension at most \(\zeta_j\). If \(P(\mathbf c)\) restricts into \(F_j^k\), choose an actual \(\mathbf f\in F_j\) with that restriction. The vector \(P(\mathbf c)-\mathbf f\) has zero restriction, and its full Beta output is the vector
\[
 \left(\int_0^1 q_m(X)P(X)\,dX\right)_{m=0}^L .
\]
Thus the polynomial kernel of the map into \(E_j^k/F_j^k\) has its moment image inside the error image. The moment map on degree at most \(j\) has rank \(\min(j+1,L+1)\): the first \(r=\min(j+1,L+1)\) weights span all polynomials through degree \(r-1\), and their pairing with the first \(r\) monomials is the ordinary invertible Hilbert block. Its payment \(2r-1\le j+L+1\le p\) is available. This proves (7). In fact one may use the dimension of the full Beta moment image of the zero-restriction subspace when known, instead of \(\zeta_j\).

The polynomial identity \(XJ_0-J_0X-J_0^2=0\) gives \(D_k E_{j-2}^k\subseteq F_j^k\). The image dimension is \(\dim E_{j-2}^k-\kappa_{j-2}\). With (7), and nesting when the net increment is negative, this proves the numerical rank inequality
\[
 k\ \ge\ \dim E_d^k\
 \ge\sum_{\substack{0\le j\le d\\ j\equiv d\pmod2}}
        \max\bigl(0,\min(j+1,L+1)-\zeta_j-\kappa_{j-2}\bigr).
\tag{8}
\]
The loss from a nonconstant early block is confined to its actual commutator kernel. If the sum in (8) exceeds \(h-1\), a cutoff \(k=\max(h-1,t-r)\) forces \(t\) to be at least \(r\) plus that sum. There is no stage conclusion from using \(h-1\) alone.

For strict SDIRK with invariant \(E_d\), the sum is \(\sum_{j\equiv d\bmod2}\min(j+1,L+1)\). When \(L\ge d\) this is \(\lfloor(d+2)^2/4\rfloor\), giving
\[
s\ge L+\left\lfloor\frac{(d+2)^2}{4}\right\rfloor
\]
from the uniform mixed-word cutoff (one less from the uniform pure cutoff). If every output-visible clock is nonexceptional and \(L\ge6\) the mixed-word cutoff adds one. These are conditional rank and chronology statements, not improvements to the current unrestricted strict-SDIRK table. For example at even order \(p=2r\) and its first possible local degree \(d=r-1\), the prefix floor is at most \(r+\lfloor(r+1)^2/4\rfloor+1\), below the existing nonsingular bound \(r(r+1)/2\) for \(r\ge6\). Their use is to rule out a proposed early clock chart or its insufficient prefix, including charts with a measurable nonlocal complement. They do not license adding an independent reverse rank count to the same rows.

## The even midpoint cannot consist only of resonant clocks

Suppose \(p=2r\), \(d=r-1\), so \(L=r\), and suppose there are \(r\) output-visible local clocks (for example if all physical indicators are in \(E_d\)). By (2) these are exactly the Gaussian nodes. For the reflected variable \(Y=1-\theta\), the monic resonance polynomial is
\[
 S_r(Y)\coloneqq
 r!\sum_{a=0}^r\binom ra(-\gamma)^{r-a}\frac{Y^a}{a!}.
\]
Its two next coefficients are \(-r^2\gamma\) and \(r^2(r-1)^2\gamma^2/2\). The monic shifted Legendre polynomial has the corresponding coefficients \(-r/2\) and \(r(r-1)^2/(4(2r-1))\). These follow by differentiating \(Y^r(Y-1)^r\) exactly \(r\) times and dividing by its resulting leading coefficient; the derivative is orthogonal by formal integration by parts. Reflection preserves the monic Gaussian root set. If all nodes were resonant, the two monic polynomials would coincide. The first coefficient forces \(\gamma=1/(2r)\). At that value the difference in the second is \((r-1)^2/(8(2r-1))\ne0\) for \(r\ge2\). Thus at least one output-visible clock is nonresonant. Moreover all are nonresonant whenever \(\gamma\) avoids the finite set of scalar roots of \(S_r\) at these fixed algebraic nodes, for example for a common diagonal transcendental over the prime field.

These conclusions need neither positivity assumptions on the weights nor reality of the field, only the stated payment. The even-midpoint coefficient argument and the formation barrier are independent of the mixed-word tail proof.
