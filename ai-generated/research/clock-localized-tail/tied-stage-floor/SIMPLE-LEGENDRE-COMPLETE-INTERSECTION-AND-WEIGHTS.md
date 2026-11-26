# The nowhere-zero branch is a simple Legendre complete intersection

Work over characteristic zero, with a real or ordered field where positivity is used. The starting hypothesis is an ordinary order-\(p\) nonsingular lower triangular RK tableau of the exact quadratic-floor stage count. Use either even \(p=2m\), \(m\ge2\), and define \(n\coloneqq m+1\), or tied odd \(p=2m-1\), \(m\ge2\) even, and define \(n\coloneqq m\). Thus \(s=mn/2\); both original parity sums are saturated. Write
\[
 \mathbf c\coloneqq A\mathbf1,\qquad
 \mathbf g\coloneqq A\mathbf c-\tfrac12\mathbf c^{\odot2},\qquad
 G\coloneqq\operatorname{diag}(\mathbf g).
\]
Through this note assume every \(g_i\ne0\). The established saturation identities are \(F_{j+2}=ME_j\) and, by pure diagonal multiplication and invertibility of \(G\), \(F_{j+2}=GE_j\); thus the actual \(E_j\) consists of evaluations at the literal pairs \((c_i,g_i)\) of polynomials of weighted degree at most \(j\). The coordinate weights are one for \(x\) and two for \(z\). In particular \(E_{p-2}\) is full and the pairs are distinct. Repeated clock labels by themselves are allowed.

## The two equations and their exact multiplicities

Let \(L_\ell\) be the monic shifted Legendre polynomial of degree \(\ell\) for formal integration over \([0,1]\). For example it is the unique monic degree-\(\ell\) polynomial orthogonal to all lower degrees under the rational moment form. Consecutive such polynomials are coprime: their monic three-term recurrence has nonzero coefficient on \(L_{\ell-1}\), as follows from the nonzero norm ratio, so a common root would descend to \(L_0=1\).

For degree \(j\) let \(\mathcal O_j\) denote the scalar polynomials of degree at most \(j\) orthogonal to all degrees at most \(p-1-j\). The kernel of the evaluation map into \(E_j/F_j\) is exactly \(\mathcal O_j\): ordinary mixed moments give one inclusion, and both have dimension \(j+1-\min(j+1,p-j)\). Therefore \(L_m(\mathbf c)\in GE_{m-2}\), and \(L_{m-1}(\mathbf c)\in GE_{n-2}\). There are actual pair-vanishing polynomials
\[
 U(x,z)=L_m(x)-zU_0(x,z),\qquad
 V(x,z)=L_{m-1}(x)-zV_0(x,z)
\]
of weighted degrees \(m\) and \(n\), respectively. The first weight is exactly \(m\) because of its trace. The second cannot have weight less than \(n\): in the even case the only scalar trace at grade \(m\) is a multiple of \(L_m\); in the odd case grade \(m-1\) has zero scalar kernel. These polynomials are unique with their indicated traces at the indicated grades: a difference of zero trace would be \(z\) times a polynomial vanishing at all pairs of grade at most \(n-2\), and that grade has no relations by the low-degree saturated Hilbert dimensions.

Substitute \(z=t^2\). The ordinary polynomials \(U(x,t^2)\) and \(V(x,t^2)\) have degrees \(m,n\) and share no nonconstant factor, even over an algebraic closure. In fact any such factor has a nonzero constant restriction to \(t=0\), as it divides both consecutive \(L\)'s there. If it had positive total degree, the remaining factor of \(U(x,t^2)\) would already need degree at least \(m\) to restrict to a nonzero constant multiple of \(L_m\), contradicting additivity of degree. Each of the \(s\) distinct physical pairs gives two distinct affine intersections with \(t^2=g_i\). They exhaust the projective Bézout product \(mn=2s\). Thus there are no other intersections, no intersection at infinity, and all these points are simple. In particular the weighted leading forms of \(U,V\) are coprime, the physical pairs are their whole affine zero set, and the actual two-coordinate derivatives
\[
 J_i\coloneqq U_x(c_i,g_i)V_z(c_i,g_i)-U_z(c_i,g_i)V_x(c_i,g_i)
\]
are nonzero. The last assertion also follows directly from the weight argument below. The even-weight leading form in the even-order degree pair must have a nonzero pure highest \(z\)-power: otherwise \((x:t)=(0:1)\) would be common at infinity. In the odd-order degree pair at least one of the two degree-\(m\) leading forms has this coefficient nonzero.

## The individual weights are exact Jacobian reciprocals

Fix a physical pair \((c_i,g_i)\). For \(H=U,V\) define the two polynomial divided differences
\[
 H_{x,i}(x,z)\coloneqq\frac{H(x,z)-H(c_i,z)}{x-c_i},
 \qquad
 H_{z,i}(z)\coloneqq\frac{H(c_i,z)-H(c_i,g_i)}{z-g_i}.
\]
Define \(D_i\coloneqq U_{x,i}V_{z,i}-V_{x,i}U_{z,i}\). Its weighted degree is at most \(m+n-3=p-2\), and it is \(J_i\) at its own pair and zero at every other one. Indeed at another pair the two-by-two matrix of divided differences kills the nonzero coordinate difference; at its own pair it is the derivative matrix. Its trace on \(z=0\) is
\[
 D_i(x,0)=-\frac{1}{g_i}
 \frac{L_m(x)L_{m-1}(c_i)-L_{m-1}(x)L_m(c_i)}{x-c_i}.
\]
The integral of the displayed difference quotient is \(H_{m-1}\coloneqq\int_0^1 L_{m-1}(x)^2\,dx\). For completeness, the monic recurrence telescopes after multiplication by \(L_j(c_i)/H_j\), giving the quotient as \(H_{m-1}\sum_{j=0}^{m-1}L_j(x)L_j(c_i)/H_j\); only \(j=0\) survives integration. Ordinary order applies to \(D_i\) as a genuine polynomial in the clock and pure quadratic residual. Hence
\[
             \boxed{\ b_i g_i J_i=-H_{m-1}.\ }                    \tag{1}
\]
In particular all \(b_i\ne0\), and over an ordered field the literal sign of \(b_i g_i\) is the opposite of the sign of \(J_i\). This is a per-stage condition, not an aggregate of clock fibres.

## Conversely, the equations and weights pay every polynomial moment

Start instead with two real polynomials of the indicated weights and traces, with coprime weighted leading forms and \(s\) distinct real simple common pairs of nonzero second coordinate. Define the weights by (1). Then
\[
          \sum_i b_i f(c_i,g_i)=\int_0^1 f(x,0)\,dx
          \qquad (\deg_{\rm w}f\le p-1).                         \tag{2}
\]
Here is a finite algebraic proof with no general residue theorem. Write \(N_j\) for the dimension of the weight-at-most-\(j\) polynomials, zero when \(j<0\). The only syzygies between the coprime equations are \(UR+VS=0\) with \(R=VQ,S=-UQ\). Thus the quotient by their products of weight at most \(j\) has dimension \(N_j-N_{j-m}-N_{j-n}+N_{j-m-n}\). For sufficiently large \(j\) this is \(mn/2\): the cumulative generating series is \((1-t^m)(1-t^n)/((1-t)^2(1-t^2))\), which is a polynomial divided by \(1-t\) because at least one degree is even; the numerator evaluates to \(mn/2\) at \(t=1\). The divided-difference separators already make evaluation onto the \(s\) pairs surjective at grade \(p-2\), so every vanishing polynomial is in the ideal \((U,V)\). Moreover a relation of weight at most \(j\) can be represented with \(\deg_{\rm w}R\le j-m,\deg_{\rm w}S\le j-n\). If the initially chosen products exceed that weight, their top terms cancel; coprimeness of the leading forms lets one subtract a multiple of \((V,-U)\) to lower both top weights. Iteration gives the asserted filtered representation.

Apply this to \(f-\sum_i f(c_i,g_i)D_i/J_i\), a vanishing polynomial of weight at most \(p-1\). The trace integral of its \(UR+VS\) representation is zero, because the trace multiplier degrees are at most \(m-1,m-2\) in the even case and at most \(m-2,m-2\) in the odd case. Use the computed integral of \(D_i\) to obtain (2). This also proves (2) for a candidate data set before any tableau is constructed.

For later primitive compatibility, the trace map of the weight-at-most-\(j\) vanishing ideal is exactly \(\mathcal O_j\) for \(j\le p-1\). In the affected grades \(j\ge m\), its traces are the sums \(L_m R+L_{m-1}S\) with degrees \(j-m,j-n\) respectively. No nonzero combination of these vanishes, by coprimeness and the degree bounds, and the dimension is \(j+1-\min(j+1,p-j)\). Below \(m\) both spaces are zero. This gives the exactness of the scalar trace quotient even for high grades where a stage vector has several polynomial representatives.

The common-diagonal chronology is a separate condition. The companion note reduces it to an exact list of physical interpolation tests and proves their sufficiency; the curves and weights alone do not assert the existence of a triangular tableau.
