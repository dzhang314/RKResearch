# Eigenspace ranks and arithmetic obstructions for fixed weighted transposes

A nonsingular lower-triangular tableau at the attained full-weight balanced parity floor that is fixed by weighted transpose plus stage reversal is much more restrictive than a tableau that is merely carried to another tableau of the same order. We give a complementary rank equation at every grade, an isometry obstruction at every odd balanced order, and a parity refinement for the actual clock-group defect moments. In particular, **over the rationals no such fixed tableau exists at an odd balanced order \(p\ge3\)**, with no restriction on clock multiplicities or on equality of the diagonal entries. This is a symmetry obstruction, not a lower bound for predominantly nonsymmetric methods.

## 1. Setting and exact complementary eigenspace ranks

Let \(K\) be a field, let \(A\) be lower triangular with all diagonal entries nonzero, and suppose \(\operatorname{HasOrder}(p,A,b)\) with \(p\ge2\) and all \(b_i\ne0\). Put
\[
 x=A\mathbf1,\qquad u=2x-\mathbf1,\qquad
 C=\operatorname{diag}(x),\qquad R=CA-AC-A^2,\qquad
 \langle v,w\rangle_b=\sum_i b_i v_iw_i.
\]
Products and powers of stage vectors are coordinatewise. Write \(J\) for chronological reversal and \(A^\dagger=\operatorname{diag}(b)^{-1}A^{\mathsf T}\operatorname{diag}(b)\). The fixed-point assumption is \(Jb=b\) and \(J A^\dagger J=A\). The balanced floor means that both terminal parity censuses equal the stage number \(n\). At positive orders above one this is the attained nonsingular stage floor with \(p\not\equiv1\pmod4\).

Let \(E_j\) be the genuine elementary column span through grade \(j\), and let \(F_j\) be the span of equal-grade, forest-factorial-normalized tree differences through grade \(j\). In the paid range \(0\le j\le p-1\) the attained chart gives
\[
 F_j=E_{p-1-j}^{\perp_b},\qquad
 E_j=F_j\oplus\operatorname{span}(\mathbf1,u,\ldots,u^{q_j}),\qquad
 q_j=\min(j,p-1-j).
 \tag{1}
\]
For clarity, the elementary rank is the parity census at every grade: applying the Volterra rank step backwards from either tight terminal count leaves no room for excess. For \(j\ge2\), \(R E_{j-2}\subset F_j\), \(R\) is invertible, and the affordable clock block is independent modulo \(F_j\) by the paid Hankel determinant. Its width gives equality and the split in (1); the grades zero and one have no defects. Products give \(F_j\subset E_{p-1-j}^{\perp_b}\), and reflection of the parity widths gives equality of the dimensions. These are the exact flags of the [weighted-transpose transfer](weighted-transpose-involution.md), not assumed extra simplifying conditions.

Here is the flag-invariance argument at arbitrary balanced order. For \(j+1<p\), the map \(A^\dagger\) sends \(F_j\) into \(F_{j+1}\), since it is adjoint to \(A:E_{p-2-j}\to E_{p-1-j}\). Let \(v\) be any genuine normalized tree of size \(d\) with \(d+j+1\le p\). The paid scalar identity is
\(\beta x^r v=1/(d+r)\) for \(r\le p-d\), where \(\beta=b^{\mathsf T}\). Unary attachment produces the normalized size-\(d+1\) column \(dAv\). Its paid clock probes agree with those of \(xv\), so in particular
\[
 d\,\beta((1-x)^j Av)=\beta(x(1-x)^jv).
\]
The same pure moments of \(v\) identify the two sides of the beta identity
\[
 (j+1)\beta(x(1-x)^jv)=d\,\beta((1-x)^{j+1}v).
\]
Indeed this is the zero endpoint difference of the formal derivative of \(X^d(1-X)^{j+1}\); all divisions used by formal integration have indices at most \(d+j+1\le p\). Pairing with every such \(v\) and using (1) proves
\[
 (j+1)A^\dagger(1-x)^j-(1-x)^{j+1}\in F_{j+1}.
\]
At \(j=0\), \(F_1=0\) proves \(A^\dagger\mathbf1=1-x\). Multiplication by \(1-x\) advances \(F\), by the original clock advance and monotonicity, and all affordable products of defects remain in their original flag. Reflected pure quadrature is paid by the binomial change \(X\mapsto1-X\). Thus the same normalized tree recursion, attaching a size-\(d\) tree by multiplying by \(d A^\dagger\) of its column, places every new normalized tree of grade \(j\) in \((1-x)^j+F_j\) and proves its paid scalar condition. Subtracting equal-grade columns gives inclusion of the new defect flags, and the reflected powers are polynomials of the same degrees in \(x\), giving inclusion of the new elementary flags. The reversed weighted transpose is again nonsingular lower triangular at the same balanced floor and the same order, so its exact flag ranks are the same by (1); both inclusions are equalities.

On the fixed chart this gives \(J E_j=E_j\), \(J F_j=F_j\), and \(Ju=-u\). Characteristic two does not arise: all the integer casts \(1,\ldots,p\) are units under the attained order. Set \(H_\pm=\ker(J\mp I)\), \(h_+=\lceil n/2\rceil\), \(h_-=\lfloor n/2\rfloor\), and
\[
 c_+(q)=1+\lfloor q/2\rfloor,\qquad
 c_-(q)=\lfloor(q+1)/2\rfloor .
\]
The two \(H_\pm\) are mutually orthogonal and nondegenerate under \(\langle\, ,\,\rangle_b\), because \(Jb=b\). A superscript \(\epsilon\in\{+,-\}\) means intersection with \(H_\epsilon\). Taking both the clock split and the weighted duality in their separate eigenspaces gives the exact all-grade formula
\[
 \boxed{\ \dim F_j^\epsilon+\dim F_{p-1-j}^\epsilon=h_\epsilon-c_\epsilon(q_j)\ },\qquad
 \dim E_j^\epsilon=\dim F_j^\epsilon+c_\epsilon(q_j).
 \tag{2}
\]
This equation does not assume that \(R\) commutes with \(J\); it generally need not.

## 2. The odd-order isometry and discriminant obstruction

Write the odd balanced order as \(p=4m-1\), \(m\ge1\). Then \(n=2m^2\) and the middle grade is \(j=2m-1\). Formula (2) fixes
\[
 \dim F_{2m-1}^{+}=\dim F_{2m-1}^{-}=\frac{m(m-1)}2,\qquad
 \dim E_{2m-1}^{+}=\dim E_{2m-1}^{-}=\frac{m(m+1)}2 .
 \tag{3}
\]
In particular it recovers the one direction of each sign in the order-seven cubic defect space.

There are exactly \(m^2\) reversal pairs of physical stages. The coordinates on one member of each pair identify both ambient forms on \(H_+\) and \(H_-\) with the same diagonal form \( \operatorname{diag}(2 b_i)\). Write \(P^\epsilon\) for the pure clock sector of degree at most \(2m-1\). Its form is nondegenerate by the paid Hankel determinant and the eigenspace split. Formula (1) at the middle grade implies that \(F_{2m-1}^\epsilon\) is totally isotropic in \((P^\epsilon)^{\perp_b}\) inside \(H_\epsilon\), and (3) says it has exactly half that complement's dimension. Thus the complement is hyperbolic: choose vectors dual to an isotropic basis and subtract half their Gram matrix from the dual vectors in the isotropic directions. In the resulting basis the Gram matrix is
\(\left(\begin{smallmatrix}0&I\\I&0\end{smallmatrix}\right)\).

Consequently the two rational pure clock forms, interpreted in \(K\), must become isometric:
\[
 G_+\ \cong\ G_-,\qquad
 (G_+)_{ij}=\frac1{2(i+j)+1},\quad
 (G_-)_{ij}=\frac1{2(i+j)+3},\quad 0\le i,j<m .
 \tag{4}
\]
Indeed both complements are the same number of hyperbolic planes and can be canceled from the isometric ambient forms. Equivalently one may use rank-one cancellation successively after diagonalizing each hyperbolic plane: given two vectors of the same nonzero norm, reflection in their difference or their sum gives an isometry taking the first to the second (with a sign change if needed). One of those two reflection vectors is nonisotropic because the sum of the two norms is four times the common nonzero norm. This proves the needed cancellation over fields of characteristic different from two.

To check the entries of (4), the affine change \(u=2x-1\) sends the paid monomial quadrature to zero on odd powers and to \(1/(d+1)\) on even powers of degree \(d\), for \(d\le p-1\). This is the finite binomial identity
\[
 \sum_{a=0}^d {d\choose a}\frac{2^a(-1)^{d-a}}{a+1}
   =\frac{1-(-1)^{d+1}}{2(d+1)} .
\]
All its divisions are permitted, and the two pure bases in the middle are \(1,u^2,\ldots,u^{2m-2}\) and \(u,u^3,\ldots,u^{2m-1}\).

Already determinant square classes obstruct (4). The Cauchy numerators of \(G_+\) and \(G_-\) coincide. Their denominator ratio telescopes:
\[
 \frac{\det G_+}{\det G_-}
   =\prod_{i,j=0}^{m-1}\frac{2(i+j)+3}{2(i+j)+1}
   =\prod_{i=0}^{m-1}\frac{2m+2i+1}{2i+1}
   =\frac{(4m-1)!!}{((2m-1)!!)^2}.
 \tag{5}
\]
Therefore \((4m-1)!!\) must be a square in \(K\). Over \(\mathbb Q\), a prime strictly between \(2m\) and \(4m\) exists by Bertrand's postulate and has valuation one in that odd product. This gives the stated rational exclusion, including orders 7, 11, 15 and 19. At order seven the necessary square class is \(105\), without assuming four distinct clocks; at order eleven it is \(1155\). This is strictly a restriction on being fixed by reflection, not on arbitrary rational tableaux.

There are also concrete positive-characteristic exclusions. If \(\ell=4m+1\) is prime and \(m\) is odd, the square-class condition fails over \(\mathbb F_\ell\): by Wilson's theorem,
\((4m-1)!!\equiv-1/(2^{2m}(2m)!)\), and \(((2m)!)^2\equiv-1\pmod\ell\). For \(\ell\equiv5\pmod8\) a square root of \(-1\) is not itself a square. For example, the order-eleven fixed chart is empty over \(\mathbb F_{13}\). This uses \(\ell>p\), not a denominator degeneracy. Over an ordered field the two pure blocks are positive definite (the paid rational Gram matrices have positive leading Cauchy minors). Thus each chronological half has exactly \(m(m-1)/2\) negative and \(m(m+1)/2\) positive output weights. No positivity of the given weights was assumed.

## 3. Even-order residual and its exact limitation

At \(p=2m\) let \(P_\epsilon\) be the sector of \(\operatorname{span}(1,u,\ldots,u^{m-1})\), put \(f_\epsilon=\dim F_{m-1}^\epsilon\), and write
\[
 W_\epsilon=F_m^\epsilon/F_{m-1}^\epsilon,\qquad
 d_\epsilon=h_\epsilon-c_\epsilon(m-1)-2 f_\epsilon .
 \tag{6}
\]
The quotient bears a nondegenerate induced form of dimension \(d_\epsilon\). Indeed \(F_{m-1}^\epsilon\) is isotropic and \(F_m^\epsilon\) is its orthogonal complement inside \(P_\epsilon^{\perp_b}\), by (1). Splitting off the hyperbolic planes of the isotropic subspace gives
\[
 H_\epsilon\cong P_\epsilon\ \perp\ H^{f_\epsilon}\ \perp\ W_\epsilon,
 \qquad d_++d_-=\lfloor m/2\rfloor,
 \tag{7}
\]
where \(H\) denotes a hyperbolic plane. The last identity follows from \(n=m(m+1)/2\) and \(\dim F_{m-1}=\lfloor(m-1)^2/4\rfloor\). The two ambient forms are the same form on matched pairs, except that for odd \(n\), \(H_+\) also contains the line of the central weight, whereas \(H_-\) does not. Equations (6)–(7) are a necessary exact rank and form constraint; the residual forms cannot simply be canceled as in the odd case.

For example, at \(p=6,n=6\) the cap \(d_+\ge0\) forces the actual order-two defect direction to be odd; at \(p=10,n=15\) both \(d_+\) and \(d_-\) are odd and their sum is two, forcing two directions of each sign in \(F_4\) and one residual direction of each sign. Also, odd \(n\) forces a physical midpoint clock at the central stage. Thus if \(m\equiv2\pmod4\), the balanced even-order floor has odd \(n\) and cannot have exactly the minimal \(m\) distinct clocks: the total number of sites of a reflected set containing its midpoint is odd. This gives at least \(m+1\) distinct clocks on that fixed chart, e.g. at order twelve. No claim of a universal even-order field exclusion is made.

## 4. A parity refund for actual clock-group defect moments

The following rule applies whether or not the elementary ranks are tight, provided the clock and weight data reflect and the indicated vector signs hold. Let the \(q\) distinct centered clock sites be \(\xi_g\), with monic nodal polynomial \(P(X)=\prod_g(X-\xi_g)\). For \(f\in F_a^\epsilon\), \(g\in E_d^\delta\) with \(a+d+1\le p\), put
\[
 \mu_{\xi}=\sum_{i:u_i=\xi}b_i f_i g_i,\qquad D=p-1-a-d,\qquad \sigma=\epsilon\delta.
\]
Then \(\mu_{-\xi}=\sigma\mu_\xi\) and the paid moments against all polynomials of degree at most \(D\) vanish. Equivalently there is a unique polynomial \(Q\) with
\[
 \mu_\xi=\frac{Q(\xi)}{P'(\xi)},\qquad
 \deg Q\le q-D-2,\qquad Q(-X)=\sigma(-1)^{q-1}Q(X).
 \tag{8}
\]
A negative degree bound means the zero polynomial. To prove the representation, interpolate the values \(Q(\xi)=P'(\xi)\mu_\xi\) in degree less than \(q\). The top coefficient of the Lagrange interpolation polynomial for the weighted values \(X^dQ\) is exactly \(\sum_\xi \xi^d\mu_\xi\). If \(Q\ne0\) and \(\deg Q>q-D-2\), take \(d=q-1-\deg Q\le D\) to get a nonzero top coefficient; the converse follows by the same formula. The reflection identity follows from \(P'(-\xi)=(-1)^{q-1}P'(\xi)\) and interpolation. This proves the reflection refund for all degrees, over the original field.

In the minimal-clock odd balanced chart \(p=4m-1,\ q=2m\), the actual grade \(a=b=m\) has \(D=q-2\). Same-sign products in \(F_m\) thus vanish groupwise. Opposite-sign products leave at most a constant numerator \(Q\), defining a common bilinear pairing \(\Gamma\) across the groups after the known factor \(1/P'(\xi)\). The pairing factors through \(F_m^\pm/F_{m-1}^\pm\), because lowering either grade buys one further clock test. Since \(\dim F_m-\dim F_{m-1}=\lfloor m/2\rfloor\), its rank \(r\) obeys
\[
 r\le\lfloor m/4\rfloor .
 \tag{9}
\]
In particular the entire paired grade is zero groupwise at orders seven and eleven; only rank-one cross-pairing can remain at orders fifteen and nineteen.

Here is an actual cell-size consequence. Write \(N_\xi\) for the number of stages in a clock group and \(L_\xi\) for the restrictions of \(F_m\) to that group's coordinates. The group total weight is nonzero, since the exact \(q\)-by-\(q\) pure Hankel determinant factors through the invertible node Vandermonde and the group masses. The image \(L_\xi\) lies in the nondegenerate zero-mean complement of the group constant vector: the first moments of its members already have the full \(q\) clock tests. The restricted weighted form on \(L_\xi\) has rank exactly \(2r\), by the same-sign zero blocks and the common cross-pairing of rank \(r\). Its radical therefore has dimension \(\dim L_\xi-2r\), giving
\[
 N_\xi\ \ge\ 1+2\dim L_\xi-2r.
 \tag{10}
\]
At order seven this recovers the exclusion of four pair groups: the initial stage-order-two seed has value \(A_{00}^2\ne0\), and \(F_2\) is one-dimensional and \(J\)-invariant, so the final value is its nonzero signed reflection. The four reflected clock sites have no midpoint, hence these are different groups. Each needs at least three stages and the others at least one, so the multiplicities are exactly \(3,3,1,1\). The same argument on the fixed chart does not need equal diagonals. At order eleven the grade-three restriction requires at least five stages at any site where its local rank is two, not just three for a single active seed.

Finally, reflection makes the pure quadrature at odd \(p\) satisfy the additional top odd centered moment automatically, even with more than the minimal number of nodes. At the minimal \(q=(p+1)/2\) this makes the node polynomial the usual monic Gaussian polynomial for the uniform centered moments, since all its tests through degree \(q-1\) are then paid. This recovers the Gaussian conclusion from the earlier four-clock result and is logically independent of the no-clock-guard obstruction (5).

All proofs here are mathematical. The companion exact-arithmetic checker tests the recurrent ranks, determinants, and the finite support parity identity; it is not a construction of a tableau or a Lean kernel receipt.
