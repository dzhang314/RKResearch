# Supported early quartic excludes live reflected arithmetic at the seven-zero floor

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight, over a field of characteristic zero or greater than seven, with common diagonal \(\gamma\ne0\). Let \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly seven physical entries of \(\mathbf g\) vanish, at seven distinct literal clocks, and the three other physical clocks are pairwise distinct. Use the actual last three physical rows in reflected orientation. Suppose their second defect ratio is nonzero and physical row 8 is live in the arithmetic phase.

**Result.** This is impossible over every such paid field, independently of the forward first-three phase or placement of the three off rows. No real or ordered structure is required. This packet does not exclude the live reflected star or silent reflected ghost modes, nor change the overall stage interval.

## 1. Full support at grade four and exact pure grade-five rank

Use the [paid support and rank census](../sdirk-eight-seven-eight-zero-census/README.md). Write \(U=\ker\operatorname{diag}(\mathbf g)\), \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\), and \(C'=\operatorname{diag}(\mathbf x)\). The off projection of \(E_3\) has rank three because the scalar \(1,T,T^2\) evaluations at its distinct off clocks are independent. The off restrictions of \(W_2,W_3\) vanish; in particular all three off weights are silent.

There is an actual supported representative of **every** polynomial of degree at most four, irrespective of the leading degree of the interpolating residual. Let \(P\) be the degree-at-most-two graph interpolating the normalized nonzero residuals \(\mathbf g/\gamma^2\) on the three off clocks, and let \(R_{\rm off}\) be the monic cubic with those off clocks as roots. The five supported stage features
\[
 \mathbf p,\ C'\mathbf p,\ (C')^2\mathbf p,\
 \mathbf r,\ C'\mathbf r,\qquad
 \mathbf p=P(\mathbf x)-\mathbf g/\gamma^2,\quad
 \mathbf r=R_{\rm off}(\mathbf x)
\]
belong to \(E_4\). Their actual restrictions to \(U\) are the scalar profiles \(P,TP,T^2P,R_{\rm off},TR_{\rm off}\); they are zero individually on the off rows. The polynomials are a basis of degree-at-most-four profiles. Indeed \(\gcd(P,R_{\rm off})=1\), because \(P\) has a nonzero value at each of the three simple roots of \(R_{\rm off}\). A relation \(P\,p+R_{\rm off}q=0\) with \(\deg p\le2,\deg q\le1\) implies that the cubic divides \(p\), so \(p=q=0\). This checks the rank even where \(P\) is linear or constant. The actual supported space also has dimension \(8-3=5\) by the same off rank on \(E_4\).

The pure forward space \(F_5\) has dimension six, and \(G E_3\subset F_5\) has rank three and vanishes on \(U\), where \(G=\operatorname{diag}(\mathbf g)\). Thus \(\dim(F_5|_U)\le3\). On the other hand the shifted Legendre polynomials \(L_{3,D},L_{4,D},L_{5,D}\) are all actual pure grade-five scalar traces: their pairing with \(W_2\) is zero by the degree-two scalar moment, and \(F_5=\operatorname{Ann}(W_2)\) at saturation. All these integrals use degree at most seven. Their leading coefficients \(20,70,252\) are units in the paid field, so the polynomials remain independent on seven distinct zero labels. Consequently
\[
                 F_5|_U=\langle L_{3,D},L_{4,D},L_{5,D}\rangle|_U . \tag{1}
\]
The argument uses neither any weight sign nor a leading pivot on a particular triple of zero rows.

## 2. The first five actual forward zero reads

Work in the reflected scalar coordinate \(Y=D-T\) while retaining the actual **forward** chronological order. Write \(y_i=D-x_i\), and \(I_D(Y^j)=D^j/(j+1)\). The last three literal sites are \(y_s=1,\ y_t=1+v,\ y_r=1+2v\), where \(s,t,r\) are physical rows \(10,9,8\), respectively. They are live: rows 9 and 10 always have nonzero weights and this branch assumes row 8 is nonzero-weight.

Take the monic polynomial \(P_4(Y)\) with roots the four earlier zero clocks. It is an actual supported degree-four input by section 1: use its precomposition \(P_4(D-T)\) in the five-dimensional profile space. Its actual \(A'\) reads are zero at the first four zero rows and diagonal at row \(r=8\), since every earlier supported input is zero and the literal diagonal is one. The pure discrepancy from the primitive \(J_D^*P_4(Y)=\int_Y^D P_4(X)\,dX\) lies in \(F_5|_U\). Thus by (1) the actual image on \(U\) is represented by one polynomial
\[
 \Pi(Y)=J_D^*P_4(Y)+\sum_{j=3}^5 \lambda_j L_{j,D}(D-Y)
\]
of degree at most five. It vanishes on the four distinct early roots, so it is \(P_4\) times a linear polynomial (also allowing a constant quotient). At \(y_r\), division by \(P_4(y_r)\ne0\) says the quotient is one. Therefore
\[
                   \Pi(Y)=[1+\nu(Y-y_r)]P_4(Y)                 \tag{2}
\]
for some scalar \(\nu\). There is no appeal to a polynomial interpolation inverse on first-three rows or to a real order of the clocks.

Pair (2) with \(Y^k\), \(k=0,1,2\). The Legendre correction has zero mean under each. Formal monomial integration, or changing the order of the two polynomial primitives, gives the exact coefficient identity
\[
 I_D(Y^k J_D^*P_4)= I_D(Y^{k+1}P_4)/(k+1).
\]
Thus for \(m_k=I_D(Y^kP_4)\) the three equations are
\[
 \left(m_k-\frac{m_{k+1}}{k+1}\right)+
             \nu(m_{k+1}-y_r m_k)=0.                           \tag{3}
\]
Only the first two of these will be used.

## 3. Rear cardinal moments and a paid contradiction

The pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\) is supported on \(U\) and annihilates the first six powers. On its seven distinct labels it is therefore a nonzero barycentric row. Write \(P_7(Y)=P_4(Y)(Y-y_s)(Y-y_t)(Y-y_r)\), and \(B_j=I_D(P_7/(Y-y_j))=b_jP'_7(y_j)\). In particular \(B_t\ne0\). Put \(\kappa=1+2v-v^2\ne0\) and \(\rho=B_r/B_t\); by the literal reverse residual ratios
\[
 B_s/B_t=\kappa,\qquad
 \kappa_3\rho=\kappa,\qquad
 H(v)\kappa_3=-\kappa Q(v),
\]
where \(H(v)=v^3-4v^2-v+2\), \(Q(v)=4v^3-12v^2+3v+2\), and \(\kappa_3\) is the actual third ratio. These are the [literal reflected arithmetic identities](../sdirk-eight-seven-zero-pure-distinct/README.md#2-rear-cardinal-rows-and-the-arithmetic-compatibility-sextic), before division by \(H\) or \(Q\). By cancellation of the nonzero \(\kappa\), they give \(\rho Q=-H\).

The three quadratic tail cardinal polynomials are a basis on \(1,1+v,1+2v\). Their Lagrange interpolation gives, for \(k=0,1,2\),
\[
 N_k:=\frac{2v^2m_k}{B_t}
       =\kappa-2(1+v)^k+\rho(1+2v)^k .
\]
Writing \(a_0=N_0-N_1,\ a_1=2N_1-N_2,\ c_0=N_1-(1+2v)N_0,\ c_1=N_2-(1+2v)N_1\), the two equations (3) read \(a_0+\nu c_0=0,\ a_1+2\nu c_1=0\). The scalar determinant is
\[
          2a_0c_1-a_1c_0=2v^2(\rho Q-H).
\]
Since \(2v^2\ne0\), this forces \(\rho Q=H\). Hence \(H=0\); the literal ratios and \(\rho\ne0\) force \(Q=0\). But the exact integer identity
\[
 (676v^2-1604v-493)H+(-169v^2+570v+525)Q=64
\]
is impossible in the paid field. This proof does not require the arithmetic sextic, division by either gap polynomial, or a characteristic-zero factorization.

## 4. Scope and replay

Run `python check_scalar.py` for the independent determinant and Bézout checks. The full tableau ingress above uses saturation and paid-field integration; no unconditional bound over arbitrary commutative rings or small-characteristic fields is asserted. The pure proof of (1) and the actual diagonal ingress at physical row 8 are source-level, not hidden inside a native rooted-tableau theorem.

The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightSevenZeroSupportedQuartic.lean) and local proof audit pass on Lean/Mathlib 4.36.0. The full tableau argument remains mathematical.
