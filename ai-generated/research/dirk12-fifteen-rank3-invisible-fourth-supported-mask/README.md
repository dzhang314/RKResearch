# DIRK12/15: fourth-supported mask and a nonzero fifth ordinary diagonal

Work in the real ordinary fifteen-stage \(C(2),f_5=3\) order-twelve equality frame with weighted-invisible cubic and four distinct cubic-dirty ghosts. Assume the [nine-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) or [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronology. The [fourth-diagonal exclusion](../dirk12-fifteen-rank3-invisible-nonzero-fourth-exclusion/README.md) forces the fourth ordinary live nonzero row's diagonal to be zero and its nodal quintic to have nonzero ghost divided difference.

The fifth ordinary live nonzero row now has **nonzero diagonal**; the sixth has zero diagonal, agreeing with the independent reverse construction. The genuine fourth-supported grade-five ghost-zero mask has exact scalar degree five; its exceptional quartic case is excluded separately, by finite coefficient algebras of total degrees \(26\) (first nonroot) and \(8+32\) (first Legendre root). In the remaining case its literal commutator gives a quadratic reconstruction of the sixth read without generic division by the coefficient \(1+\lambda\). We do not eliminate all remaining scalar grids. These restrictions are not an unrestricted lower bound; real DIRK12 is still **15–16**.

## The first-five evaluation of \(F_8\) is invertible

Use physical ordinary variable \(X\), reflected \(Y=1-X\), the first five distinct nonzero ordinary live clocks \(a,b,c,e,f\), and \(g\) for the actual next such clock. These are unique physical rows in the two qualified chronologies: the only repeated nonterminal pair in the nine-site case is still later in ordinary order. The literal ordinary origin is the only earlier numerical live zero; all four ghosts precede \(b\). Let
\[
    P=X(X-a)(X-b)(X-c),\qquad K=(X-e)P,\qquad Q=(X-f)K.
\]
The three early nonzero reverse labels are \(d,v,u\). In these chronologies \(1-g=u\), \(w=1-f\). The shifted fixed hull of the [split-free grid](../dirk12-fifteen-rank3-invisible-split-free-grid/README.md) is
\[
            Y Q(1-Y)=Y^\eta P_{\mathrm{fixed}}(Y),
\]
where \(\eta=1\) only when one of the first five ordinary clocks repeats the literal terminal clock in the nine-site chart. In particular, \(\eta=0\) for the ten-site earliest extra reflected zero (that extra zero is still later in ordinary order). The identity includes \(w=0\) in the nine-site case, though that subcase was excluded independently. Define
\(n_j=\int_0^1 Y^{j+1}Q(1-Y)\,dY\) for \(0\le j\le4\).
These are genuine degree-at-most-eleven scalar moments.

The [actual stage-space calculation](../dirk12-fifteen-rank3-invisible-third-ordinary-live/README.md) puts the nonterminal live restriction of \(F_8\) in \(X\langle L_4',\ldots,L_8'\rangle\). It has scalar degree at most eight and is orthogonal on \([0,1]\) to \((1-X)P_2\), by the genuine \(8+3=11\) tests. If it vanishes at \(a,b,c,e,f\), its already-required origin factor makes it \(Q(X)S(1-X)\), \(\deg S\le2\). The three pairings are the linear system with matrix \((n_{i+j})_{0\le i,j\le2}\) on the coefficients of \(S\).

Paid scalar quadrature gives \(n_j=\sum_{z\in\{d,v,u\}}\omega_z z^j\), with \(\omega_z=B_z z^\eta P_{\mathrm{fixed}}(z)\). The three remaining labels are distinct and nonzero, none is in \(P_{\mathrm{fixed}}\), and each aggregate \(B_z\) is nonzero by the true early barycentric head (including the signed early \(d\)-pair). Thus the moment matrix is \(V\operatorname{diag}(\boldsymbol\omega)V^{\mathsf T}\) for a nonsingular three-site Vandermonde matrix \(V\). Nonzero signed values suffice. Therefore \(S=0\), and a genuine \(F_8\) vector zero at those five live rows is zero on **all** nonterminal live rows. No claim of terminal vanishing is needed.

## A genuine grade-six nodal state and its two primitive reads

Write \(\mathcal A\) for the literal ordinary live-only action of \(A\), omitting the four ghost taps, and \(R=CA-AC-A^2\). For scalar inputs of degree at most six with zero constant, \(\mathcal A(F)-JF\) is in \(X\langle L_5',L_6',L_7'\rangle\), from the true grade-seven scalar discrepancy and the actual ghost-tap profiles. For inputs of degree at most seven it has degree at most eight, by the corresponding true \(T_8,F_8\) projections. We use these polynomial identities only for nonterminal live rows, since the literal terminal is never their source.

All four individual ghost-coordinate directions are in genuine \(F_6\). Consequently \(Q(\mathbf c)\) can be made exactly zero on the four ghosts without changing live entries, producing a genuine grade-six state \(\mathbf S_Q\). The commutator \(R\mathbf S_Q\) is a genuine \(F_8\) vector: \(XJF-J(XF)-J^2F=0\) in the continuous scalar model. It vanishes on the first five live rows by the actual chronological support of \(\mathbf S_Q\), hence all nonterminal live rows by the Hankel rank. At \(g\), the only nonzero potentially available live input is its own \(Q(g)\ne0\); the literal \(R\) value there is minus its diagonal squared times \(Q(g)\). Thus its diagonal is zero.

By causality \(A\mathbf S_Q\) is itself zero at every ghost, because all ghosts precede \(b\) and \(\mathbf S_Q\) is zero through \(a\). Its live profile \(\mathcal A(Q)\) is degree at most seven and vanishes through \(g\). It equals
\[
                    \mathcal A(Q)=\Lambda(X-g)Q.
\]
Pairing \( \mathcal A(Q)-JQ\) with \(1-X\), with one ordinary primitive, gives
\[
                   \Lambda(u n_0-n_1)=n_1/2 .
\]
With \(h=3n_1/(2n_0), q=n_0n_2/n_1^2\), the true split-free relations \(u/h=2q/(9-6q)\) and \(n_1/(h n_0)=2/3\) give
\[
        \Lambda=\frac{3-2q}{6(q-1)},\qquad
        c_*=-\frac{\Lambda^2}{1+\Lambda}.
\]
The actual guards \(q\ne1,3/2,3/4\) ensure \(\Lambda\ne0\) and \(1+\Lambda\ne0\). The equation \(R\mathbf S_Q=0\) on nonterminal live rows and ghost-zero \(A\mathbf S_Q\) give
\[
 (1+\Lambda)\mathcal A(XQ)=(X+\Lambda g)\mathcal A(Q),\qquad
 \mathcal A(XQ)=X\mathcal A(Q)+c_*(X-g)^2Q .
\]
These identities hold as polynomials of degree at most eight, because the chart has at least nine distinct nonterminal live labels. No pure grade nine is being used here.

## Why the actual fifth diagonal is nonzero

Independently of the absence of a grade-five mask for \(K\), its four ghost values can be removed using the actual \(F_6\) coordinates, giving a **grade-six** state \(\mathbf S_K\). This state and \(A\mathbf S_K\) are zero on ghosts; the latter follows by the same literal chronology. The polynomial \(\mathcal A(K)\) has exact degree seven: in the true two-mode formula, the top term comes from the nonzero product of the \(L_7'\) tap coefficient and the nonzero ghost divided difference of \(K\). All other terms are degree at most six.

If the fifth diagonal were zero then \(\mathcal A(K)\) would vanish through the fifth receiver \(f\), and \(R\mathbf S_K\in F_8\) would too. The latter would therefore vanish on every nonterminal live row. Write \(\mathcal A(K)=QJ_1\), \(J_1=sX+t\), with \(s\ne0\) by the exact top degree. Since \(XK=Q+fK\),
\[
 (X-f)\mathcal A(K)-\mathcal A(Q)-\mathcal A(\mathcal A(K))=0 .
\]
Use the two reads just proved to substitute
\(\mathcal A(\mathcal A(K))=J_1\,\mathcal A(Q)+s c_*(X-g)^2Q\).
After division by \(Q\) one gets
\[
 (X-f)J_1=(1+J_1)\Lambda(X-g)+s c_*(X-g)^2 .
\]
At \(g\), \(g-f\ne0\) forces \(J_1(g)=0\), hence \(J_1=s(X-g)\). Cancel \(X-g\) and compare the linear coefficients:
\[
                         s=s(\Lambda+c_*)=\frac{s\Lambda}{1+\Lambda}.
\]
This is impossible since \(s\ne0\) and \(1+\Lambda\ne0\). These are actual physical diagonals, not coefficients of a compressed numerical-clock tableau.

## The degree-five fourth-supported mask

For \(M(G)=\sum_j\ell_jG(c_j)\) on the four actual ghosts, the divided-difference criterion says that an input of scalar degree at most five has a genuine grade-five ghost-zero mask precisely when \(M(G)=0\). The preceding \(K\) result says \(M(K)\ne0\). Below we exclude \(M(P)=0\) in each ordinary Legendre branch. We may therefore put
\[
      \zeta=M(XP)/M(P),\qquad \tau=e-\zeta\ne0,\qquad
      F=(X-\zeta)P=K+\tau P .
\]
This is the alternative proper grade-five mask. Its scalar is zero on the first three nonzero live rows but is **nonzero at the literal fourth row** \(e\). Let its actual corrected state be \(\mathbf S_F\). The true grade-seven \(R\mathbf S_F\) is zero at the first three live rows, so zero on all nonterminal live rows by their already-proved three-mode evaluation rank. By chronology \(A\mathbf S_F\) is ghost-zero; its profile \(U=\mathcal A(F)\) vanishes through \(e\) because the fourth diagonal is zero. Its discrepancy from \(JF\) is a single multiple of \(X L_6'\) because it is an actual grade-five ghost-zero state. Thus
\[
                     U=L K,\qquad L(X)=\lambda X+\mu.
\]
The profile \(U\) is not identically zero: if \(JF\) is a multiple of \(X L_6'\), its zero derivative at the origin forces the multiple and then \(F\) to be zero. Put \(H=\mathcal A(K)/K\). It is an exact **quadratic**: \(\mathcal A(K)\) vanishes at all roots of \(K\), and its degree is exactly seven as above. Also \(H(f)\) is precisely the nonzero fifth actual diagonal.

Using \(XP=F+\zeta P\), \(XK=Q+fK\), and the actual \(R\mathbf S_F=0\), obtain the following single polynomial identity:
\[
 \begin{split}
  \beta&=(1+\lambda) f+\mu-\zeta,\\
  (1+\lambda)\Lambda(X-f)(X-g)&=(X-e)L(X)-\beta H(X).
 \end{split} \tag{*}
\]
For example, expand \(\mathcal A(XF)+\mathcal A(U)=XU\) using those relations and the known \(\mathcal A(Q)\). No row split or unknown ghost parameter occurs after the geometry-free two-mode primitive is evaluated. No division by \(1+\lambda\) was made. The coefficient \(\beta\) is necessarily nonzero: if it vanished, evaluation at \(f\) would give \(L(f)=0\) and hence \(f=\zeta\). Cancel \(X-f\) in \((*)\) to obtain \((1+\lambda)\Lambda(X-g)=\lambda(X-e)\). Coefficient comparison and \(g\ne e\) force \(\lambda=0\), contradicting \(\Lambda\ne0\). Also \(L(f)\ne0\) by the row value \((f-e)L(f)=\beta H(f)\).

Equation \((*)\) gives a trimmed scalar check **without a new degree-six interpolation** in \(1+\lambda\ne0\): the top coefficient determines \((1+\lambda)\Lambda\), the first moment of its roots determines \(g+f\), and the row equation at \(f\) is a cubic with top coefficient \(-(1+\lambda)[X^2]H\ne0\). Compare the recovered \(\Lambda,g\) against their independent split-free values and then check the true mixed equation and physical reverse gates on both early orientations. If \(1+\lambda=0\), use the degenerate polynomial identity \(\beta H=(X-e)L\) directly and retain the separate genuine degree-six fifth condition. In particular it is invalid to normalize or discard the \(1+\lambda=0\) fiber.

For another division-free comparison, set \(E=1-e\), \(Z=1-\zeta\), and \(M_j=\int Y^{j+1}P(1-Y)\), \(N_j=M_{j+1}-EM_j\); then \(n_j=N_{j+1}-wN_j\). The paid single-primitive relations \(\int Y^{k+1}(U-JF)=0\), \(0\le k\le4\), give
\[
  \tau M_{k+1}=[1+(k+2)\lambda]N_{k+1}-(k+2)(\lambda+\mu)N_k.
\]
In particular for \(0\le k\le3\), with \(l_0=\lambda+\mu\),
\[
 [1+(k+3)\lambda]N_{k+2}
   -[(k+3)l_0+Z+E(k+2)\lambda]N_{k+1}
   +E(k+2)l_0 N_k=0 .
\]
The maximum scalar integrand degree is eleven. These identities are only necessary conditions; they do not assume a vanishing next quadrature discrepancy. The same formulas apply before taking a possible repeated endpoint out of the hull, instead of dividing by its weight.

See [quartic case](quartic-case.md) for the two exact small exclusions. The native core checks the cleared \(\beta\) and final-slope implications and independently checks modular Bézout identities and unit pivots on the seven literal residue coefficient arrays. The stage-space arguments are mathematical, not a new native rooted-order theorem.

## Additional split-free physical interface at \(w\ne0\)

The code in [tail.py](tail.py) independently compares two coefficients read from both actual directions, and the true low reverse lift at \(w\). The case \(w=0\) can only occur for nine sites and has separate [first-root](../dirk12-fifteen-rank3-invisible-nine-site-first-root-zero-exclusion/README.md) and [nonroot](../dirk12-fifteen-rank3-invisible-nine-site-nonroot-zero-exclusion/README.md) exclusions; no weight at such an endpoint is divided out here.

Work with the actual normalized reverse row \(w/d\). Its taps to the numeric labels \(d,v,u,w\) are determined from the first four positive-degree scalar inputs, with the true degree-two through degree-four discrepancies as in the [split-free script](../dirk12-fifteen-rank3-invisible-split-free-grid/grid.py). Call these taps \(T_1,T_r,T_t,T_w\). The actual \(w\) scalar row is a singleton, as is \(u\). Hence \(A_{ff}=dT_w\), and \(B_u A_{gf}=d B_w T_t\), where \(B_s\) are the unique aggregate quadrature weights at the reflected clocks. On the ordinary side, \(\mathcal A(K)(f)=A_{ff}K(f)\) and \(\mathcal A(K)(g)=A_{gf}K(f)\), since \(K\) is zero through \(e\) and the actual sixth diagonal is zero. Thus directly compare
\[
   \mathcal A(K)(f)-dT_w K(f)=0,\qquad
   B_u\mathcal A(K)(g)-dB_w T_t K(f)=0 .
\]
The script evaluates both expressions after ordinary normalization by \(a\) and clears that scalar factor back to the common units. Neither comparison needs to assign an individual weight to either \(d\)-row.

For ten sites the true \(N(Y\mathbf G)/\mathbf G\) is the known quadratic \(\psi\), interpolated at \(0,1,r\) in normalized variables. Thus its literal \(w\)-row requires
\(\sum_{z\in\{1,r,t,w/d\}}T_z z\,G_z/b_z=\psi(w/d)G_w/b_w\) in the normalized amplitudes. The extra numerical-zero source drops from \(Y\mathbf G\) without being removed from the tableau. For nine sites use affine \(N\mathbf H/\mathbf H\). The literal \(d_2\) contribution is \(k(h_w-\sigma T_1)\) because the actual \(\Delta T_{d_2}=h_w-\sigma T_1\); the remainder is \(h_vT_r+h_uT_t+h_wT_w\). This cancels the signed pair split exactly, using the actual nonzero aggregate early pair. These are distinct tests from the genuine mixed \(\alpha/\gamma\) relation and do not replace it or pay \(\varepsilon_{12}\).

    python3 -B verify.py
    python3 -B rebuild-quartic.py
    python3 -B verify-quartic.py
    python3 -B tail.py

The last command checks the two exact arithmetic paths with rational negative controls, not an enumeration or a candidate tableau.
