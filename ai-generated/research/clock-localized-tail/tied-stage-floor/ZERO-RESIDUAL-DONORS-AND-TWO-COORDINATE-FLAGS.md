# At floor equality: zero-residual donors or two-coordinate flags

Assume an ordinary order-\(p\) nonsingular lower triangular RK tableau over a paid field, with \(p\ge3\), \(p\) even or \(p\equiv3\pmod4\), and \(s=Q(p)\). These are precisely the order parities used here where both parity sums reach the quadratic floor. The conclusions below do not require distinct clocks, nonsingular output weights or a repeated/cancelling fibre. Write
\[
 C\coloneqq\operatorname{diag}(A\mathbf1),\quad
 M\coloneqq CA-AC-A^2,\quad
 \mathbf g\coloneqq A\mathbf c-\tfrac12\mathbf c^{\odot2},\quad
 G\coloneqq\operatorname{diag}(\mathbf g).
\]
Let \(\mathcal W_r\) denote the actual row span of \(\mathbf b^{\rm row}\) followed by words of length at most \(r\) in \(A,C\). As before, genuineness requires the whole word to be within its ordinary tree budget; no auxiliary transpose method is assumed.

The tied parity saturation gives
\[
 F_{j+2}=ME_j,\qquad
 \operatorname{Ann}(E_j)=\mathcal W_{p-3-j}M
 \quad(0\le j\le p-3).
                                                                    \tag{3}
\]
Indeed the ordinary forward and reverse commutator recurrences both attain equality in the paired parity sums, and the right side of the second equality annihilates \(E_j\) and has exactly its codimension. Also \(E_{p-2}=E_{p-1}\) is the whole stage space. Each additional genuine rooted diagonal letter, of cost \(|t|-1\), gives an actual exact row in this same filtration: it has its ordinary scalar polynomial representative plus a row in the annihilator in (3). This uses the same paid word pairing and dimension argument as the two-sided surplus note.

## If any quadratic residual is zero, a genuine donor exists in a proper prefix

For any named index \(i\) with \(g_i=0\) the literal row
\[
                         \ell_i\coloneqq e_i^{\rm row}M
\]
is nonzero with greatest support \(i\), and annihilates \(E_0\) because \(M\mathbf1=-2\mathbf g\). It is in the paid space \(\mathcal W_{p-3}M\) by (3); equivalently the coordinate row \(e_i^{\rm row}\) itself is in \(\mathcal W_{p-3}\). This is not an inferred start or rank of an unobserved path: it is the actual pure reverse read paid at degree zero, with an actual physical pivot at the zero-residual stage.

There is a zero-residual index in a **proper** prefix if there is any zero anywhere. Otherwise only \(g_s=0\) could occur. The terminal weight \(b_s\) cannot vanish, since trimming then preserves order and nonsingularity and violates the quadratic floor. The genuine row \(\mathbf b^{\rm row}G\) annihilates \(E_{p-3}\), by the quadratic pure identity, so (3) puts it in the one-dimensional space spanned by \(\mathbf b^{\rm row}M\). Its terminal coefficient is zero when \(g_s=0\), whereas \((\mathbf b^{\rm row}M)_s=-b_s a_{ss}^2\ne0\). Hence \(b_i g_i=0\) for every row. A real or paid-field order-\(p\ge3\) quadrature needs two or more nonzero weights (already the 2-by-2 Hilbert matrix has nonzero determinant). That leaves an earlier weighted zero of \(\mathbf g\), a contradiction to the assumed sole terminal zero.

These donors are **necessarily refunded** by the older commutator image at equality. Their existence does not alone increase the stage count. It is the universal physical donor alternative in this branch, rather than a presumed cancelling weight group.

## Higher degree and the coordinate-zero invariant

Set
\[
 T\coloneqq -2M^{-1}G,\qquad
 Z\coloneqq\{i:g_i=0\},\qquad
 L\coloneqq\{i:g_i\ne0\}.
\]
The actual \(T\) preserves every \(E_j\) through \(p-3\), by \(GE_j\subseteq F_{j+2}=ME_j\); the two later full spaces are also invariant. Further \(T\mathbf1=\mathbf1\). Its kernel is the literal coordinate space on \(Z\). The algebraic multiplicity of eigenvalue zero equals \(|Z|\) because \(T\) is lower triangular with diagonal \(2g_i/a_{ii}^2\). As its geometric multiplicity is also \(|Z|\), zero is semisimple and
\[
 E_j=(E_j\cap\ker T)\oplus(E_j\cap\operatorname{im}T).
\]
This can be proved without splitting other eigenvalues: the projection onto the zero factor is a polynomial in \(T\) by the relatively prime \(x\) and nonzero parts of its minimal polynomial. Equivalently, writing \(I_Z\) for coordinate inclusion and \(R_Z\) for restriction, the projection is exactly
\[
          I_Z (M_{ZZ})^{-1}R_Z M,
\]
where the actual principal block \(M_{ZZ}\) is invertible. Its kernel is \(\{v:R_Z M v=0\}=\operatorname{im}T\); the displayed map is the identity on the coordinate space on \(Z\).

In particular if \(E_j\) restricts injectively to the actual nonzero-residual coordinates \(L\), then \(E_j\subseteq\operatorname{im}T\). Every \(e_i^{\rm row}M\) for \(i\in Z\) then annihilates \(E_j\), every corresponding \(e_i^{\rm row}\) is in \(\mathcal W_{p-3-j}\), and \(F_{j+2}\) is zero at every \(i\in Z\). Thus each zero-residual stage actually evaluates all rooted models through degree \(j+2\) at its own clock. This higher-degree conclusion does not treat a single vanishing quadratic as by itself sufficient. In particular two distinct nonzero-residual clocks suffice for \(j=1\), since \(E_1=\operatorname{span}(\mathbf1,\mathbf c)\). In a singleton clock method with just one nonzero-residual coordinate, that coordinate must be silent by \(\mathbf b\cdot\mathbf g=0\). In a nonsingular lower triangular method the first coordinate has \(g_1=a_{11}^2/2\ne0\), so it is the silent coordinate in that sole-residual case.

More generally let \(\nu_j\coloneqq\dim(E_j\cap\ker T)\). The span of all \(e_i^{\rm row}M\) for \(i\in Z\) has a subspace of dimension exactly \(|Z|-\nu_j\) annihilating \(E_j\), since the coordinate-zero projection of \(E_j\) has rank \(\nu_j\). If a literal leading prefix contains \(z_P\) such named zero coordinates, at least \(z_P-\nu_j\) independent rows of this form are supported there, whenever this number is positive. For each one (3) gives exactly the older read with those zero coordinates, not a fictional pure clock row. As above no stage increase follows without an independent incompatibility with older rank.

## If no quadratic residual is zero

The alternative supplies an especially simple genuine rooted description. Now \(G\) is invertible on the whole stage space. From \(GE_j\subseteq F_{j+2}=ME_j\) and equality of dimensions,
\[
 F_{j+2}=GE_j .
\]
Hence by induction each \(E_j\) through \(p-1\) is exactly evaluation of the genuine two-coordinate polynomial space
\[
 \operatorname{span}\{\, x^\ell z^k:\ \ell+2k\le j \,\}
       \quad\text{at the literal pairs }(c_i,g_i).
\]
The argument uses the scalar lifts \(\mathbf c^{\odot\ell}\) and the pure space \(F_j=GE_{j-2}\); it does not claim independent monomials past the scalar cutoff. Since \(E_{p-2}\) is full, no two physical stages can have identical pairs \((c_i,g_i)\). The diagonal weighted-support recurrence in the companion note now also proves every \(b_i\ne0\). By scalar ranks and exact orthogonality, the spaces of actual reverse rows are the weighted images of these same numerical polynomial flags; one can see it directly by replacing the saturated right-\(M\) image by the same-dimensional right-\(G\) image at each grade.

Over the reals at the odd tied orders the companion sign theorem then forces both signs of \(\mathbf g\) on positively weighted stages and gives the exact joint \((\operatorname{sgn}b_i,\operatorname{sgn}g_i)\) census. This is the alternative to finding a cancelling repeated clock. The argument still allows mixed signs at the floor and therefore does not assert an improved unrestricted stage minimum.
