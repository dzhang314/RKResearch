# DIRK12/15: endpoint debit and chronology of the four cancelling pairs

Consider real ordinary order-twelve DIRK with \(C(2)\), fifteen stages and \(f_5=3\), on the [exact four-cancelling dirty-label case](../dirk12-fifteen-rank3-four-active-cubic/README.md). There are four actual dirty pairs. At each of their four distinct numerical clocks \(z\), the two physical stages have the same nonzero cubic defect \(h_z\) and opposite nonzero weights. The other seven physical rows are clean, on the fixed seven-node Lobatto grid including the literal origin and terminal. All weights are live. No dirty clock is assumed to differ from every clean clock. This is an exact necessary structure, not an exclusion of this subcase. The overall real bound remains **15–16**.

Write \(T_j,F_j,\mathcal B_j\) for the actual numerical, pure forward and true scalar weighted reverse spaces at grade \(j\), i.e. tree order minus one. Let \(D=L_6'\), \(C=\operatorname{diag}(\mathbf c)\), \(\beta\mathbf v=\mathbf b\odot\mathbf v\) and \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\). Let \(F(X)=\prod_z (X-z)\) be the monic hull of the four dirty labels (not a pure space). Put \(i_z<j_z\) for the actual two physical rows at \(z\), \(b_z=b_{i_z}=-b_{j_z}\), \(\mathbf u_z=\mathbf e_{i_z}+\mathbf e_{j_z}\), and \(\psi_z(v)=v_{i_z}-v_{j_z}\). Let \(\mathcal C\) be the eleven-dimensional space of vectors equal within every pair, and \(\mathcal U=\mathbf h P_3(\mathbf c)\), the four-dimensional span of the \(\mathbf u_z\). Put \(\kappa_z=1/(h_z F'(z))\). These are true nonzero factors.

## The bidirectional splitter and single endpoint debit

The four active labels give
\[
 F_j=\mathbf h P_{j-3},\qquad \mathcal B_j=\beta F_j\quad(3\le j\le5).
\]
In particular \(\mathcal B_5=\operatorname{Ann}T_6\), \(\mathcal B_4=\operatorname{Ann}T_7\), and both sides' genuine grade-five pure spaces vanish at all clean rows. The actual reverse grade-six flag has rank five and equals \(Z=\operatorname{Ann}T_5\cap\{\lambda_\tau=0\}\); see the [rank-three reverse alternative](../dirk12-fifteen-rank3-four-active-cubic/README.md). This also follows here because it contains the four-dimensional clock-invariant \(\beta\mathcal U\), and the incoming weighted two-detector gain disallows a unit 3-to-4 step into an invariant grade-six space.

The seven clean values can be set independently with degree-six scalars. The four dirty coarse values are then freely adjusted by \(\mathcal U\). Thus \(P_6(\mathbf c)+\mathcal U=\mathcal C\), even when a dirty pair shares the numerical clock of a clean row. The true \(T_6\) has rank twelve, so \(F_6=\mathcal U+\langle\mathbf k\rangle\), where \(\mathbf k\) splits the two rows in at least one dirty pair. The conditions \( (\beta\mathbf h)P_2\subset\operatorname{Ann}T_6\) say that the four numbers \(b_z h_z\psi_z(\mathbf k)\) annihilate powers \(1,X,X^2\) on the four labels. Vandermonde yields the unique barycentric line. Normalize \(\mathbf k\) so
\[
                         b_z\psi_z(\mathbf k)=\kappa_z
                               \quad\text{for every }z .
\]
In particular **all four pairs split**.

In the weighted reverse space, \(\mathcal B_6\) contains \(\beta\mathcal U\), the span of the antisymmetric coordinate rows of each pair. A vector \(\boldsymbol\zeta\in Z\setminus\beta\mathcal U\) has nonzero aggregate on some dirty pair: otherwise subtract within \(\beta\mathcal U\) to leave only the six nonterminal clean entries, where annihilation of \(P_5(\mathbf c)\) forces it zero. Pairing \(\boldsymbol\zeta\) with \(F_5=\mathbf hP_2\) imposes exactly the same barycentric pattern. Normalize so \(\zeta_{i_z}+\zeta_{j_z}=\kappa_z\) for every \(z\). The normalized reverse pure vector \(\mathbf k^\vee=\beta^{-1}\boldsymbol\zeta\) then splits all pairs and has the same differences as \(\mathbf k\). This inverse uses the already proved all-live case only.

Both \(\beta\mathbf k\) and \(\boldsymbol\zeta\) annihilate \(T_5\): the first by the true \(6+5=11\) product, the second by \(Z\). Already \(\mathbf k(o)=0\) at the literal stage-order-two origin, and \(\zeta_\tau=0\) at the terminal. The six-node Lagrange cardinal for the terminal on the clean nodes excluding the origin is \(D/42\); the origin cardinal excluding the terminal is \(-D/42\). Their paid degree-five tests give
\[
 \mathbf k(\tau)=-\mathfrak d,\qquad
 \mathbf k^\vee(o)=+\mathfrak d,\qquad
 \mathfrak d=\sum_z \frac{D(z)}{h_zF'(z)} ,
\]
using \(b_o=b_\tau=1/42\). Thus:

- if \(\mathfrak d=0\), then \(\beta F_6=\mathcal B_6=Z\) and both pure bands are zero at **both** endpoints;
- if \(\mathfrak d\ne0\), their intersection is precisely \(\beta\mathcal U\), and their sum is the full six-dimensional \(\operatorname{Ann} T_5\).

After subtracting pair differences from \(\beta\mathbf k-\boldsymbol\zeta\), the remaining seven clean entries annihilate the six scalar columns through degree five. Their unique possible line is \(\beta L_6\) restricted to clean rows by the fixed Lobatto moments; at the two endpoints the coefficient is \(-\mathfrak d\). Thus the exact clean discrepancy difference is known on all seven rows, not only at the boundary.

The additional \(\mathbf k,C\mathbf k,\ldots,C^3\mathbf k\) have independent split patterns on the four labels. The saturated rooted ranks give
\[
          T_j=\mathcal C+\langle \mathbf k,C\mathbf k,\ldots,C^{j-6}\mathbf k\rangle
                               \quad(6\le j\le9).
\]
This uses actual forward multiplication by the clock and no normalized adjoint hypothesis.

## Actual reverse construction and the two-site affine law

For linear algebra only, use the weighted adjoint \(\widehat N=\beta^{-1}A^{\mathsf T}\beta\) in the original coordinate ordering; reversing physical order and replacing \(c\) by \(1-c\) makes its actual direction chronological. It is **not** assumed to be a full order-twelve tableau. Its genuine scalar and pure possibilities through grade five are exactly the numerical \(P_j(\mathbf c)+F_j\) (in reflected scalar coordinates when read chronologically), since \(\beta F_j=\mathcal B_j\), and the initial \(D(1),D(2)\) vanish. The normalized reverse grade-six numerical space has the same \(\mathcal C\) plus one splitter. Also \(\widehat N T_5\subset T_6\) and \(\widehat N T_6\subset T_7\) can be proved *without* any reverse-rooted order assertion: test against \(F_5\) and \(F_4\) under the weighted pairing, use \(AF_5\subset F_6\) (with the paid \(5+6=11\) pairing) and \(AF_4\subset F_5\) (paid \(6+5=11\)), then use \(\beta F_5=\operatorname{Ann}T_6\), \(\beta F_4=\operatorname{Ann}T_7\).

Each direction produces its grade-six splitting already by applying its genuine primitive to numerical \(T_5\). In the forward direction, in a grade-six tree with no branch of grade five, every individual branch primitive is in \(T_5\), thus equal within each pair and so is their product. Only an actual primitive of a grade-five stage vector can split a pair. The reverse statement follows from the definition of the actual flag: every new grade-six monomial primitive error or word is generated by the primitive applied to a scalar or lower-flag vector through grade five, or by multiplication by the clock; scalars and clock shifts alone are still coarse. The normalized \(\mathcal B_6\) is not coarse. Therefore in both directions the row difference restricted to \(T_5\) is nonzero at **every** pair (its only possible nonzero pattern is the splitter line with no zero coordinates).

Let \(H_{zw}=\psi_z(A\mathbf u_w)\). Since \(\mathbf u_w\in T_6\), the \(T_7\) description makes \(b_zH_{zw}/\kappa_z\) affine in \(z\) at fixed \(w\). Adjoint pairing gives \(b_zH_{zw}=b_w\psi_w(\widehat N\mathbf u_z)\), hence \(b_z H_{zw}/(\kappa_z\kappa_w)\) is separately affine in \(z,w\). The possible \(zw\) coefficient is zero: \(A(C^2\mathbf h)\in F_6\) has a constant normalized split, whereas summing a separately affine row against the amplitudes \(h_w w^2\) extracts the \(w\)-linear coefficient by the two barycentric identities through degrees two and three. We obtain the exact physical relation
\[
       b_z\,\psi_z(A\mathbf u_w)=\kappa_z\kappa_w(\alpha+\delta z+\epsilon w).
\]
This includes diagonal pair blocks and does not require interval overlap or a generic nonzero tap.

## Literal chronological necessities

1. **At least three distinct dirty labels have appeared before the first nonorigin clean row in either direction.** For any clean row \(s\), the four aggregate taps \(\gamma_z=(A\mathbf u_z)_s\) satisfy \(\sum\gamma_z h_z z^j=0\) for \(j=0,1\), using actual \(A\mathbf h,A(C\mathbf h)\) of grades four and five, clean. Hence \(\gamma_z=\kappa_z(\alpha_s+\delta_s z)\). The same holds in the other physical direction with the actual normalized weighted primitive and its own clock. If at least two dirty labels had not appeared, their two zero taps would make all four aggregate taps zero. Since scalar columns are equal on each pair, the row could then only use the origin and its own clean clock \(u\); its exact scalar primitive of \(X(X-u)\) (grade three) would vanish numerically but equals \(-u^3/6\ne0\).

2. **No dirty pair can physically complete before the second nonorigin clean row in either direction.** For a pair completed that early, its difference of matrix rows, on coarse coordinates, has support only on the origin, possibly the first nonorigin clean clock \(u\), and at most four dirty coarse groups. It annihilates \(T_4\) by the actual inclusion \(AT_4\subset T_5\) (or its actual reverse scalar counterpart), but does not annihilate \(T_5\) by the splitter result above.

   If at most five distinct numerical clocks are present on that prefix, scalar \(P_4\) probes kill the aggregate coefficients at each. Any remaining overlap can only be between a clean and a dirty group; there are at most two such labels. The two genuine probes \(\mathbf h,C\mathbf h\in T_4\) kill their separate dirty coefficients as well. Thus the difference functional would vanish on the whole earlier coarse span, impossible.

   The only other case uses six distinct clocks \(0,u\), and all four dirty labels \(z\). The scalar annihilator of degree at most four there is the single barycentric line for the hull \(X(X-u)F(X)\). Its actual \(\mathbf h,C\mathbf h\) tests imply
   \[
               \sum_z \frac{h_z z^j}{z(z-u)F'(z)}=0,\qquad j=0,1.
   \]
   Therefore \(h_z/[z(z-u)]\) is affine on the four labels (its degree-three interpolation coefficients of degrees three and two vanish successively by barycentric pairing). Let \(P\in P_3\) interpolate the four \(h_z\). Then \(P=X(X-u)R\) with \(\deg R\le1\). The genuine grade-three contrast \(P(\mathbf c)-\mathbf h\) vanishes numerically through the first nonorigin clean row \(u\), as does its clock lift, because \(P(0)=P(u)=0\) and every dirty row has \(h_z=P(z)\). Their two actual primitive reads in grades four and five force \(JP(u)=J[XP](u)=0\). After scaling by \(u\ne0\), the \(X(1-X)\) Gram on affine polynomials gives \(R=0\), contrary to the nonzero defects. This argument works unchanged in reflected chronology with the actual weighted flags; it uses neither a fake reverse tableau order nor a grade-six clean assertion.

Thus the two end runs before their respective first nonorigin clean rows are each made of **three or four single occurrences**. At most two of the eight dirty physical stages lie in the interval between these two clean rows. There are no sign or numerical-order restrictions on their dirty clocks.

These are exact restrictions on the still-open all-cancelling face. The first-occurrence, completion and two-sided endpoint cases are not amalgamated into an unconditional fifteen-stage exclusion.

The [Lean scalar receipt](../../lean/RKCert/Research/DIRK12CancellingPairFrontGate.lean) checks that the two true primitive equations at a nonzero clean clock force the affine factor to vanish. It checks on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The flag, endpoint and physical chronology arguments are source proofs, not end-to-end Lean exclusions.
