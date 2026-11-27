# The actual grade-five rank excludes the fixed six-opening cubic decoder at ERK10

No fourteen-stage order-ten explicit method can use the **fixed canonical six-opening, literal cubic-decoder** architecture below, in characteristic zero. The conclusion holds for every later high clock pattern, chronology, score sign, or zero score. It subsumes the earlier [two-pair](../erk149-two-pair-dormant-aggregate/README.md) and [one-triple](../erk149-one-triple/README.md) chronology obstructions in this particular cut, by a different argument. It does not impose literal co-order or assume anything about score placement, and does not exclude a changed prefix or cross block. The unrestricted ERK10 interval remains **14–15**.

## Precise architecture and four independent lower pure vectors

The first six physical clocks are \(0,e,s=2p/3,p,q,r\), with \(e,p,q,r\ne0\) and \(0,p,q,r\) pairwise distinct. They have the same canonical row formulas as the [rational order-nine construction](../erk9-fourteen-rational-triple/README.md): the row at \(e\) reads only the origin; the row at \(s\) reads \(e\) with coefficient \(s^2/(2e)\); the row at \(p\) reads \(s\) with coefficient \(3p/4\); the row at \(q\) uses only \(0,s,p\) and exact moments on \(1,X,X^2\); the row at \(r\) uses only \(0,s,p,q\) and the same three moment conditions, with its last tap free. Exact moments on \(1,X,X^2\) include row-sum consistency. The old aperture \(\Pi\) is cubic interpolation at the actual rows \(0,p,q,r\). The new high block \(B\) is any strictly lower triangular matrix, and its actual low-to-high cross block must be
\[
                             (EJ-BE)\Pi ,
\]
where \(E\) evaluates at the physical high clocks and \(J\) integrates from zero. The remaining rows need not have distinct clocks. This is a **literal row identity on coefficients**, not a property only on low-size vectors. The output weights can be arbitrary.

Each of the three clean old donor rows \(p,q,r\) reproduces the ideal derivative models of all trees through size four. The rough stage \(s\) is exact up through size three, and these donors have no tap to the preceding rough stage \(e\), so their exact first three monomial moments have this ordinary-tree consequence. Thus \(\Pi\) realizes the ideal cubic tree model on sizes at most four. By strict high induction the literal cross block then makes all high derivative profiles ideal through size five; to obtain a size-five derivative, each child primitive input has size at most four. In particular a pure rooted vector of grade at most four vanishes at every high coordinate. Grade is tree size minus one.

Use \(C=\operatorname{diag}(\mathbf c)\). Four explicit pure columns, of grades \(2,3,4,4\), are
\[
     \mathbf d=A\mathbf c-\mathbf c^{\odot2}/2,\qquad
     A\mathbf d,\qquad A^2\mathbf d,\qquad
     \mathbf D=A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4 .
\]
Here a column is pure when its formal tree-model polynomial is zero. Every monomial \(\mathbf c^{\odot k}\) is the actual \(k\)-leaf bush derivative, so the displayed model cancellations are true rooted linear combinations.

The first column is supported at the old \(e\) row with value \(-e^2/2\); the second is supported at old \(s\) with value \(-e s^2/4\). The third restricts on the clean donor coordinates to the second's nonzero value times
\(\mathbf V=(A_{i,s})_{i=p,q,r}\). The fourth restricts there to
\(\mathbf Q=(A\mathbf c^{\odot3}-\mathbf c^{\odot4}/4)|_{p,q,r}\). Explicitly,
\[
 V_p=3p/4,\quad V_q=3q^2(3p-2q)/(4p^2),\quad
 Q_p=-p^4/36,\quad Q_q=5pq^3/9-p^2q^2/3-q^4/4 .
\]
Their determinant \(Q_pV_q-Q_qV_p=3p q^2(p-q)^2/16\) is nonzero. This proves actual independence of all four columns via the two pivot rows \(e,s\) plus the two donor axes \(p,q\), irrespective of the last old tap.

Write \(\ell\) for the nonzero annihilating row of \(\mathbf Q,\mathbf V\) on \(p,q,r\), pulled back by polynomial evaluation on those nodes. In particular its \(r\)-coordinate is nonzero. For an actual size-five tree \(t\), write
\(\rho_t=g_t-\Pi\boldsymbol\Phi_t^{\rm old}\), where \(g_t(X)=|t|X^{|t|-1}/t!\). The actual span of these \(\rho_t\)'s is \(H_5=\ker\ell\) in \(X\mathcal P_3\), of dimension three. Indeed each of the two pure columns above interpolates the corresponding independent clean defect \(\mathbf Q,\mathbf V\) into this source space, and a size-five bush contributes a monic quartic minus a cubic. Conversely, a non-unary size-five root has only children of size at most three and is ideal at the clean old donors; a unary input of size four can differ from its ideal scalar plus the first rough column only by the second rough column. Its clean old primitive defects therefore use precisely \(\mathbf Q,\mathbf V\). Every source vanishes at 0 because \(\Pi\) includes the actual origin.

## Grade five and the first two physical high rows

Use the **actual** [fourteen-stage equality ledger](../ERK10-FOURTEEN-STAGE-EQUALITY.md), which implies \(\dim F_5=5\) for true rooted order ten, where \(F_5\) is the pure numerical span through grade five. This is the only global equality input to the rank argument.

### Nonpoint annihilator \(\ell\not\propto E_r\)

At least one of the two clean columns \(\operatorname{diag}(p,q,r)\mathbf Q,\operatorname{diag}(p,q,r)\mathbf V\) escapes their span. Otherwise \(\ell\) is a left eigenrow of the diagonal on three distinct nodes, so it is a single coordinate evaluation. Its nonzero \(r\)-coordinate would force \(\ell\propto E_r\), a contradiction. The escaped vector is realized by clock-multiplying the corresponding **actual** grade-four pure column by \(C\), which raises grade by one and leaves all its high entries zero. Together with the four old pure columns this gives **five independent old-only vectors**. Thus the full \(F_5\) is supported in the old prefix. No genuine pure size-six residue may be nonzero at any high row.

Let \(a\) be the clock of the actual first high row. Since \(B\) is empty there, its size-six pure residue for a unary child with source \(f\in H_5\) is \(-J_a f\). If \(a=0\), the entire physical row is identical to the origin (its cross block is \(J_0\Pi=0\)), so it can be merged, impossible at the fourteen-stage floor. Otherwise \(J_a\) on \(X\mathcal P_3\) is nonzero, and its vanishing on \(H_5\) identifies \(H_5=\ker J_a\).

Let \(b\) be the clock of the actual second high row and \(k\) its literal high tap to the first. Those same pure size-six equations now say that \(J_b-kE_a\) annihilates \(H_5\), hence is proportional to \(J_a\). On the inputs \(X,X^2,X^3\), the exact determinant is
\[
                 \det(J_a,E_a,J_b)
                          =a^4 b^2(a-b)^2/24 .
\]
It forces \(b=0\) or \(b=a\). In either case \(J_b|_{H_5}=0\), whereas \(E_a\) and \(J_a\) are independent (minor on \(X,X^2\) is \(a^4/6\)). Thus \(k=0\). If \(b=0\) the second high row duplicates the origin; if \(b=a\) it duplicates the first high row. These are literal strict-row equalities, not only root-grade aliases.

### Point annihilator \(\ell\propto E_r\)

Now \(Q_r=V_r=0\), and the old donor \(r\) is literally the row \(J_r\Pi\): it uses only \(0,p,q\) and agrees with \(J_r\) on \(1,X,X^2,X^3\). The equality is obtained coefficient-wise by cubic interpolation; both sides use only \(0,p,q,r\) and the actual coefficient on \(r\) is zero. Here \(H_5=X(X-r)\mathcal P_2\). The four independent grade-four pure columns vanish not only at all high rows but also at the old **physical** row \(r\).

Project the actual \(F_5\) onto the two coordinates old \(r\) and first high \(a\). For the pure size-six unary defects based on actual size-five sources \(f\), these two entries are \((-J_r f,-J_a f)\) because the literal old \(r\) row is \(J_r\Pi\) and the first high row has no preceding high input. On \(X(X-r),X^2(X-r)\) their primitive functionals have the signed minor
\[
     J_a[X(X-r)]J_r[X^2(X-r)]-J_a[X^2(X-r)]J_r[X(X-r)]
                    = a^2r^3(a-r)^2/24 .
\]
If \(a\ne0,r\) the projection has rank two, and its kernel already contains the four independent actual grade-four vectors. This gives \(\dim F_5\ge6\), contradicting the ledger. If \(a=0\) the old origin is duplicated. If \(a=r\), the first high row is literally \(J_r\Pi\), the actual old row \(r\) with zeros on the additional columns. An actual duplicate stage can be removed by transferring all its weights and subsequent taps to the identical earlier row. All rooted conditions are unchanged by a direct induction on the derivative recursion, so none of these duplicates can occur at the floor. This completes the point branch without assuming whether any other high clock collides with \(r\).

## Independent distinct-high moment check

For the separate generic route with all eight high clocks distinct, only the origin scored in the opening, and endpoint \(1\), one can see the conflict without the grade-five rank argument. The same clock multiplication of the lower two donor directions adds a third independent cubic source at direct size six, and the size-six bush supplies degree five. Later direct bushes of sizes seven and eight add degrees six and seven. Thus the actual direct source span through eight is \(X\mathcal P_6\). A length-two actual rooted clock/primitive word isolates the raw reverse moment defect \(\mathbf U=T(Y\mathbf w)-Y^2\mathbf w/2\): literal \(D(1)\) from the equality ledger pays the shorter fresh terms. Since the endpoint has zero defect, the seven distinct high interiors (nonzero and distinct from 1) give an invertible weighted evaluation of this seven-dimensional polynomial span, forcing \(\mathbf U=0\). The first reverse nonterminal row is either a zero-weight row whose only tap is killed by \(T\mathbf w=Y\mathbf w\) and can be pruned, or it has a nonzero weight and \(U=-w y^2/2\ne0\). Thus this separate moment-separation route also excludes the distinct high generic shape, but it does not by itself give the arbitrary shape/score theorem proved above.

## Reproduce

The standalone exact SymPy replay verifies every displayed determinant, all leading vector factors and the early row compatibility. Four characteristic-zero field statements are kernel-checked in Lean/Mathlib 4.36.0, with the typed standard-axiom transcript. The application of the graded equality rank and the actual tree-to-cubic-source calculation remain mathematical, not a claim that the entire lower-bound argument is formalized.

From ai-generated:

    python3 -B research/erk10-canonical-cubic-rank/replay.py
    sha256sum -c research/erk10-canonical-cubic-rank/sources.sha256

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.ERK10CanonicalCubicRankGate
    lake env lean AuditERK10CanonicalCubicRankGate.lean
