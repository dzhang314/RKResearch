# Exact cubic-decoder obstruction on the ten-site DIRK10 mesh

This excludes the specified **six-opening, three-literal-merge, rank-one cubic decoder** at width 12 over \(\mathbb Z[1/210]\). It uses necessary **actual rooted** source gates, not the stronger separate top payment ansatz. It is not a lower bound for arbitrary twelve-stage DIRK10 tableaux. The [factorial-localized width-13 witness](../dirk10-factorial-thirteen-compact/README.md) is unaffected.

## Exact scope

1. Use the ten distinct output sites \(j/6\), \(-3\le j\le 6\), with their integrated degree-nine interpolation weights. Attach the zero site's weight to an old, literal zero row. The other nine sites have reflected order \((1,-1/2,-1/3,e_1,e_2,e_3,r,p,u)\). The last six entries permute the remaining six sites; the three ports \(u,p,r\) occupy the final three positions in this order.
2. The actual six opening rows, in forward chronological order, have clocks \(0,d,s,u,p,r\) with \(d=u/4,\ s=u/2\). The row at \(d\) is trapezoidal on \(0,d\); those at \(s,u\) are Simpson on \(0,d,s\) and \(0,s,u\), respectively. This is a cubic decoder \(\Pi\) on the four literal retained port rows \(0,u,p,r\); in particular the \(s\) slot is not a decoder column. A shared clock between \(s\) and \(r\) does not identify these two physical rows.
3. Write \(E\) for evaluation on high sites, \(J\) for integration from \(0\), and \(T\) for the forward high block (write \(K\) for its transpose after reflection). The old \(u,p,r\) rows and all high rows use the common adjusted primitive \(EJ\Pi+\boldsymbol\eta\sigma\), with \(\sigma=G_u-J_u\Pi\) and \(\eta_u=1\). In an enlarged before-merge tableau, the low-to-high block is \((EJ-T E)\Pi+\boldsymbol\eta\sigma\). The three copied high rows are redirected to the old \(u,p,r\) rows. With the three appended port copies first in the forward high chronology, arbitrary within-port taps are allowed; they cancel with the corresponding decoder taps upon this redirection. No extra rank or zero restrictions on the later reflected nonport rows are added.
4. Write \(\mathbf x,\mathbf y=\mathbf1-\mathbf x,\mathbf w\) for the reflected high clocks and weights, and \(\mathbf W_j=\mathbf w\odot\mathbf y^j\). The reverse leading ansatz is \(K\mathbf W_0=\mathbf W_1,\ K\mathbf W_1=\mathbf W_2/2,\ K\mathbf W_2=\mathbf W_3/3+\mathbf U\), with \(\langle\mathbf U,\mathbf x^j\rangle=0\) for \(1\le j\le6\). This low leading ansatz is a hypothesis; no top separability or upper-order simplifying assumption is imposed.

This makes a nominal \(6+9-3=12\) literal stages. The proof does not treat another mesh, different first reflected donors, a different protected opening, a nonconsecutive high-port block, a rank-two decoder injection, or different reverse leading conditions (including cubic densities outside the stated polynomial annihilator). The exact census excludes the full rational amplitude family under the stated hypotheses, not arbitrary order-ten methods over the localization.

## Actual rooted discrepancy context

For any linear combination \(d\) of rooted stage vectors of the same size \(m\), write \(d_L,d_H\) for its actual old and high stages, and \(p\) for the corresponding linear combination of pure monomial profiles. Set
\[
 \boldsymbol\Delta=d_H-Ep,\qquad \rho=\Pi d_L-p,\qquad v=\sigma d_L.
\]
All high profiles through size five are pure. The old decoder rows \(0,u,p,r\) are likewise honest through size five: the decoder is exact on pure inputs of size at most four, the Simpson row at \(u\) is honest through size five, and \(\sigma\) vanishes on those inputs. A simultaneous tree-size induction proves this directly. Equality of copied and retained port profiles also follows by induction on tree size, since the difference reads only earlier-in-tree differences in the three port columns.

In size five, write \(d_*\) for the size-five bush. Its projected discrepancy is \(-F\) for \(F(X)=X(X-u)(X-p)(X-r)\), and its high deviation is zero. A second size-five combination \(d_0\) has \(\rho=0,\boldsymbol\Delta=0,v=1\) and pure profile zero. To see this, take the tree obtained by two unary extensions of the size-three bush, normalize its pure profile to \(X^4\), and subtract the size-five bush. The difference is zero at all decoder positions but at \(s\) is \(12G_{s,d}(d^3/6)\ne0\), since the earlier trapezoidal stage has cubic defect \(d^3/6\). The coefficient \(\sigma_s=2u/3\ne0\) reads this difference, so it can be normalized to give the asserted \(v=1\).

The size-six pure-zero combination \(A d_0\) has actual high deviation \(\boldsymbol\eta\) and old projected discrepancy \(Q_\eta\), the cubic interpolant of \(0,\eta_u,\eta_p,\eta_r\) at \(0,u,p,r\). Adding \(j\) sibling leaves to the root tests pure \(x^j\) multiplication. Consequently its actual rooted order equations give \(\boldsymbol\eta\perp\mathbf W_0,\ldots,\mathbf W_4\).

For a general size-\(m\) combination \(d\), adjoining one unary parent gives the actual high deviation
\[
 \boldsymbol\Delta_{A d}=EJ\rho+\boldsymbol\eta v+T(\boldsymbol\Delta-E\rho).
\]
No separation of mixed paths is used: this is an identity of actual high rows. For \(m+1+j\le10\), the size-\(m+1\) rooted order equation with \(j\) extra sibling leaves gives \(\langle\mathbf W_j,\boldsymbol\Delta_{A d}\rangle=0\), equivalently by linear combinations of leaf additions using \(\mathbf y^j\). The order equation at \(d\) with \(j+1\) leaves gives \(\langle\mathbf W_{j+1},\boldsymbol\Delta\rangle=0\). Integration by parts on the exact scalar quadrature gives \(\langle\mathbf W_j,EJ\rho\rangle=\langle\mathbf W_{j+1}/(j+1),E\rho\rangle\): the degree is at most nine, \(\rho(0)=0\), and the old origin contributes zero. Thus, for \(j\le4\),
\[
 \big\langle K\mathbf W_j-\mathbf W_{j+1}/(j+1),
                  \boldsymbol\Delta-E\rho\big\rangle=0 .
\]
Taking \(j=2\) on \(A d_0\) and on that combination with one extra sibling leaf gives \(\boldsymbol\eta\perp\mathbf U,\mathbf y\odot\mathbf U\), because the decoded discrepancies in each case have degree at most six and zero constant. In the second case the actual high deviation is \(\mathbf x\odot\boldsymbol\eta\), and then \(\mathbf y=\mathbf1-\mathbf x\).

Put \(\mathbf h=K\mathbf W_3-\mathbf W_4/4\) and \(\mathbf k=K\mathbf U\). Taking \(j=3\) shows that \(\mathbf h\) annihilates each of \(EF,E(XF),\boldsymbol\eta-EQ_\eta\). For \(EF\) use \(d_*\). For \(E(XF)\) use the size-six bush, whose projected discrepancy is \(-F\) times a monic linear polynomial and whose high deviation is zero. For the third vector use \(A d_0\) as above. To check \(\mathbf k\), take \(j=2\) in the same contextual identity but on \(A d\), where \(d\) is any of these size-five or size-six combinations. The decoded discrepancy of \(A d\), like \(J\rho\), has degree at most six and zero constant, so both are annihilated by \(\mathbf U\). The injection term \(\boldsymbol\eta v\) is annihilated too. The surviving term is exactly \(\langle K\mathbf U,\boldsymbol\Delta-E\rho\rangle=0\). This proves the same three orthogonalities for \(\mathbf k\) using only actual rooted equations; it does not assert separate primitive and transit payment.

## Causal and mixed scalar gates

Put \(F_3=X(X-u)(X-p)\). Causality of the old \(p\) row at the future decoder slot \(r\) requires
\[
  J_p F_3-\eta_p J_u F_3=0,\qquad
  J_u F_3=\frac{u^3(2p-u)}{12},
  \quad J_p F_3=\frac{p^3(2u-p)}{12}.
\]
The two zero-pivot pairs \(p=u/2\) have nonzero target. For the other pairs the ratio fixes \(\eta_p\).

The reflection begins at physical 1 so its first row is zero, and the second reflected row has forced diagonal \(y_1/2\) from the two leading conditions. Therefore \(U(1)=0\) and \(U(x_1)=w_1y_1^3/6\ne0\), where \(x_1=-1/2\). If \(P_8\) is the nodal hull on all eight proper high sites, their exact cofactor description is
\[
        U_i=\frac{\alpha[1+t(x_i-x_1)]}{x_iP'_8(x_i)},
\]
with \(\alpha\) fixed by the second row as above. This affine parameter covers every projective direction with the required nonzero normalized coordinate; the direction that vanishes at \(x_1\) is incompatible. Meeting the first five \(\boldsymbol\eta\)-orthogonalities means exactly
\[
 \eta_i=f(x_i)/(w_iP'_9(x_i)),\qquad f\in P_3,
\]
by cofactor interpolation on all nine high sites. The conditions at \(u,p\) leave \(f=f_0+(X-u)(X-p)(a+bX)\), where \(f_0\) is linear. The two remaining conditions \(\boldsymbol\eta\perp\mathbf U,\mathbf y\odot\mathbf U\) are a \(2\times2\) system with coefficients affine in \(t\); its determinants are checked even at singular directions.

Form \(\mathbf V\) from \(\boldsymbol\eta-EQ_\eta\) by subtracting \(EF\) times the linear interpolant of its two ratios at \(e_2,e_3\). Both ratios are well-defined because these are nonports. Then \(\mathbf V\) vanishes at \(u,p,r,e_2,e_3\), and necessarily annihilates \(\mathbf h,\mathbf k\). On the first four nonports all actual reverse rows read only the first four nonport columns. Let \(G\in P_3\) interpolate \(U_i/w_i\) on those four sites, and let \(g_2,g_3\) be the final two coefficients of \(G(1-Y)\). The leading actions imply on these rows
\[
  \mathbf k=\mathbf w\odot E J^*G+g_2\mathbf U+g_3\mathbf h,\qquad
  J^*G(X)=\int_X^1G(s)\,ds.
\]
Also \(\mathbf V\) annihilates \(\mathbf U\), since both \(Q_\eta\) and \(F\) times a linear factor have zero constant and degree at most six. Consequently the necessary mixed gate is \(\langle\mathbf V,\mathbf w\odot EJ^*G\rangle=0\). Clearing the determinant of the eta solve gives a cubic in \(t\) with rational coefficients.

## Exact tally and receipts

There are \(6\cdot5\cdot4\cdot3=360\) chronology classes: ordered \(u,p,r\), with a choice of \(e_1\) from the three nonports left. Reversing \(e_2,e_3\) does not change the necessary gate or its test; literal tableaus need not be equal. The two zero-causal-pivot pairs account for 24 classes. Among the other 336:

- 282 have a cubic with no rational root, each with a checked modular no-root certificate and nonzero leading coefficient at the prime.
- All other 54 have just \(t=2/3\) as a regular rational root, with a checked nonsquare quadratic factor. Each resulting literal \(s\)-column tap has denominator involving an outside prime: the [per-branch receipts](exact-gates.jsonl) record a reduced literal tap and the factor of its denominator left after stripping \(2,3,5,7\). The first forbidden prime for each recorded tap is 11 in 21 branches, 13 in six, 17 in six, 29 in six, 109 in six, 199 in three, and 347 in six; the full reduced denominator is also printed. The tap is precisely \((2u/3)\eta_i\) at some old or retained high row. Neither decoder taps nor high-to-high redirection touch the \(s\) column, so this denominator cannot be an artifact of a choice of coordinates.
- There are separately 22 rational singular \((u,p,t)\) intercepts in the eta solve, all inconsistent. These are not extra chronology classes. There are no identity-zero mixed polynomials, compatible singular branches, or unhandled degenerate projection cases in this census. In particular a zero constructed \(\mathbf V\), if it occurs at an isolated parameter, is already covered by testing all roots of the mixed polynomial.

Run with Python 3 and SymPy:

    python3 -B check.py --emit /tmp/dirk10-cubic-gates.jsonl
    cmp exact-gates.jsonl /tmp/dirk10-cubic-gates.jsonl
    sha256sum -c sources.sha256

The script verifies factor multiplication, residual roots, modular primality and complete no-root tables, nonsquare bounds, and the exact singular systems. It does not rely on a numerical fit. The mathematical rooted reduction and the arithmetic replay are distinct parts of this scoped proof.

The dependency-free core module is
\(\textsf{RKResearch.Certified.DIRK10CubicDecoderTenMeshArithmetic}\).
It checks the 282 modular cubics, 54 nonsquares, 54 unpaid fractions, 22
singular nonzeros, and two nonzero causal targets on Lean 4.34.1, 4.35.0,
4.36.0, and 4.37.0-rc1. See [the replay log](lean-tested.log) for the
per-release axiom audit; there are only standard Lean axioms. The
arithmetic module does not claim native formalization of the rooted
reduction. To regenerate it:

    python3 -B generate-lean.py /tmp/DIRK10CubicDecoderTenMeshArithmetic.lean
    cmp /tmp/DIRK10CubicDecoderTenMeshArithmetic.lean \
        ../../lean/RKCert/ReviewedNative/DIRK10CubicDecoderTenMeshArithmetic.lean
