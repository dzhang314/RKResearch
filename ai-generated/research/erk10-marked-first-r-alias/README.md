# A genuinely marked first row and its next-row gate at ERK10

This is an actual forward **ingredient**, not an order-ten tableau or a bound improvement. With the [canonical six opening clocks](../erk10-canonical-cubic-rank/README.md), one can release the literal cubic cross block at the first new physical row. The first new row can be genuinely marked through actual size-six profiles, although the particular two-row continuation below is blocked. The unrestricted order-ten interval remains 14–15.

## The equality-compatible changed cross block

Over characteristic zero, suppose a fourteen-stage order-ten candidate keeps the canonical six old physical rows but may change its high cross coefficients. Retain only high derivative purity through size four, not through five. By the four lower pivots of the [fixed-cubic rank note](../erk10-canonical-cubic-rank/README.md), the actual pure \(F_5\) restricts onto the five nonorigin old coordinates: in the generic old branch the fifth independent old column comes from \(C\mathbf Q\) or \(C\mathbf V\); in the point branch it comes from the nonzero \(J_r\) response on a true \(H_5\) source. These are old-column statements independent of the high cross block. At a true equality candidate \(\dim F_5=5\); hence the pure high value of each row \(i\) is a linear functional \(R_i\) of the old pure values through grade five.

The early old pure columns at \(e,s\) are annihilated by \(R_i\), since the high stage is actually pure through size four. The old nonorigin clean coordinates are \(p,q,r\). Transport of the two clean grade-four axes by \(C\) gives
\[
            R_i(\operatorname{diag}(p,q,r)-c_i I)
                           \bigm|_{\operatorname{span}(\mathbf Q,\mathbf V)}=0 .
\]
For \(c_i\) off \(p,q,r\) this determines
\(R_i=\lambda_i\ell(\operatorname{diag}(p,q,r)-c_iI)^{-1}\).
If \(c_i\) is one of those old clocks and the corresponding component of \(\ell\) is nonzero, \(R_i\) instead is a multiple of that physical evaluation.

Let \(E_{\rm old}\) evaluate polynomials on the actual six old clocks, and \(E_i\) on \(c_i\). If \(B\) is the physical strict new/high block, set
\[
      P_i=J_{c_i}-R_i E_{\rm old}J,\qquad Q_i=E_i-R_i E_{\rm old}.
\]
All actual unary inputs through size four uniquely determine the new row's six old taps:
\[
        A_{i,{\rm old}}
           = R_i A_{\rm old}-\sum_{j<i}B_{ij}R_j
                  +\left(P_i-\sum_{j<i}B_{ij}Q_j\right)\Pi .
\]
Indeed the old numerical span of rooted derivatives through four consists of the four cubic clock models plus two independent early pure columns, spanning all six positions. Substituting this literal formula into inputs of size five gives the additional necessary linear gate
\[
                   \left(P_i-\sum_{j<i}B_{ij}Q_j\right)|_{H_5}=0 .
\]
This is a condition on actual earlier reads, not a mechanism for adding a virtual row.

## Literal first marked row

Use \(p=1,\ q=33/100,\ r=3/4,\ e=1/7,\ f=65625/63382\). On \(X\mathcal P_3\) the unscaled annihilator \(\ell\) is \(J_r\). To check this, the three clean evaluation coefficients of \(J_r\Pi\) are \((-81/4288,78125/165088,43/224)\); they annihilate the actual \(\mathbf Q,\mathbf V\), and \(J_r[X(X-p)(X-q)(X-r)]=0\). The old \(r\) donor is **not** locally pure through size five: its rough tap and cubic moment defect are \(-2187/5504\) and \(9873/220160\), respectively.

Take the actual first new row at the old scalar clock \(r\), with \(R_1=E_r/2\) on the low pure coordinates. Its literal old row is
\[
                        A_{1,{\rm old}}=(A_r+J_r\Pi)/2 .
\]
It is physically distinct from the old \(r\) row and from the integrated cubic row. For every actual rooted profile through size six it equals the ideal value at \(r\) plus **one half** the old row's actual pure defect. The independent replay checks all 37 profiles exactly. This produces a genuine non-pure new row, using no prospective high input. The newly realized high probe is \(Q_1=E_r/2\) on the scalar source space.

For a second high row at an off-old clock \(z\), the new size-five gate requires \(J_z\) in the span of \(J_r,E_r,\ell\,(\operatorname{diag}(p,q,r)-zI)^{-1}E_{\rm old}J\). For this specific first row the four-by-four moment determinant of those rows, clearing the last fraction by \(\prod_{c=p,q,r}(c-z)\), is exactly
\[
                \frac{2187 z^2(z-1)(4z-3)^3(100z-33)}{671088640000}.
\]
Thus the first distinctly off-old second clock in this sample cannot be nonzero. This is a blocked continuation of a genuine first ingredient, not a claim that any changed cross block is impossible.

## General obstruction to a nonzero off-old first row

Under the stated canonical opening and high purity through size four, an off-old first row with nonzero clock \(a\) cannot satisfy the necessary gate, even if its cross block is released. Normalize \(p=1\) by formal clock scaling. Let \(\ell=\ell_0+f\ell_1\) after dropping a common nonzero scalar. Write \(L_j=\ell_j(\operatorname{diag}(1,q,r)-aI)^{-1}E_{\rm old}J\) times \(\prod_{c=1,q,r}(c-a)\), and \(M_j=\ell_j E_{\rm old}\). On the four moment coordinates \(X,X^2,X^3,X^4\), a solution of the first row's gate would represent \(J_a\) with coefficients
\[
                (u,\; fu,\; v,\; fv)
                  \quad\hbox{in the columns }(L_0,L_1,M_0,M_1).
\]
Consequently the determinant replacing \(M_1\) by \(J_a\) must be \(f\) times the one replacing \(M_0\), by determinant multilinearity. This implication does **not** divide by the original determinant.

Exact independent polynomial calculation gives the replacement of \(M_0\) identically zero, while that of \(M_1\) is
\[
 \frac{a^2q^7r^3(q-a)^2(r-a)^3(a-1)^2(q-1)^6(q-r)^2(r-1)^2}{5},
\]
nonzero for distinct \(1,q,r\) and a nonzero distinct \(a\). The contrast therefore needs a different opening family, a low-clock collision, or earlier high impurity in order even to pass this first causal rank gate. The example above uses such a collision correctly.

From this directory:

    python3 -B replay.py
    python3 -B noncolliding.py
    sha256sum -c sources.sha256

The small literal profile replay uses exact fractions and SymPy for the determinant; the general symbolic calculation uses exact multivariate polynomials. No end-to-end Lean theorem is asserted for the changed block.
