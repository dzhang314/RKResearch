# Paid support and kernel replay for the two variable eight-site closures

The [two-repeat proof](../dirk12-fifteen-rank3-invisible-four-ghost-variable-two-repeats/README.md) and the [three-pair proof](README.md) use true physical reverse chronology in the same genuine order-twelve equality frame. This ledger separates each cancelling correction from the scalar conclusion. A true weighted defect of grade \(j\) is in \(\mathcal B_j\), and the scalar primitive of a weighted input of grade at most four has its pure discrepancy in \(\mathcal B_5\). The two actual lifts \(N,Y\) each cost one grade. All ghost slots in \(\mathcal B_5\) are zero.

| Input or cut | Correction and actual zero prefix | Exact paid implication |
| --- | --- | --- |
| Two-repeat first singleton \(u\) | Bare \(\mathbf W(X(X-d)(X-v))\) is zero before \(u\), not at \(u\). | The true grade-five commutator has only the diagonal term there, and forces literal diagonal zero. The separate grade-four and grade-five primitive errors on the input and its clock lift vanish at the singleton, yielding both Radau moments. |
| Two-repeat spending cuts | Bare grade-four \(\mathbf W(R)\) is zero through the spent block. Before \(u\) use \(R=X(X-s)(X-t)^2\); before \(w\) use \(R=X(X-d)(X-v)(X-u)\). | The literal \(T_6\) block indicator pairs with the actual grade-five error, giving \(m_s JR(s)=0\). A zero-mass interior repeat would leave the other seven fixed labels and violate the Radau residue; a zero-mass reflected endpoint \(1\) includes the literal ordinary origin and cannot yet have completed. |
| Two-repeat final mask | Subtract \(\alpha\mathbf G+\beta\mathbf H\in\mathcal B_4\) from \(\mathbf W(S)\) to match the two earlier \(d\)-rows. Ghosts and origin vanish automatically, and \(S(u)=0\). | The clean grade-five read at \(u\) gives zero actual primitive because \(JS(u)=0\), and its nonzero literal \(v\)-tap removes the last preceding obstruction. The clean read at \(w\) therefore has only its diagonal. |
| Three-pair first singleton after two labels | Subtract \(\mathbf G\in\mathcal B_3\) from a weighted cubic \(\mathbf W(S)\) matching the two earlier normalized amplitudes. A zero-mass pair has equal normalized values on both rows even when spent. | The commutator costs two grades, and its zero at the singleton makes both actual primitive reads zero, whether the input itself or the diagonal there is zero. This yields the two independent moment tests for every cubic in the affine interpolation line. |
| Three-pair spending bound before \(a\) | Bare grade-four \(\mathbf W(X\prod_j(X-z_j))\) is zero through any completed repeat before \(a\). | At a nonzero-mass spent pair the grade-\(6+5\) cut gives a double root of the primitive. Together with the double origin, at most one such spending is possible before \(a\). |
| Three-pair first nonzero-mass spending | Choose \(R\in X(X-s)(X-a)P_1\) and subtract an actual \(\boldsymbol\eta\in\mathcal B_4\) zero on the whole spent pair \(s\), matching the two untouched pair readings. Its normalized data there impose at most one scalar condition. This corrected input vanishes through both the spending event and \(a\). | The genuine grade-five error at \(a\) and its \(T_6\) block cut at \(s\) force \(JR\) to have three double roots \(0,a,s\), impossible in degree at most five. Zero-mass pairs, including a possible reflected endpoint, remain uniform masks and never require a division by their aggregate mass. |
| Three-pair final mask | On \(X(X-a)P_2\) retain the profiles whose three site readings lie in the rank-two image of \(\mathcal B_4\). Subtract the corresponding actual \(\boldsymbol\eta\in\mathcal B_4\); the input is zero at every row before \(b\). | The singleton \(a\) supplies \(JS(a)=0\). The two-dimensional primitive space with double roots \(0,a\) gives the two explicit tests at singleton \(b\), where the exact paid primitive can only use its actual diagonal. |

Neither the polynomial root count nor the definite-sign tests assume variable clock positivity. For the spending polynomial the exact primitive at \(s\) is
\[
                           -s^3\bigl(s^2+5(s-2t)^2\bigr)/120,
\]
nonzero for \(s\ne0\) over an ordered field. In the three-pair proof, all stage deductions use real scalar quadrature and this definite-sign test, but no modular grid specialization. In the two-repeat proof, the only modular part is the already frozen \(\pmod{1013}\) fixed-grid guard for a zero-mass interior label.

## Verified native scope

From the pinned ai-generated/lean environment:

    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenVariableGhostScalar
    lake env lean AuditDIRKOrderTwelveFifteenVariableGhostScalar.lean

The native module checks the two cubic moment line and donor tests, the Radau quartic factor and donor guards, the ordered-field spending sign, the actual polynomial three-double-root impossibility, and the actual polynomial two-diagonal-test contradiction. The typed import audit passed Lean/Mathlib 4.36.0 with only propext, Classical.choice and Quot.sound. Its exact output is in mathlib-4.36-replay.txt. The independent fixed-grid coefficient module is core-only and passed 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 with no axioms. The rank, causal prefixes, and their connection to true rooted flags in the two notes are mathematical, not a complete native exclusion.
