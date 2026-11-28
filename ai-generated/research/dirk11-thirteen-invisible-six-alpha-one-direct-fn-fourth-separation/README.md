# An exact fourth-clean separation identity in the live direct Fn chart

**Result.** In the live reciprocal direct \(F_n\) branch of
the normalized no-late invisible-six DIRK11/13 chart with
\(\alpha=1,\beta=1\) or 2, the first physical middle ghost
\(x\) cannot coincide numerically with the fourth regular
reverse clock \(V\). An exact product formula identifies
when the fourth diagonal can vanish. This uses
characteristic zero but no ordering
of the field. It is not a global stage exclusion.

Use the actual rows and symbols of the
[gap-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md),
the [small direct contacts](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-small-contacts/README.md),
and the [slope-minus-one exclusion](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one/README.md).
In particular, in the remaining direct profile,
\(r^2-3s\), \(r^2-6s\), \(2r^2-9s\) and \(1+\ell_1\)
are live; the first comes from the small finite closure,
the next two from the old guard identities, and the last
from the separately certified finite slope chart.

Write \(l=\ell_1\ne0\), \(\ell=l(Y-z)\) and
\(\delta=1/4-l\). Use \(P=Y(Y^2+rY+s)\), \(P_0=YR\),
and the true \(W_0=IP_0/P\bmod R\).
The exact polynomial quotients
\[
 F=\frac{W_0}{Y-z},\qquad B_0=\frac{IP_0-PW_0}{P_0}
\]
are at most affine. The first numerator vanishes at \(z\).
The second vanishes at 0 and the three distinct old roots
by the old fit. **pure-fit.py** independently computes
their exact coefficients in the generic rational old
parameterization and verifies
\[
 \delta F-lB_0=\Lambda Y,\qquad
 \Lambda=-\frac{(1+l)(r^2-6s)}{10(2r^2-9s)} .
\]
All divisions in the generic rational calculation
are by factors already known live in the old-fit
ledger; the inversion modulo \(R\) divides only by
the live multiplication determinant of \(m\).
In particular \(\Lambda\ne0\).

Put \(K=K_*\) from the true matched column \(D\),
\(k=G_V/b_V\), and \(\omega=(1+l)K-\delta\).
Integration by parts and the exact old fit give
\[
 (1+l)\rho=\ell^2+\delta W_0,\quad
 (1+l)L=(Y-z)\,[\ell+\omega F].
\]
Since \(L=\lambda(Y-z)(Y-x)\) with \(\lambda\ne0\),
\(\omega=0\) would give \(x=z\). Thus \(\omega\)
is live, and
\[
 (1+l)\lambda(Y-x)=l(Y-z)+\omega F(Y).
\]
The known literal quartet at \(V\) gives
\(IP_0(V)-k W_0(V)=d_V P_0(V)\). Since
\((V-z)(k-P(V))=K P_0(V)\), this is
\[
 d_V=B_0(V)-K F(V).
\]
It holds even if \(V=z\).

The already established \(ND=0\) at \(V\) gives
\(L(V)k=IQ_4(V)\).
Use \(IQ_4=(Y-z)IP-I^2P+K IP_0\) and
\((1+l)(I^2P-\rho k)=\ell(IP-\ell k)+
\delta(IP_0-W_0 k)\) at this sample. The result, after
cancelling the live \(P_0(V)\), is exactly
\[
 (V-z)(\delta-lK)+\omega d_V=0.
\]
Now substitute \(d_V=B_0(V)-K F(V)\) and
\(lB_0=\delta F-\Lambda Y\) into the left-hand side.
It is the same as
\[
 (\delta-lK)(1+l)\lambda(V-x)=\Lambda\omega V.
\]
This forces both \(\delta-lK\ne0\) and \(V\ne x\).
Multiplying by \(V-z\) and using the adjacent scalar
equation, then cancelling \(\omega(1+l)\), gives
\[
 \boxed{\lambda(V-x)d_V
       =\frac{r^2-6s}{10(2r^2-9s)}\,V(V-z).}
\]
Thus \(d_V=0\) iff \(V=z\) within this remaining
direct profile, without initially assuming either
clock difference or the diagonal is live. In the
separately established nonzero-fourth slice the right
side is nonzero.

Run **python3 pure-fit.py** with SymPy for the exact
rational coefficient audit. The adjacent derivation
above is a written consequence of the actual rooted
matrices and does not posit further independent order
conditions. The unrestricted real order-eleven stage
interval remains **13–14**.
