# The early ghost is a simple root of the true reverse quintic error

**Result.** In the normalized no-late invisible-six DIRK11/13
chart with live reciprocal multiplier, \(\alpha=\beta=1\)
and direct noncontact \(F_n\), the first-gap zero-weight
ghost clock \(z\) is a simple root of the actual compensated
weight-error polynomial \(Q_5\). This concerns a possible
repetition of a **formal root of \(Q_5\)**, not a collision
of distinct physical ghost clocks. Combined with the
[cubic leader proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-quintic-leader/README.md)
and the
[live late affine pivot](../dirk11-thirteen-invisible-six-alpha-one-live-fn-late-affine/README.md),
it gives three distinct roots in the coefficient field
for that remaining live, nonzero-regular-diagonal profile.
This is not a numerical stage-bound improvement.

Use the reverse notation and actual weighted columns from the
[gap-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md).
In particular \(P=Ym,\ P_0=YR,\ P_5=(Y-V)P_0\),
\(Q_4=(Y-z)P+K_*P_0\),
\(D=(Y-z)G-W(Q_4)\),
\(ND=G L-W(IQ_4)\), and \(L=\lambda(Y-z)(Y-x)\) with live
\(\lambda\). The distinct \(z,x\) are the first gap and first
middle ghosts. The true order-five weighted primitive error
is \(W(IP_5)-NW(P_5)=GQ_5+\theta H_{\rm bary}\).
It has roots \(z,x\), is cubic by the separate leader proof,
and \(D,W(P_5)\) are both zero through \(V\).

## 1. Repeat hypothesis and exact polynomial span

If \(z\) is a repeated root of \(Q_5\), then
\(Q_5=\sigma(Y-z)L\) for a live scalar \(\sigma\).
By literal donor chronology the \(N\)-images of \(D,W(P_5)\)
are zero on the same zero prefix. At the four weighted
ordinary samples \(v,u,w,V\), the actual relations give
\[
 IP_5=\sigma (Y-z)IQ_4+\theta YJ_4 .
\]
This uses only the live ordinary weights and the exact
reciprocal \(H_{\rm bary}/b_{\rm wt}=YJ_4\); no regular
diagonal is divided by. At polynomial zero each term
also vanishes, so the degree-at-most-six difference
is exactly \((a+bY)P_5\).

Set \(C_1=IP_5-YP_5/6,\ C_2=P_5-P_5'(0)YJ_4\).
For a polynomial \(F\) of degree at most five with zero
constant and linear terms, define
\[
 \operatorname{trim}(F)=(Y-z)F-[Y^6]\big((Y-z)F\big)\,Y P_5.
\]
This keeps only degrees at most five and preserves its
factor \(Y^2\). Comparing the two leaders (at \(Y^6\)
and \(Y\)) in the full difference gives the exact span
\[
 C_1=a C_2+\sigma\,\operatorname{trim}(IQ_4).
\]
The \(Y\) comparison uses \(J_4(0)=1\), and the fact that
both primitive terms are double at zero. All three
vectors have just four coefficient coordinates, in
powers \(Y^2,\ldots,Y^5\).

By linearity of trim, the four-column determinant with
columns
\[
 C_1,\quad C_2,\quad
 \operatorname{trim}\big(I[(Y-z)P]\big),\quad
 \operatorname{trim}(IP_0)
\]
must vanish. This is independent of \(K_*,x,t\).
In the scaled clock code the mark is cleared to
\(Z=qY-p\), and \(C_2\) is scaled by the nonzero
fourth power of the horizontal clock scale as in the
leader proof. This changes only common normalizations.
**coordinate-audit.py** checks the exact affine split,
the polynomial primitive coordinates and adjacent
division under four independent rational samples.

## 2. Exact support and saturation

**project.py** computes this determinant's exact norm
in the monic rank-12 ordinary quartic/direct \(F_n\)
cubic algebra. Its raw degree is **1704**, squarefree
degree **312**. The forbidden factors are \(J_4,E_+,E_-\);
the complete additional factor list is:

| Factor | Live guard | Exact rank cap | Prime / residue degree |
|---|---|---:|---|
| degree 12, constant 16227 | homogeneous \(c_1+6s\) | 11 | 103 / 12 |
| degree 12, constant 54123 | \(c_2\) in lower rank-four algebra | 9 | 103 / 4 |
| degree 60, constant −1461941766456 | old multiplication determinant | 11 | 103 / 1 |
| degree 216 | 1 | 12 | 101 / 1 |

On each nontrivial guard the indicated exact norm
divisibility proves the rank cap (using the lower
ordinary algebra specifically for \(c_2\)).
At the allowed exact chart these are live guards.

In **rank.py** use \(E=qK_*\) and
\(Q^\#=(qY-p)P+E P_0=qQ_4\).
The four \(3\times3\) minors of the actual three-column
span, now with \(\operatorname{trim}(I Q^\#)\) in the
cleared mark gauge, are each degree at most one in \(E\).
The paid quadratic adjacent mark \(ND=0\) at \(V\) is
the same polynomial divided by \(P_0\) as in the
cubic-leader proof, of degree at most two in \(E\).
Neither \(V-z\) nor \(1+\lambda\) is divided by.

The cap-three basis matrices of the five gates, after
multiplication by all guard-basis elements and allowed
powers of \(E\), have ranks **528, 144, 44, 48** in
the just-listed residue components. These attain the
exact upper dimensions of the four guard coefficient
images. The exact characteristic-zero images therefore
contain the live guard in degree zero, contradicting
any candidate. No unknown tableau or carrier is reduced
modulo a prime.

Run **bash verify.sh** with SymPy and python-flint 0.9.
This is an exact reproducible source result, not an
end-to-end formal tableau theorem.
