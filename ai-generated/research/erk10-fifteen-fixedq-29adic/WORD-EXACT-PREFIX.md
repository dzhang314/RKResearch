# Exact eight-word algebraic prefix and symmetric Z-tail test

These arithmetic replays are separate from the Lean word solver. They
perform exact rational arithmetic in the degree-ten decic coefficient
field, then in pairs \(f_0(C)+a f_1(C)\) with \(a^2=s(C)a-q(C)\).
There is no approximate root substitution or large-modulus extrapolation.
The same actual physical data, without changing the pair chronology,
pass every one of eight word equations in each of the first eight
reverse rows. All solved prefix coefficients have 29-unit power-basis
denominators.

The second check keeps the two terminal-observer output tests univariate.
Write \(d=26,\ R=15\), \(D_3=(Y^2-sY+q)(Y-d)\),
\(J(Y)=Y-14Y^2+56Y^3-84Y^4+42Y^5\), and
\[
P_\flat(Y)=J(c)(6Y^5-15cY^4+10c^2Y^3)-c^5J(Y),\qquad
N_\flat(Y)=2qc+2(-2q+cs-c^2)Y.
\]
The exact quadratic \(V\) is determined by
\[
Y^2(Y-c)^2 V(Y)+N_\flat(Y)P_\flat(Y)\equiv 0\pmod{D_3}.
\]
Thus \(V\) is the ordinary scalar interpolation behind
\((30J(c))a(2b-c)\,Q_Z(Y)=(Y-c)V(Y)\).
With \(\mu\) the actual cardinal numerator, define
\[
\sigma=\frac{\mu(d)d(d-R)(d-c)}{(d-1)N_\flat(d)}.
\]
This equals the cofactor scale divided by \(a(2b-c)\) after using the
d-site head ratio, so the two scored terminal gates are the univariate
identities
\[
\mu(y)(y-R) P_\flat(y)
 +(y-1)y \sigma (y-c)V(y)=0,\qquad y=e,f.
\]
This avoids a bivariate expansion for these two gates. The replay
checks both exact identities and the paid residues of the subtraction
data. It does not yet turn them into additional native K row proofs.

Replay from the repository root:
- `python3 ai-generated/research/erk10-fifteen-fixedq-29adic/exact-quad.py ai-generated/research --prefix 8`
- `python3 ai-generated/research/erk10-fifteen-fixedq-29adic/z-tail.py ai-generated/research`

The first check can take several minutes without an accelerated rational backend. The compact univariate
test is substantially smaller.
