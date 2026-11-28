# Three late ghost roots force a zero fifth reverse diagonal

**Result.** In the normalized no-late invisible-six
DIRK11/13 profile with live reciprocal multiplier and
cubic carrier, \((\alpha,\beta,\gamma)=(1,2,3)\)
forces \(d_B=0\) at the fifth regular reverse row.
Moreover the actual commutator on the weighted quintic
below vanishes identically. This calculation does not
use a direct/alternate old profile, a value of the
fourth diagonal, or a finite-characteristic inference.
It excludes the nonzero fifth-diagonal branch, not by
itself the whole beta-two profile. The unrestricted
real interval stays **13–14**.

Use the literal order and actual spaces from the
[live finite-profile proof](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md).
In reverse order the regular old three rows are followed
by \(z,V,x,y,B\). The three physical ghost clocks
\(z,x,y\) are distinct; the two after \(V\) are the
middle ghosts. Numerical ghost contacts with unrelated
ordinary clocks are allowed. Put \(Y=1-c\),
\(N=A^{\mathsf T}\) in literal reverse order,
\(W(P)=b_{\rm wt}P(Y)\), and write \(I\) for the primitive
from zero. Let \(R\) be the old cubic hull,
\(P_0=YR\), and \(P_5=(Y-V)P_0\). Define
\[
 L_0=IP_0/Y,quad L_1=I(YP_0)/Y,quad
 D=L_1-V L_0,quad j=J_4(V),\quad h=D(V).
\]
These are all in the **reverse** variable.
Normalize the live reciprocal relation as
\(H_{\rm bary}/G=U_r\) on weighted nonendpoint regular
rows, where \(U_r(Y)=U(1-Y)\) and
\(H_{\rm bary}/b_{\rm wt}=YJ_4(Y)\) there.
No division by the origin weight or by a ghost weight
is used.

## 1. The actual three-late polynomial relation

The true weighted quintic primitive error is
\[
 W(IP_5)-NW(P_5)=GQ_5+\theta H_{\rm bary},
 \qquad \deg Q_5\le3.
\]
Every inclusive weighted input through the second
middle ghost \(y\) is zero: terminal, old regular
rows and \(V\) annul \(P_5\), and ghost weights vanish.
Thus \(Q_5\) has roots \(z,x,y\).
For the old interpolation \(m=G/(Yb_{\rm wt})\),
the old read gives
\(mQ_5=D-\theta J_4\bmod R\).
The independent old determinant of \(L_0,L_1,J_4\)
from the
[two-ghost debit](../dirk11-thirteen-invisible-six-alpha-two-debit/README.md#1-a-nonzero-old-determinant)
uses only the distinct ordinary Jacobi clocks.
It implies \(Q_5\ne0\), hence \(Q_5\) is cubic
with all three stated distinct roots.

Put \(B_5=j(Q_5+\theta U_r)\).
The two genuine sample identities are
\[
 B_5(V)=h U_r(V),\qquad
 mB_5=jD\pmod R .
\]
For the first, the actual weighted input at \(V\)
of \(P_5\) is zero even when its diagonal is live.
Divide the literal primitive output by \(V\) and use
the reciprocal ratio there. The second follows from
the old fit and \(mU_r=J_4\bmod R\).

The actual commutator \(\mathcal R=CA-AC-A^2\)
gives \(\mathcal R^{\mathsf T}W(P_5)\in Z_7\)
by \(5+5+1=11\). As in the live finite-profile
proof, \(Z_7=G\mathcal P_4+H_{\rm bary}\mathcal P_1\).
This uses \(\dim E_3=5\), the separate terminal
debit, and independence of the clean directions
from \(G\) on six distinct live ghost clocks.
Write the row as \(GQ_c+H_{\rm bary}\Theta\),
with \(\Theta\) affine. Its zero old samples give
\(Q_c+\Theta U_r=(u_0+u_1Y)R\).
At \(V\) the literal weighted input through the
whole prefix is zero, giving \(u_0+u_1V=0\).
At \(B\), the only potentially nonzero weighted
input is its own; the literal commutator diagonal
is \(-d_B^2\). Thus with \(\chi=u_1\),
\[
 Q_c=-\Theta U_r+\chi(Y-V)R,qquad
 \chi J_4(B)=-d_B^2 U_r(B).
\]
It vanishes at all three ghost roots of \(Q_5\),
since the weighted prefix there is zero.
By degree, \(Q_c=\Lambda Q_5\) for an affine \(\Lambda\).
Consequently
\[
 \chi(Y-V)R=(\Theta-\theta\Lambda)U_r
                              +\Lambda B_5/j.
\]
Evaluate at \(V\), use the independent true sample
\(B_5(V)=hU_r(V)\), and cancel only live \(U_r(V)\).
The affine polynomial
\(\Theta-\theta\Lambda+(h/j)\Lambda\) is zero at
\(V\), thus equals \(\eta(Y-V)\) for a scalar \(\eta\).
It follows that
\[
 \chi R=\eta U_r+\frac{\Lambda}{j}
                       \frac{B_5-hU_r}{Y-V}.
\]
If \(d_B\ne0\), then \(\chi\ne0\), so
\(\eta,\Lambda\) are not both zero.

On the old three roots multiply by \(m\), using
the exact old samples. The three sites differ
from \(V\), so this implies the pure ordinary
coefficient determinant
\[
 \boxed{\det(E,YE,J_4)\bmod R=0,qquad
 E=\frac{jD-hJ_4}{Y-V}.}
\]
The numerator has the exact polynomial root \(V\).
The bound contains no \(m\), \(t\), or ghost
clock. The columns are the three reverse-coordinate
remainders in the same old cubic algebra.

## 2. Exact ordinary contradiction

The ordinary pencil is the monic
\(T_5=(J_5+\lambda J_4)/132\) with five distinct
nonendpoint roots. **ordinary.py** computes the
displayed determinant with \(60L_0,60L_1\).
Recover \(\lambda=-J_5(V)/J_4(V)\) and deflate
at \(V\), then at \(B\). The cleared ordinary
quartic in \(B\) has live leader \(132J_4(V)\).
After clearing that leader and taking a
pseudo-remainder of the determinant, the only
removed nonconstant content is proportional to
\(J_4(V)^{11}\); the remaining expression is
cubic in \(B\).
Its exact resultant with the ordinary quartic
factors as
\[
      J_4(V)^{12} E_-(V)^6
      \quad\text{up to a nonzero rational scalar},\qquad
      E_-=(J_5-J_4)/(2(V-1)).
\]
The factors are both forbidden. The first by
Jacobi coprimality, the second because it forces
\(\lambda=-1\) and the forbidden ordinary root
\(1\). Thus \(d_B=0\). Then \(\chi=0\), and
\(Q_c=-\Theta U_r\) is zero at the three ghost
roots with \(U_r\) live. The affine \(\Theta\)
is zero; the entire commutator vanishes.

This proof has no residue arithmetic, no
hypothesis that an old-profile denominator is live,
and no moving ghost order or leading-profile assumption.
It uses only actual live reciprocal shapes and
three true weighted-prefix ghost roots.
The separate QQ audit checks the reverse primitive
coefficients and the cancelled determinant against
literal evaluations on eight rational samples.
The existing first-middle coordinate audit verifies
the signed literal transpose
\(\mathcal R^{\mathsf T}=YN-NY-N^2\).

Run **python3 ordinary.py** and
**python3 coordinate-audit.py** with SymPy;
python-flint ground arithmetic can accelerate
the exact ordinary elimination.

This immutable packet is an exact written/source
proof. Optional Lean scalar source is kept separate
while the kernel audit is pending.
