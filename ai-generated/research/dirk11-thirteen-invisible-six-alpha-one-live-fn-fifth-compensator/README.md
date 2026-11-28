# The fifth compensator is live, with an explicit cleared late kernel system

**Result.** In the direct noncontact \(F_n\) branch of the
normalized no-late invisible-six DIRK11/13 chart, take
\(\alpha=\beta=1\), live reciprocal multiplier, and the
fourth and fifth regular diagonals nonzero.
The actual fifth clean compensator \(\omega_B\) is nonzero.
Equivalently \(D_B\ne0\) and \(d_B\ne B-x\), where \(x\)
is the actual first middle ghost in reverse. There are also
two explicit necessary generic gates in the preceding
clock and carrier variables alone, of carrier degrees at
most 6 and 24. This does not exclude the whole \(\beta=1\)
chart or change the unrestricted real interval **13–14**.

Use the [matched reverse columns](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md)
and [live late affine pivot](../dirk11-thirteen-invisible-six-alpha-one-live-fn-late-affine/README.md).
The literal reverse order starts \(T,v,u,w,z,V,x,B,y\),
where the physical ghosts \(z,x,y\) are distinct, and
\(d_x=d_y=0\). In reverse write \(Y=1-c\), \(N=A^{\mathsf T}\),
\(W(f)=b_{\rm wt}f(Y)\), \(P=Ym,\ P_0=YR,\ P_5=(Y-V)P_0\).
Here \(R=(Y-v)(Y-u)(Y-w)\), and \(I\) is the zero-constant
primitive. The old fits \(\ell,\rho,W_0,M\) are as in the
cited exact proofs. We use \(\omega_B\) specifically for
the fifth compensator, not the separate old-slope expression.

## 1. Three low-degree equations on the zero-compensator slice

The matched column is \(D=(Y-z)G-W(Q_4)\),
\(Q_4=(Y-z)P+K_*P_0\), with
\[
 L=(Y-z)\ell-\rho+K_*W_0=\lambda(Y-z)(Y-x),\qquad
 IQ_4=\lambda(Y-x)Q_4+\eta P_5.
\]
Both identities are actual: \(D,ND\) are zero through \(V\),
and the \(x\) diagonal and \(L(x)\) are zero.
Put \(q\ne0,\ p=qz,\ E=qK_*,\ Z=qY-p,\ Q=ZP+EP_0=qQ_4\).
With common old adjugate scale \(n\), let
\[
 L^\#=Z\widehat\ell-q\widehat\rho+E\widehat W_0=qn L,\quad
 a=[Y^2]L^\#,\quad x_n=-q[Y]L^\#-pa,\quad x_d=qa .
\]
Thus \(x=x_n/x_d,\ \lambda=a/(nq)\), with \(x_d\) live.
Hats on old fits mean multiplication by \(n\).
Write \(\eta_N=(nq/5-a)[Y^4]Q,\ \eta_D=nq^2\), so
\(\eta=\eta_N/\eta_D\). Taking the coefficient of \(Y\)
in the exact primitive identity gives the small quadratic
\[
 A(E)=q\,\eta_N Vc_0+x_n[Y]Q=0 ,
\]
where \(c_0=R(0)\). The signs use \(P_5'(0)=-V c_0\).
This is the actual adjacent equation, not an additional
independence assumption on an old \(F_6\) determinant.

Use \(Q_V=Q(V)=(qV-p)k\) for \(k=G_V/b_V\), and
\(R_v=R(V)\). In the actual nonzero-\(d_V\) chart,
\(V-z\ne0\) and \(Q_V\ne0\). The following polynomial is
a common scale of the live reciprocal carrier:
\[
 S=Q_V S_M+n(qV-p)VJ_4(V)R=nR_vQ_VU_r,\qquad
 S_M=R_v\widehat M-\widehat M(V)R .
\]
Consequently the genuine first-forward-clean read has
\(d_B=J_b/(bS_B)\), with \(S_B=S(B)\), \(b=1-B\), and
\(J_b=\int_B^1(1-Y)S(Y)\,dY\). In the scaled clock code
the upper limit is the horizontal scale, and \(b\) is
that scale minus the scaled \(B\).

The polynomial
\[
 D_{\rm pol}=nR_vQ_V ZYJ_4-QS
\]
is divisible by \(P_5\): on the old three roots this follows
from \(m\widehat M=nJ_4\), at \(V\) from \(Q_V\) and
the construction of \(S\), and at 0 from the factor \(Y\).
At \(B\) it represents \(qS_BD_B/b_{\rm wt,B}\).
Thus with \(B_z=(D_{\rm pol}/P_5)(B)\),
\[
 \omega_B=(B-x)D_B/W(P_5)_B
          =(B-x)B_z/(qS_B).
\]
All divided numerical factors are live, including \(P_5(B)\).
The polynomial quotient prevents carrying a needless
high-degree factor into the clock projection.

Let \(\nu=\eta-(1+\lambda)\omega_B\), which is live
by the actual late affine read. The exact fifth kernel equation
is
\[
 d_B\nu=(B-x)(\nu+\omega_B).
\]
Also \(B-x\) is live in this nonzero-\(d_B\) chart, as proved
by the gap-diagonal packet. Hence \(\omega_B=0\) is equivalent
both to \(D_B=0\) and to \(d_B=B-x\). It forces, in addition
to \(A(E)=0\), the two degree-at-most-two gates
\[
 B_z(E)=0,\qquad J_b x_d-bS_B(Bx_d-x_n)=0 .
\]

## 2. Full exact zero-compensator exclusion

**project.py** takes the two exact degree-two homogeneous
resultants against \(A\), one with each of the last two
gates, in the same monic rank-12 direct \(F_n\)/ordinary
tower and horizontal scale as the earlier
[exact clock proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth/README.md).
These resultants remain necessary if any quadratic leader
drops. Their exact raw/squarefree degrees are
**4888/508** and **6576/632**. Only common polynomial
content on the known ordinary forbidden factors is removed.
The common squarefree gcd has degree **172**.
Beyond \(J_4,E_+,E_{\rm rep}\), its irreducible factors are:

| Factor | Live guard | Exact cap | Residue degree at 103 |
|---|---|---:|---:|
| degree 12, constant 16227 | homogeneous \(c_1+6s\) | 11 | 12 |
| degree 12, constant 54123 | \(c_2\) in the lower rank-four clock algebra | 9 | 4 |
| degree 24, constant 72 | old \(m\)-multiplication determinant | 10 | 1 |
| degree 48, constant 1865429207937 | homogeneous first-gap \(q\) | 11 | 1 |
| degree 60, constant −1461941766456 | old \(m\)-multiplication determinant | 11 | 1 |

For the rank 11 factors the exact determinant is zero
by the verified norm divisibility of the guard. For \(c_2\)
the lower ordinary norm zero gives rank at most three and
the free cubic extension gives cap nine.
The degree-24 **cap ten is proved over the exact number
field**, not inferred from its residue. **exact-rank.py**
checks the old determinant's \(12\times12\) multiplication
matrix by exact Gaussian row operations in \(\mathbb Q[V]/f_{24}\).
Each pivot inverse is checked; the two remaining rows are
zero. No reducedness of the upper two monic extensions is needed.

In **rank.py** multiply all three actual carrier quadratics
by the indicated guard, each ordinary clock basis element,
and allowable \(E\)-powers at cap 3.
The image lies in the direct sum of four exact guard images.
The residue matrices at 103 attain ranks
**528, 144, 40, 44, 44**, their exact caps times four and the
residue degrees. Thus the rational image contains the live
guard in degree zero, contradicting any candidate killing the
three actual gates. No unknown clock, \(E\) or tableau
coefficient is reduced. This excludes \(\omega_B=0\).

## 3. Generic kernel reduction without a late-root adjunction

For clarity the generic code uses the exact scaled reverse
coordinate throughout. Let \(D_0=L_1-VL_0\) with
\(L_0=IP_0/Y,\ L_1=I(YP_0)/Y\),
\(S_D=R_v\widehat D_0-\widehat D_0(V)R\) where
\(\widehat D_0=n(D_0/m\bmod R)\). Its effective scaled
four-ordinary fit for \(Q_5+\theta U_r\) is
\(Q_V S_D+n(qV-p)V D_0(V) R\).
Cross it with \(S\) at \(z\) (numerically homogenized by
\(q^3\)). Expansion cancels the constant-times-constant
cross term and the common \(Q_V\), leaving a
degree-at-most-one-in-\(E\) cubic equal to
\(nR_v(q^3S(z))Q_5\). This is the actual weighted
quintic from the previous checked packets.

Use the proved roots \(z,x=x_n/x_d\) for two exact synthetic
divisions. The first is homogenized by \(q^2\), the second
by \(x_d\). Write the resulting
\(L_5=Q_5/[(Y-z)(Y-x)]\) as
\((C_0+C_1Y)/C_d\). The two numerators and live denominator
have degree at most two in \(E\).
Set \(b_x=Bx_d-x_n,\ \omega_N=b_xB_z,\ \omega_D=x_dqS_B\),
and
\[
 \nu_N=\eta_N\omega_D-q(nq+a)\omega_N,\qquad
 \nu_D=\eta_D\omega_D .
\]
These represent \(\omega_B,\nu\), with degree caps
\(3,2,4,2\) for the four numerators and denominators in order.
The actual fifth gate has numerator
\[
 J_bx_d\nu_N-bS_B b_x(\nu_N+\eta_D\omega_N)=0 ,
\]
of degree at most six. The live late affine formula is
\[
 y=Y_n/Y_d,\qquad
 Y_n=x_n\nu_D C_d+nq^2\nu_N C_0,\quad
 Y_d=qa\nu_D C_d-nq^2\nu_N C_1 .
\]
Both are degree at most six, and \(Y_d\ne0\) by the
independent live late-affine proof. The actual roots and
live denominators, not assumptions on unobserved donor
clocks, justify these divisions.

For the actual late commutator, put \(T=(Y-V)R\).
Its polynomial before multiplying
\(\chi=-d_B^2U_r(B)/J_4(B)\) is \(T-S\Theta\), where
\(\Theta\) interpolates \(T/S\) at \(z,x\).
Use the homogeneous clock values
\[
 S_z=q^3S(z),\quad S_x=x_d^3S(x),\quad
 T_z=q^4T(z),\quad T_x=x_d^4T(x),\quad
 C_T=(qx_n-px_d)S_zS_x .
\]
Then, exactly,
\[
 T-S\Theta =
 \frac{C_T T-S[(x_n-x_dY)T_zS_x+(qY-p)T_xS_z]}{C_T}.
\]
This interpolation uses distinct ghosts and live \(S\) values,
not any division by \(R\) at a ghost.
After dividing the two known roots, let \(F(Y)\) be the
quadratic numerator after the homogenizing factors
\(q^3x_d^2\); its coefficient degree is at most eight.
The true late commutator from the proved \(d_y=0\) gives
\((y-B-d_B)L_5(y)+\chi (T-S\Theta)(y)/[(y-z)(y-x)]=0\).
Clearing scales before evaluating at \(y\) gives the
quadratic in \(Y\)
\[
 b n R_v Q_V J_4(B)\,q^3x_d^2 C_T
       \,[bS_B(Y-B)-J_b]\,(C_0+C_1Y)
       -J_b^2 C_d F(Y).
\]
Its coefficient degrees in \(E\) are at most 12.
Homogenize this quadratic at \((Y_n,Y_d)\) to obtain
the promised generic carrier gate of degree at most 24.

**coordinate-audit.py** independently checks the literal
adjacent coefficient, scaled \(B_z\), signs, and both
generic numerator/denominator formulas on four exact QQ
old-coordinate probes. **generic.py** builds the full
carrier-degree ledger on a sample ordinary residue algebra.
It is a diagnostic symbolic check, not a reduction of an
unknown tableau or a claimed generic exclusion.

Run **bash verify.sh** with SymPy and python-flint 0.9.
This is an exact written and executable source proof.
