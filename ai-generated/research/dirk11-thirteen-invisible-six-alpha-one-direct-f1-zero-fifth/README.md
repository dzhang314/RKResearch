# Independent zero-fifth exclusion for the direct F1 profile

**Result.** In the normalized live reciprocal no-late invisible-six
DIRK11/13 chart, \(\alpha=1\) and \(\beta=1\) or 2, direct
noncontact \(F_1\) cannot have fifth regular reverse diagonal
\(d_B=0\). The [uniform beta-two zero fifth result](../dirk11-thirteen-invisible-six-alpha-one-beta-two-zero-fifth/README.md)
therefore independently excludes every live beta-two direct
\(F_1\) tableau. This proof does not transfer a direct \(F_n\)
carrier by reflection. The [first-ghost bridge](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-bridge/README.md)
is a separate shorter route to exclusion, including beta one.

Use the actual old marks of the
[live old-profile proof](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md)
and the [zero first-middle diagonal](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md).
In reverse coordinates, let \(R=Y^3+c_2Y^2+c_1Y+c_0\), \(P=Ym\),
\(P_0=YR\) and \(P_5=(Y-V)P_0\), with \(z,x\) the distinct first
and first-middle zero-weight ghosts. The direct \(F_1\) profile is
\[
 m=Y^2+rY+s,\quad
 F_1(s)=96s^3-80c_1s^2+75c_0c_2s-75c_0^2=0,\quad
 r=15(c_2s-c_0)/(16s).
\]
The guard \(s\) is live. No assumption about any alternate solution
of the old quadratic is made.

## 1. Actual fifth-diagonal pin and exact ordinary projection

Use the scaled reciprocal gauge from the
[independent zero-fifth direct Fn proof](../dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth/README.md):
\(U_r=M+tR\) with \(M,W,Q\) numerator fits of
\((J_4,L_0,L_1)/m\bmod R\), all in common live adjugate
scale \(n\). Then \(k=G_V/b_V=nVJ_4(V)/U_r(V)\)
and \(d_V U_r(V)=C_V=D_4(V)+tL_0(V)\).
Here \(D_4=(L_0M-WJ_4)/R\), \(D_5=(L_1M-QJ_4)/R\),
\(L_0=IP_0/Y\), \(L_1=I(YP_0)/Y\).
The first forward nonorigin clean row \(b=1-B\) has
literal grade-five read \(d_B b U_r(B)=J(b)\) with
\(J=I_X[XU_r(1-X)]\), because all previous inclusive
donors for \(C\phi\) are zero. Thus the hypothesized
\(d_B=0\) gives \(J(b)=j_0+j_1t=0\).
The code calculates this also by the exact reverse
endpoint primitive; after horizontal scaling the
upper endpoint is the scaled origin.

The true adjacent \(V\) mark gives \(A(t)=a_0+a_1t+a_2t^2=0\),
using \((z-V)T=I^2P(V)-\rho(V)k\) itself, with no
division by \(1+\ell_1\). Hence
\[
 a_0j_1^2-a_1j_0j_1+a_2j_0^2=0
\]
even if a leader drops. **project.py** forms this exact
norm over the monic rank-12 ordinary quartic and **direct
F1** cubic tower, with the same horizontal clock scale
\(132J_4(V)\) as in the companion exact norm construction.
The common ordinary polynomial content that may be removed
divides a power of the known live factors
\(V(V-1)J_4 E_-E_+E_{\rm rep}\).
No guard factor that vanishes at an admitted candidate is removed.
The absolute norm has raw degree 736 and squarefree degree 356.
After the four forbidden Jacobi factors, its exact support is
the irreducible degree-24 factor of constant \(364663909217\)
and an irreducible degree-312 factor. The degree-24 factor
divides the **exact** norm of the live first-gap denominator
\(q=3s c_2-4rs-3c_0\) up to its common homogeneous scale;
this supplies rank cap 11 there. The other factor uses cap 12.

## 2. New first-middle pin with two true polynomial reads

For the actual zero-diagonal first middle ghost \(x\), the
[gap-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md)
gives the exact \(L=(Y-z)\ell-\rho+K_*W_0
=\lambda(Y-z)(Y-x)\), with live \(\lambda\) and
\(K_*=(V-z)(k-P(V))/P_0(V)\).
If \(z=p/q\), \(u=U_r(V)\), \(h=VJ_4(V)\), the code uses
\[
 L^\#=P_0(V)u[(qY-p)\widehat\ell-q\widehat\rho]
          +(Vq-p)(nh-P(V)u)W
       =q n P_0(V)u L .
\]
Hats denote the common adjugate scale \(n\).
Therefore \(x=x_n/x_d\) with
\(x_d=q[Y^2]L^\#\ne0\) and
\(x_n=-q[Y]L^\#-p[Y^2]L^\#\).

The true \(P_5\) weighted primitive error has roots \(z,x\)
by its literal weighted-zero prefix. Reconstruct its cubic
by crossing its scaled effective old-and-\(V\) fit
\(B_5=J_4(V)(Q-VW)+(D_5(V)+tL_1(V)-V C_V)R\)
against \(U_r\) at \(z\). Divide its known factor \(Y-z\)
in the polynomial, clear \(q\), and homogenize at
\((x_n,x_d)\). The necessary gate has degree at most 3 in \(t\).
The other read is the true \(P_0\) commutator:
\[
 (x-V-d_V) W_0(x)+Q_c(x)=0
\]
using \(d_x=0\). Here
\(Q_c= -d_V^2 U_r(V)\big(R-R(z)U_r/U_r(z)\big)/(nJ_4(V))\).
Cancel the common polynomial \(Y-z\) (with live \(x-z\)),
clear the \(z\) and carrier powers, and homogenize at the
same \((x_n,x_d)\). This gate has degree at most 4 in \(t\).
Neither gate divides by \(d_V\), by a quartic signal,
or by a ghost–regular clock difference.
**coordinate-audit.py** verifies the adjacent numerator,
new affine pin, both scale formulas, and reflection on four
exact \( \mathbb Q \) coordinate inputs.

## 3. Saturated residue images lift to exact exclusion

In the two exact characteristic-zero tower algebras, take
\(g=q\) in the degree-24 case and \(g=1\) in the degree-312
case. The exact upper ranks of multiplication by \(g\) are
11 and 12, respectively. At 103 the chosen residue factors
have degrees 3 and 1, explicitly
\(V^3+97V^2+7V+10\) and \(V+2\).
On these entire residue tower components, the ranks of
multiplication by \(g j_1\) and of the summed images of the
\(g\)-multiples of the pinned gates are both exactly
\(33/33\) and \(12/12\) in their respective exact caps.
The pinned gates use \(t=-j_0/j_1\) with fixed homogeneous
carrier caps \(2,3,4\), preserving any specialized leader loss.

The matching exact rank cap and residue minors prove that
both images are the full image of \(g\) in characteristic zero.
First \(j_1\) is therefore live on any actual candidate,
since it cannot kill live \(g\). Then evaluation of the pinned
gates at a candidate would kill the same live \(g\), impossible.
These are exact lifts in the fixed clock algebra, not reductions
of unknown tableau values.

Run **bash verify.sh** with SymPy and python-flint 0.9. It
reruns the exact rational coordinate audit, exact projection,
and both rank witnesses. No numerical stage-bound change or
end-to-end Lean tableau proof is claimed.
