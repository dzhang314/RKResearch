# Why simply deleting the duplicated clock cannot give a rational eleven-stage chart of this type

This is an architecture-specific obstruction, not an eleven-stage ERK lower bound. Use the same five-row head and the same seven active sites as in [the twelve-stage construction](README.md), but use only one physical slot at \(f=1-a\). Assume the sites \(0,a,1/2,d,1-d,f,1\) are pairwise distinct, \(b^\top\) has the eight paid moments, and \(B,D,E\) have the same moment and head-silence requirements as the construction.

Column chronology still forces \(E_j=(1+f)D_j-fB_j\) for every donor at \(1-d\) or \(f\), since the only later receiving clocks there are \(f,1\). Thus the same degree-four test gives
\[
       (21a^2-14a+2)d=a .
\]
This form does not assume the coefficient on the left is a unit: it follows by directly integrating the nodal polynomial with \(\mu_2-(1+f)\mu_1+f\mu_0\). In a rational chart \(a\ne0\), so division is legitimate.

A single stage at \(f\) has only one later receiver, at 1, so \(D_f=B_f\). Set \(P_f=x(x-a)(x-1/2)(x-d)(x-1+d)\), the degree-five polynomial vanishing on the active donor sites other than \(f\). The equality \(D_f=B_f\) implies the exact identity
\[
  0=\int_0^1 [\mu_1-(1-x)^2]P_f(x)\,dx
    =\frac{(3a-2)(7d^2-7d+1)}{1680}.
\]
Indeed \(D\) pays degree five and \(B=b^\top(I-C)\); the factor \(1-x\) kills the final site. The quadratic in \(d\) has discriminant 21 and has no rational root. The remaining possibility \(a=2/3\) gives \(d=1/3=f\), excluded by distinctness. Consequently this symmetric chart cannot simply lose its duplicate physical clock over \(\mathbb Q\) or \(\mathbb Z[1/210]\).

This does not exclude nonsymmetric nodes, other simplifying assumptions, or controls exploiting a different repeated-clock layout.
