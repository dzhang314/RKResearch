# DIRK12/15: the literal fourth ordinary diagonal splits the late-ghost projection

Continue the [geometry-free late-fourth-ghost projection](../dirk12-fifteen-rank3-invisible-late-finite-projection/README.md) in its exact scope: four distinct dirty ghosts in the real ordinary \(C(2),f_5=3\) invisible high-site equality branches, the first three ghosts having nonzero ordinary clocks before the first ordinary nonzero live row \(a\), and the fourth ghost before the next nonzero live row \(b\). Put \(x=b/a,y=c/a,t=e/a\) for the unique first four ordinary nonzero live labels. Write \(d(t)=A_{ee}/a\) for the actual fourth live diagonal. The overall real interval remains **15–16**.

There is a useful exact division of the finite prefix problem:
- If \(d(t)\ne0\), then
\[
                       t=\frac{x(y-1)}{2xy-x-y},
  \qquad 2xy-x-y\ne0 .
\]
In particular the fourth clock is fixed by the second and third ratios before testing any Jacobi interpolation at \(t\).
- If \(d(t)=0\), its exact scalar and genuine fourth-row commutator requirements reduce to a common root of degree-at-most \(2,3,3\) polynomials specified below. Their coefficient denominators and the physical two-mode evaluation are all nonzero on an actual prefix.

Neither branch is asserted globally empty. The analysis uses the actual unpaid \(\varepsilon_{12}\) only through the prior valid mixed geometry, never setting it to zero.

## Actual evaluation rank and a genuine new grade-five mask

Reuse \(\bar A=A/a\), \(\bar R=(CA-AC-A^2)/a^2\), \(J\) the ordinary scalar primitive from zero, \(R_6(s)=L_6'(as)/L_6'(a)\), and \(G_j(s)=s[L_j'(as)-R_6(s)L_j'(a)]\) for \(j=5,7\). By the genuine grade-seven calculation, the nonterminal live profiles of \(F_7\) are contained in \(s\langle L_5'(as),L_6'(as),L_7'(as)\rangle\). Evaluation at \(1,x,y\) is actually nonsingular on this mode space: two genuine pure grade-seven ghost columns \(A\mathbf e_g\) have independent first two readings by the exact rank-two tap theorem, while the genuine \(Z=\bar R(\bar A\mathbf Q)\) is zero there and has \(-\omega^2W(y)\ne0\) at \(y\). Here \(W=T^2(T-1)^2(T-x)\), \(\omega=\bar A_{cc}\ne0\), and \(\mathbf Q\) is the actual common quartic mask. Thus the two-mode evaluation on \(x,y\) of \(G_5,G_7\) has nonzero determinant on every actual prefix. This does not presume that a generic coefficient guard avoids vanishing at an arbitrary scalar grid.

The exact positive-degree ghost moment transform of the earlier proof says \(\sum_g\ell_gF(p_g)\) is a fixed nonzero multiple of \(\mathcal M_z(F)\) for \(F\in TP_4\), where \(P_j\) denotes degree at most \(j\). Since \(\ell_g=1/[h_g D_4'(a p_g)]\), this sum tests the fourth-point divided difference of \(F(p_g)/h_g\). The four \(p_g\) are distinct and \(h_g\ne0\). Therefore
\[
 \mathcal M_z(F)=0
  \quad\Longleftrightarrow\quad
 \text{there exists } Q_2\in P_2\text{ matching }F(p_g)/h_g\text{ on all four ghosts}.
\]
Equivalently the literal grade-five vector \(\mathbf S_F=F(\mathbf c/a)-\mathbf h Q_2(\mathbf c/a)\) has zero numerical entries at all ghosts. This uses actual \(F_5=\mathbf h P_2(\mathbf c)\); it is not an assertion about a synthetic reverse tableau or scalar precision at dirty ghosts.

Take \(P_0=T(T-1)(T-x)(T-y)\), and put \(N_i=\mathcal M_z(T^iP_0)\) and \(I_i=\mathcal I(T^iP_0)\) for \(i=0,1\), with \(\mathcal I(F)=JF(1)\). The geometry-free moment recurrence gives explicitly
\[
 \begin{split}
 N_0&=\frac{2(2x-1)(2xy-x-y)}{5x(x-1)},&
 N_1&=\frac{2(2x-1)(y-1)}{5(x-1)},\\
 \Delta&=I_0 N_1-I_1N_0
             =\frac{(2x-1)^2D}{150x(x-1)},&
 D&=2xy-x-3y^2+2y .
 \end{split}
\]
Here \(N_1,\Delta\ne0\) by the guards on the genuine first three clocks and \(D\ne0\).

If \(N_0=0\), set \(F=P_0\). Otherwise set \(F=P_0(T)(T-N_1/N_0)\). In either case \(\mathbf S_F\) is a genuine grade-five vector, zero at all ghosts, the literal origin and the first three nonzero ordinary live rows. Thus \(\bar R\mathbf S_F\in F_7\) is zero on those three nonzero live rows by causality. By the actual mode rank it is zero on all nonterminal live rows. At the actual fourth row its only possible source is its own diagonal, giving \(-d(t)^2F(t)=0\). If \(d(t)\ne0\), then \(F(t)=0\), and \(P_0(t)\ne0\) rules out \(N_0=0\) and gives \(t=N_1/N_0\) as stated. No assumption on the signs of individual live weights enters this argument.

In this case, the genuine scalar nodal state \(K=P_0(T)(T-t)\) satisfies \(\mathcal M_z(K)=0\) and \(\mathcal I(K)=I_1-t I_0=-\Delta/N_0\ne0\). Its exact actual zero live read also gives the single explicit test
\[
              R_6(t)=\frac{JK(t)}{t\,\mathcal I(K)}.
\]
The actual fourth diagonal is then recovered without ambiguity from \(\mathcal A(P_0)(t)/P_0(t)\), and must still satisfy the independent genuine grade-seven relation from the preceding projection. Thus the Möbius candidate does not suffice to assert a tableau.

## The zero fourth diagonal and three low-degree real equations

The actual live-only scalar functional in the source proof is
\[
             \mathcal A(F)(s)=JF(s)-s R_6(s)\mathcal I(F)-B(s)\mathcal M_z(F),
 \qquad B\in\langle G_5,G_7\rangle.
\]
If \(d(t)=0\) then its two nodal reads on \(P_0,TP_0\) are both zero at \(t\). The same two reads are zero at \(s=1,x,y\) regardless of their diagonals, because both profiles vanish on the entire live support available at those rows. The displayed \(\Delta\ne0\) solves both requirements for any of those \(s\) and for \(t\) if its diagonal is zero:
\[
 \begin{split}
 R_0(T)&=\frac{JP_0(T)N_1-J(TP_0)(T)N_0}{T\Delta},\\
 B_0(T)&=\frac{ I_0J(TP_0)(T)-I_1JP_0(T)}{\Delta}.
 \end{split}
\]
The quotient by \(T\) here is polynomial, since both primitives vanish at zero. Thus \(R_0,B_0\) have degrees at most five and six. Write \(V_0=JW-T R_0\mathcal I(W)\), using \(\mathcal M_z(W)=0\). The true modes \(R_6,B,Z\) are recovered from the earlier actual prefix: \(R_6\) is a scaled Legendre derivative, and \(B,Z\) are fixed by their exact two-mode reads at \(x,y\).

With \(d(t)=0\) the true \(\bar R(\bar A\mathbf Q)\) fourth read has only the previous \(y\)-row contribution, giving \(Z(t)=(t-y-\omega)V_0(t)\). Hence define the three exact quotient polynomials
\[
   E_{0,R}=\frac{R_6-R_0}{(T-1)(T-x)(T-y)},\qquad
   E_{0,B}=\frac{B-B_0}{P_0},\qquad
   E_{0,Z}=\frac{(T-y-\omega)V_0-Z}{P_0}.
\]
For the first two, the preceding values agree by their two actual nodal equations, and \(B_0(0)=B(0)=0\). For the third, \(V_0(0)=V_0(1)=V_0(x)=0\) by the actual prefix, while \(V_0(y)=\omega W(y)\) gives exactly \(Z(y)=-\omega^2W(y)\). Thus every denominator divides exactly on an actual prefix; the degrees of the quotients are at most \(2,3,3\), respectively. The actual fourth clock \(t\) must be a common root. In contrast to the original two equations of degrees at most \(4,5\), these incorporate the extra literal fourth diagonal value before elimination.

The replay checks the exact moment and minor factors, the Möbius relation, and the two-by-two elimination used in both branches. It is exact symbolic arithmetic with an analytic grade-space proof, not a complete Lean certification or a change to the real endpoint.

    python3 -B verify.py
