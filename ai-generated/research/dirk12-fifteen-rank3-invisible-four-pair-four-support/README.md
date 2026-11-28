# DIRK12/15: the four-pair four-support reverse cubic is impossible

Consider the [invisible four-distinct-ghost, fixed seven scalar site chart](../dirk12-fifteen-rank3-invisible-four-ghost-fixed-grid/README.md) on the ordinary real fifteen-stage \(C(2),f_5=3\) equality face. Assume the eleven live rows have four repeated pairs and three singletons, and that the true weighted reverse cubic is supported at all four repeated labels. **This subcase is impossible.** Combined with the [one- and three-support exclusions](../dirk12-fifteen-rank3-invisible-four-pair-local-three/README.md) and the invariant grade-four exclusion of two support labels, this closes the whole four-pair fixed seven-site chart. By the previous three-repeat exclusions and the earlier repeated-label count, it closes the entire invisible, exactly four distinct cubic ghosts, fixed seven-site chart. The broader invisible case and the real **15–16** stage interval are not decided.

Use true reversed physical order with \(N=A^{\mathsf T}\) in that ordering, \(\mathbf y=1-\mathbf c\), \(Y=\operatorname{diag}(\mathbf y)\), \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\), and \(JP(X)=\int_0^X P\). Every ghost coordinate is actual pure grade six by the forward \(\mathbf hP_3\) cardinal construction. The true weighted grade-five flag is zero on all ghost and singleton rows and sums to zero separately on each live fixed scalar label. In particular, for genuine weighted cubic \(\mathbf G\), both live members of each marked repeated pair have nonzero \(\mathbf G\) component, with opposite covector values. Its true grades three, four and five are the corresponding spans \(\mathbf G P_0,\mathbf G P_1,\mathbf G P_2\), by rank and clock lifts. Its grade six contains the four-dimensional clock-invariant \(\mathbf G P_3\); if grade six were rank four, the actual incoming two-detector rank bound would contradict the unit step from five. Thus grade six is rank five, although the closure below does not need its exact extra direction.

## All four repeats singly debut before the earliest event

By the [asymmetric \(6+5\) spending selector](../dirk12-fifteen-rank3-invisible-four-pair-local-three/README.md), no nonzero live label can be completely spent while at most three distinct nonzero live labels have appeared. In particular the first three nonzero labels are repeated and each is observed once.

If the fourth distinct nonzero live label were a singleton \(a\), the genuine weighted grade-three contrast interpolating the three prior normalized \(\mathbf G/b\) amplitudes and vanishing at the reverse origin would be zero before \(a\). Its grade-five commutator pure error is zero there. As in the three-support argument, this yields two zero primitive moments, forces a nonzero contrast at \(a\), and forces the actual diagonal zero. The exact degree-four primitive on the four previous labels \(0,x_1,x_2,x_3\) would then require \(J[X\prod_{i=1}^3(X-x_i)](a)=0\), excluded by the already checked unanchored fixed grid gate. Hence the first four nonzero labels \(x_1,x_2,x_3,x_4\) are precisely the four repeated labels, and only one live row of each has occurred through their four debuts. After these debuts, the next live physical row is either the first nonzero singleton \(a\), or the row spending one of the four pairs. The other singleton is denoted \(b\). If reflected \(1\) is singleton, its row is the literal ordinary origin, last in reverse order, so \(a\ne1\). Likewise no pair at reflected \(1\) can be spent before \(a\).

Zero-weight rows may be interspersed at any clocks: all weighted scalar inputs and the true pure \(\mathbf G,\mathcal B_4,\mathcal B_5\) inputs used here automatically have zero coordinates there.

## The four literal single-row debuts

Let \(g_j=G_{i_j}/b_{i_j}\) be the normalized first amplitude at \(x_j\). These are all nonzero. At the first row \(g_1=x_1^3/6\) by the two exact leading weighted primitives. Put \(t=g_2,\ z=g_3,\ w=g_4\), and leave them as exact unknowns.

Use four genuine pure facts, written as ratios with the actual \(\mathbf G\) in the full physical weighted space:
\[
 \begin{split}
  &N\mathbf W(X^3)-\mathbf W(X^4)/4 = E(Y)\mathbf G,\quad
                  N\mathbf G = A_1(Y)\mathbf G,\qquad \deg E,\deg A_1\le1,\\
  &N\mathbf W(X^4)-\mathbf W(X^5)/5 = F(Y)\mathbf G,\quad
                  N(Y\mathbf G)=U(Y)\mathbf G,\qquad \deg F,\deg U\le2 .
 \end{split}
\]
\(A_1\) here denotes a scalar affine polynomial, not the tableau. The first-row ratios are
\[
              E(x_1)=3x_1/2,\quad A_1(x_1)=x_1/2,\quad
              F(x_1)=9x_1^2/5,\quad U(x_1)=x_1^2/2 .
\]
They follow from the literal diagonal \(x_1/2\) and only earlier live zero clock. At the row of \(x_j\), normalize by this row's nonzero weight. Its aggregate taps are exactly the row functional on the Lagrange cardinals of the prefix mesh \(D_j=(0,x_1,\ldots,x_j)\). For a degree at most \(j\) scalar polynomial \(P\), this row functional is its primitive \(JP(x_j)\) plus the corresponding primitive defects:
\[
            g_j\bigl(P_2+E(x_j)P_3+F(x_j)P_4\bigr)
\]
with \(P_i\) its coefficients and nonexistent coefficients zero. The diagonal appears normally among the site taps to \(x_j\); it is not assumed zero.

Here is the denominator-cleared recurrence used by the replay. For a scalar scale \(s\) and errors \(c_i\), let \(W(D,x;s,\{c_i\})\) be the row vector indexed by \(q\in D\) with entries \(s\,J L_q(x)+\sum_i c_i\operatorname{coeff}_i L_q\), where \(L_q\) is the cardinal on \(D\). Thus it is just the scaled actual row. All scalar cardinals have fixed denominators given by differences of distinct Lobatto nodes. Define \(G_j=(0,g_1,\ldots,g_j)\).

1. \(W_2=W(D_2,x_2;1,\{c_2=t\})\). Its evaluations on \(X^3,X^4,G_2,YG_2\), subtracting the corresponding scalar primitives for the first two, give the four cleared values \(e_2=tE(x_2), f_2=tF(x_2), r_2=tA_1(x_2), u_2=tU(x_2)\).
2. Interpolate \(tE,tA_1\) from \(x_1,x_2\); at \(x_j\) denote the results by \(e_j,r_j\). Set \(W_3=W(D_3,x_3;t,\{c_2=tz,c_3=e_3z\})\). Then
   \[
          Q(t,z)=W_3 G_3-r_3z=0 .
   \]
   For the other two coefficients, \(f_3=W_3(X^4)-t x_3^5/5=tzF(x_3)\) and \(u_3=W_3(YG_3)=tzU(x_3)\).
3. Interpolate \(tzF,tzU\) on \(x_1,x_2,x_3\) using respectively \((tzF(x_1),z f_2,f_3)\) and \((tzU(x_1),z u_2,u_3)\). Denote their values at \(x_4\) by \(f_4,u_4\). Set \(W_4=W(D_4,x_4;tz,\{c_2=tzw,c_3=ze_4 w,c_4=f_4w\})\). Genuine \(NG\) and \(NYG\) then give
   \[
   \begin{split}
       F_*&=W_4 G_4-zr_4 w=0,\\
       L_*&=W_4((Y-x_4)G_4)-(u_4-x_4zr_4)w=0 .
   \end{split}
   \]
   \(F_*\) is at most quadratic in \(w\); \(L_*\) is at most affine, because using \((Y-x_4)G_4\) removes its own-stage \(w\).

Monomial divisions by \(t,z\) mean only the preceding actual normalized amplitude ratios; the replay recurrence above itself does not invert them. All presented polynomial equations are necessary conditions on the actual row chronology.

## The first post-debut event supplies one affine equation in \(w\)

If the event is the singleton \(a\), its node set is \(D_4\cup\{a\}\). Its scalar primitive is exact through degree four; for each degree-five cardinal its row is therefore \(J L(a)+\xi\operatorname{coeff}_5 L\) for one actual scalar error \(\xi\), which need not be zero. On the four earlier repeat coordinates set
\[
 I_j=JL_{x_j}(a),\qquad B_j=\operatorname{coeff}_5 L_{x_j}.
\]
Genuine \(NG,NYG\) at this singleton vanish by grades four and five. Eliminating \(\xi\) gives
\[
 C=\left(\sum I_jg_j\right)\left(\sum B_j x_jg_j\right)
     -\left(\sum B_jg_j\right)\left(\sum I_jx_jg_j\right)=0 .
\]
There is no squared \(g_j\) in \(C\), so it is affine in \(w\). No division by \(B\) or another unknown pure coordinate is required.

If the event is spending a repeated \(s=x_k\), cut immediately after that actual row. Take the scalar quartic \(R\) on \(D_4\) with \(R(0)=0\) and \(R(x_j)=(x_j-s)g_j\). The actual grade-four weighted state \(\mathbf W(R)-(Y-s)\mathbf G\) is late supported: the other repeats are still singly observed, and \(s\)'s scalar and pure readings are both zero regardless of its second amplitude. Pair the true weighted primitive with the early grade-six ordinary card on the spent site \(s\), using all four pure ghost coordinates to clear its ghost values. Thus \(I(L_s JR)=m_s JR(s)=0\) at paid \(6+5=11\). This gives
\[
                  C=\sum_j JL_{x_j}(s)(x_j-s)g_j=0,
\]
where now \(L_{x_j}\) are cardinals on \(D_4\) and \(m_s>0\) is the actual scalar aggregate at the spent clock. This is a genuine affine equation in \(w\), with coefficient zero for the amplitude of the spent group itself. In particular for \(s=x_4\) it solves \(z\) as affine in \(t\): the coefficient of \(z\) is \((x_3-x_4)JL_{x_3}(x_4)\ne0\), by the fixed exact nodal gate from the previous packet.

## Fixed-degree resultants and exact boundary factors

Write \(L_*=L_0+L_1w,\ F_*=F_0+F_1w+F_2w^2,\ C=C_0+C_1w\). For the singleton and the first three spent-site choices, eliminate \(w\) with the necessary identities
\[
       M=L_0 C_1-L_1 C_0=0,\qquad
       V=F_0 C_1^2-F_1 C_0 C_1+F_2 C_0^2=0 .
\]
Both are necessary even if \(C_1=0\), because then \(C_0=0\) at an actual solution. Thus \(t\) is a root of \(\operatorname{Res}_z(Q,M)\) and \(\operatorname{Res}_z(Q,V)\), and also of \(\operatorname{Res}_z(Q,M+V)\) if used. Resultants are **degree-padded** Sylvester determinants, so leading coefficient losses at an admissible residue do not silently change the finite expressions. Their \(z\)-degree bounds are \(2\) for \(Q\), and the table below for the other arguments.

The powers of \(t\) removed in arithmetic are *actual characteristic-zero factors*, not merely residue valuations. We use the following elementary statement. If \(Q(0,0)=0\) and \(E(t,z)\in(t,z)^k\) for \(k=1\) or \(2\), then the padded \(\operatorname{Res}_z(Q,E)\) is divisible by \(t^k\). For \(k=1\) the specialized two polynomials share the root \(z=0\). For \(k=2\), if \(Q(0,z)\) is divisible by \(z^2\), both specialized input polynomials are then divisible by \(z^2\); every column of the Sylvester map is so divisible, giving rank deficit at least two and the determinant has order at least two. Otherwise \(Q(0,z)\) has a simple root at zero. Recursively lift that root as a formal expression \(z(t)\in tK[[t]]\) using its nonzero derivative; the monic factor \(z-z(t)\) divides \(Q\) over \(K[[t]]\), and its resultant with \(E\) is \(E(t,z(t))\in t^2K[[t]]\). Multiplicativity of the homogeneous padded resultant gives the factor. This proof does not depend on irreducibility or the actual unknown \(t\)'s residue.

Here \(Q(0,0)=0\), while \(L_0,F_0\) are divisible by \(tz\) and \(L_1,F_1,F_2\) have zero constant at \(t=z=0\), directly from the cleared recurrence. At the singleton and the first spent role \(x_1\), \(C_0(0,0)=0\), so \(M,V,M+V\) lie in \((t,z)^2\). At spent roles \(x_2,x_3\) they lie in \((t,z)\). These justify exactly the removed \(t^k\) factors. For \(s=x_4\) no boundary factor removal is needed; substitute the genuine affine \(z(t)\), use \(Q(t,z(t))\) and the exact necessary polynomial \(F_0 L_1^2-F_1L_0L_1+F_2 L_0^2\) after substitution.

One also needs a true leading-degree guard, so an unknown amplitude cannot escape at the infinite place of \(t\) while all finite residues vanish. For \(A(t)=\operatorname{Res}_z(Q,M)\) the bound is sharper than the immediate total-degree bound. Write \(\deg_{\rm tot}Q\le3,\ \deg_z Q\le2\), and use:
\[
\begin{array}{c|rrrrrr}
 \text{event} &\deg_z M&\deg_{\rm tot} M&\deg_z V&\deg_{\rm tot} V&
          \deg A\text{ bound}&k\\\hline
 a          &3&5&4&6&11&2\\
 s=x_1      &3&4&3&4&10&2\\
 s=x_2      &3&4&3&4& 9&1\\
 s=x_3      &2&4&2&4& 9&1
\end{array}
\]
All degree entries are upper bounds. They follow from \(L_0,F_0\) being \(tz\) times a linear combination of the first three amplitudes; \(L_1,F_1\) have total degree at most three and \(z\)-degree at most two, and \(F_2\) has total degree at most two and \(z\)-degree at most one. For the sharper \(A\) bound, substitute \(t=1/\epsilon,z=y/\epsilon\), clear total degrees, and apply the preceding small resultant order lemma at \((\epsilon,y)=(0,0)\). The raw total-degree determinant bound is \(n\cdot 3+2\deg_{\rm tot}M-2n\) for \(n=\deg_z M\) as padded. The scaled \(Q\) has a root at \(y=0\) when \(\epsilon=0\), because \(Q(t,0)\) has degree at most two. The infinity orders of scaled \(M\) are at least \(2,1,2,1\) in the four table rows: \(L_0\) has its factor \(z\) and \(L_1(t,0)\) has degree at most two, so the homogeneous leading cubic of \(L_1\) has a factor \(z\). The latter degree-two boundary follows at once because at \(z=0\) the \(w\)-coefficient of \(W_4\) is affine in \(t\), and \(u_4(t,0)\) is at most quadratic. For the singleton, the top quadratic of \(C_0\) has a factor \(z\) and \(\deg_t C_0(t,0)\le1\); for \(s=x_2\), its top linear part is proportional to \(z\), and \(C_0(t,0)\) is constant. Thus in those two rows the leading term of \(M\) has a double \(z\) factor and its value at \(z=0\) loses at least two powers of \(t\). In the other two rows the leading term has a \(z\) factor. This proves the indicated infinity discounts. For \(s=x_4\) use the immediate exact degree bound three on \(Q(t,z(t))\) instead.

## Exact arithmetic and transfer

    python3 -B check.py

The independent standard-library checker implements the padded Sylvester determinants via exact finite interpolation within the raw total-degree bounds, including a mixed resultant for the two singleton residue roles that need it. It finds the exact leading bound attained by \(A\) modulo \(1013\) in every appropriate event, and no common root algebraically after removal of the proved exact finite boundary factors. For \(s=x_4\) the leading bound is attained by the substituted \(Q\) and it is already coprime to the second determinant. There are 600 ordered singleton and 480 cases for each spent role; the remaining 480 proposed spending roles are the literal reflected \(1\) boundary, impossible before a singleton.

To transfer, fix a prime above \(1013\) in the fixed Lobatto splitting field; the fixed roots reduce to the checked simple distinct nodes. All fixed denominators in the Sylvester expressions are small integration denominators or differences of distinct roots (and the verified nonzero fixed tap for the \(x_4\)-spent substitution). The exact boundary factors ensure the postdivision polynomials remain in the local ring there. The leading coefficient of the first normalized eliminant is a unit, by its checked degree retention. Thus an actual common \(t\), algebraic by that eliminant and nonzero because it is a first active cubic amplitude, is integral over this local ring after monic normalization. In an extension residue field it would reduce to a common algebraic zero of the checked coprime polynomials, impossible. This argument does not assume unknown tableau coefficients can be reduced, does not remove modular-only factors, and also guards the infinite place. The result remains a mathematical analytic exclusion with independent exact stand-alone arithmetic, not an end-to-end native Lean theorem.
