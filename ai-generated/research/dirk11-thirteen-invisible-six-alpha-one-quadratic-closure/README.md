# Complete quadratic-carrier exclusion with one first reverse ghost

**Result.** No normalized invisible-six no-late DIRK11/13 chart over a
characteristic-zero coefficient field has a quadratic carrier and
\(\alpha=1\). Both possible counts \((\beta,\gamma)=(1,4),(2,3)\)
are excluded for every fourth and fifth regular reverse diagonal.
This is not an unrestricted DIRK stage lower bound. Real DIRK11
remains **13–14**.

## 1. Literal chronology and fixed carrier

Use the original actual order, signed support and paid ranks of the
[invisible-six chronology](../dirk11-thirteen-invisible-six-no-late/README.md)
and [forward masks](../dirk11-thirteen-invisible-six-prefix/README.md).
The five regular ordinary nodes are distinct and not endpoints, and
the six zero-weight ghost clocks are pairwise distinct and live for
both heads. The actual reverse order is
\[
 T,v,u,w,z,V,x,[\beta-1\text{ ghosts}],B,[\gamma\text{ ghosts}],O.
\]
The first two marked ghost clocks \(z,x\) may share values with
unrelated regular clocks. The bound \(\gamma\le4\) is the true grade-five forward mask:
each initial forward ghost sees zero inclusive donors of \(C\phi\),
where \(\phi=U(c)-g\). Its ghost donors vanish and the origin factor
is zero. Hence \(I_X(XU)+UQ_2\), \(\deg Q_2\le2\), vanishes at
all \(\gamma\) distinct prefix ghost clocks. If \(\gamma=5\), its
degree at most four makes it identically zero. Then \(U\mid I_X(XU)\);
comparing highest and lowest powers shows the quotient is a multiple
of \(X^2\), and comparison at each live coefficient forces \(U\) to
be a monomial in characteristic zero. This contradicts the quadratic
reciprocal liveness at the origin (or the two first clean marks).
Thus the actual five-prefix \(\beta=0\) count is excluded, and
\(\gamma\ge3,\ \alpha+\beta+\gamma=6\) leave exactly the two counts above.

Use \(Y=1-c\), \(N=A^{\mathsf T}\) in literal reverse order,
\(W(f)=b_{\rm wt}f(Y)\), and zero primitive \(I\). The
[quadratic boundary proof](../dirk11-thirteen-invisible-six-alpha-one-quadratic-boundary/README.md)
justifies the live reciprocal normalization \(k(y)=G_y/b_y=yJ_4(y)/U_r(y)\)
at the five regular nodes, with \(U_r(Y)=U(1-Y)\). In the old cubic
\(R=(Y-v)(Y-u)(Y-w)\), write \(m=G/(Yb_{\rm wt})\bmod R\),
\(P=Ym,\ P_0=YR\). Since \(U_r\) is quadratic,
\(U_r=(J_4/m)\bmod R\) **as a polynomial**. There is no free
cubic-hull parameter. Every old \(m\) value and the corresponding
multiplication determinant are live.

In the old adjugate gauge let \(n\ne0,\ M=nU_r\), set
\(L_0=IP_0/Y,\ L_1=I(YP_0)/Y\), and let \(W_0^\#,Q_0^\#\)
be the \(n\)-scaled reduced fits of \(L_0/m,L_1/m\).
Let \(\ell^\#,\rho^\#\) similarly be the fits of \(IP/P,I^2P/P\)
after cancelling the polynomial factor \(Y\). The actual \(\ell\)
is affine. Define exact polynomial quotients
\(D_4=(L_0M-W_0^\#J_4)/R\), \(D_5=(L_1M-Q_0^\#J_4)/R\).
On every old profile write \(z=p/q\) by its own exact first-gap
formula with \(q\ne0\).

## 2. Two genuine reverse rows, without any fifth diagonal

At \(V\) put \(u_V=M(V),\,j=J_4(V),\,h=Vj,\,C_V=D_4(V)\).
The actual weighted quartic gives \(C_V=d_Vu_V\).
The [literal adjacent reads](../dirk11-thirteen-invisible-six-early-profile-census/README.md#2-a-true-adjacent-clean-read-without-ghost-weight-reconstruction)
give \(T=\ell(V)k-IP(V)+d_V(P(V)-k)\) and
\((z-V)T=I^2P(V)-\rho(V)k\), with \(k=G_V/b_V\) and
\(T=N_{V,z}G_z/b_V\). They use the degree-three comparator
\(YP-[Y^2]m\,P_0\) as well as the quartic to remove its old
degree-four part. The genuine homogeneous adjacent signal is
\[
 \mathcal A=(p-qV)\big[(\ell^\#(V)h-IP(V)u_V)u_V+
                 C_V(P(V)u_V-nh)\big]
       -q(I^2P(V)u_V-\rho^\#(V)h)u_V=0 .
\]
There is no division by \(1+\ell_1,V-z\), or a diagonal.

The [matched prefix proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md)
uses only \(\deg U_r\le3\). Define
\(K_*=(V-z)(k-P(V))/P_0(V)\),
\(Q_4=(Y-z)P+K_*P_0\), \(D=(Y-z)G-W(Q_4)\).
The actual \(D\) vanishes through \(V\). Its commutator vanishes by
the injective \(Z_6\) prefix: the zero old samples give
\(Q+\theta U_r=\mu R\) by degree at most three; the ordinary \(V\)
and ghost \(z\) samples kill \(\mu,\theta\). Thus \(d_x=0\),
and \(ND=GL-W(IQ_4)\) gives
\(L=(Y-z)\ell-\rho+K_*W_0=\lambda(Y-z)(Y-x)\), \(\lambda\ne0\).
For the latter leader, if \(L=0\), the four regular samples and
polynomial origin give \(IQ_4\) proportional to \(P_5=(Y-V)P_0\).
The derivative at zero vanishes on the left and is live on \(P_5\).
This forces \(Q_4=0\), contradicting its old samples
\((y-z)P(y)\) at three distinct \(y\). Here \(W_0=W_0^\#/n\).

Set \(c_q=P_0(V)u_V,\ k_q=(qV-p)(nh-P(V)u_V)\). The actual
\(L^\#=c_q((qY-p)\ell^\#-q\rho^\#)+k_qW_0^\#=c_q q nL\).
Thus \(x=x_n/x_d\), where \(x_d=q[Y^2]L^\#\ne0\) and
\(x_n=-q[Y]L^\#-p[Y^2]L^\#\); this leader has been paid.

The true weighted quintic error is
\(W(IP_5)-NW(P_5)=GQ_5+\theta H_{\rm bary}\), with
\(\deg Q_5\le3\) by the actual grade-six space. Every inclusive
weighted input through \(x\) is zero (old nodes, terminal and \(V\)
annul \(P_5\); ghost weights vanish), so \(Q_5(z)=Q_5(x)=0\).
Its old and \(V\) samples yield
\[
 B_5=j(Q_0^\#-VW_0^\#)+(D_5(V)-VD_4(V))R
     =j n(Q_5+\theta U_r).
\]
At \(V\) this follows from the zero weighted prefix regardless of
its diagonal; the old samples identify the remainder modulo \(R\).
The cross \(Q^\#=q^3[M(z)B_5-B_5(z)M]\) is a multiple of
\(Q_5\). Both evaluations use nominal degree three with a padded
zero cubic coefficient for \(M\). If \(Q^\#=\sum_i a_iY^i\),
synthetic division gives
\[
 D^\#=(q^2a_1+pqa_2+p^2a_3)+(q^2a_2+pqa_3)Y+q^2a_3Y^2,\quad
 (qY-p)D^\#=q^3Q^\# .
\]
The genuine quintic signal is
\(\mathcal Q=x_d^2D^\#(x_n/x_d)=0\), since \(x\ne z\).
No quintic leader or ordinary–ghost difference is inverted.
Neither row uses a literal donor from \(B\), a fifth diagonal,
or a cubic-carrier forward hull.

## 3. Exact direct noncontact projection

For the [regular direct \(F_n\) old fit](../dirk11-thirteen-invisible-six-early-profile-census/README.md),
build the exact monic rank-12 tower over \(\mathbb Q[V]\) using
\(S=132J_4(V)\), the ordinary quartic for \(SB\), and the
normalized cubic for \(L_3S^2s\), \(L_3\) the scaled \(F_n\) leader.
The old ratio \(r=6c_2s/(c_1+6s)\) and the leaders are live.
The only removed nonconstant coefficient content is supported on
\(V(V-1)J_4E_+E_-E_{\rm rep}\); the endpoint and repeated-root
pencil factors and Jacobi common root are excluded for the actual
five distinct nonendpoint ordinary clocks. Each division is exact.
For the horizontal scale \(Y'=SY\), use \(N'=SN\),
\(P'=S^3P(Y'/S),\,G'=S^3G\) in the monic old gauge.
Then \(U_r'=S^2U_r(Y'/S)\) and the uncleared adjacent residual
scales by \(S^5\), while \(x',z'=Sx,Sz\) and
\(Q_5'=S^3Q_5(Y'/S)\). Arbitrary common old profile gauge factors
are harmless. The independent rational coordinate audit compares
the exact unscaled and cleared formulas at both scales for four
generic old profiles (not claimed to be tableaux).

The exact norm of \(\mathcal A\) has degree **1568**, squarefree
degree **352**. An actual evaluation killing \(\mathcal A\)
annihilates its multiplication image, so its specialized norm
vanishes. Apart from \(J_4,E_+,E_{\rm rep}\), the complete exact
factor list and image ranks are:

| Irreducible degree, primitive constant where small | Live guard \(g\) | Exact cap | Residue degree at 103 | \(g\mathcal A\) rank; joint with \(g\mathcal Q\) |
|---|---|---:|---:|---|
| 12, 16227 | scaled \(c_1+6s\) | 11 | 12 | 11; 11 |
| 12, 54123 | lower \(c_2\) | 9 | 4 | 9; 9 |
| 60, −1461941766456 | old fit norm | 11 | 1 | 11; 11 |
| 252 | \(1\) | 12 | 1 | 11; 12 |

The caps are exact upper bounds on \(\dim\operatorname{im}g\):
the two cap-11 factors divide the exact guard norms,
and \(c_2\) is affine in \(SB\) with coefficient one and zero
exact lower norm, giving cap \(3\cdot3=9\) after the upper
cubic extension. The nonzero residue minors certify the matching
ranks in the exact coefficient fields. The columns lie in
\(\operatorname{im}g\), so fill it; an actual solution killing both
signals would kill \(g\), contradiction. A residue factor is
only a rank witness; no tableau or clock is reduced modulo 103.

## 4. Exhaustive finite ledger

The other exact models are reconstructed from the old finite proof
sources, stopping before their carrier equations. The signal
\(\mathcal A\) already has full rank in every model retained here:

| Old profile | Prime | Exact image rank / dimension |
|---|---:|---:|
| \(m=1,Y^2\) | 103 | 1/1, 1/1 |
| mixed \(c_2s=c_0,\ rs\ne0\) | 101 | 1/1 |
| lost ratio \(c_1+6s=c_2=0\) | 103 | 2/2 |
| alternate \(F_1,F_2\) | 103 | 1/1, 2/2 |
| alternate repeated \(F_n\), \(H_3,H_5\) | 103 | 2/2, 2/2 |

Both roots are retained for every affinity or physical clock lift
with two possibilities. The monomial \(m=Y\) already fails the
first-ghost gate \(-3c_0^2/10\). The mixed \(r=0\) case and direct
\(F_1\) have \(\ell_1=-1\), excluded by the
[first-ghost bridge](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-bridge/README.md)
and [degree-60 slope proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one/README.md).
The latter only uses true reverse prefix and middle gates with
arbitrary \(E=qK_*\), never a cubic leading coefficient or a fifth
diagonal; its replay is part of the boundary companion. Direct
\(F_2\) has \(m\mid R\), impossible. At vanishing old affine pivot,
both coefficients vanish and the alternative old quadratic roots
are retained. After the earlier contacts and \(F_1,F_2\), the true
remaining \(F_n\) root must be repeated by differentiation of the
exact resultant at those two zero coefficients. Its two exact
discriminant fields and the leader-loss fallback are in the table.
No disjointness of old factors is assumed.

## 5. Degree and reciprocal scope

This packet treats **degree exactly two**. The reciprocal multiplier
cannot be zero for any nonzero \(U\) of degree at most two: the actual
old triple has three distinct clocks and individually live \(G\),
so zero multiplier would make all three roots of \(U\). The
zero polynomial itself is not an actual carrier of live ghosts.
The separate [constant packet](../dirk11-thirteen-invisible-six-constant-exclusion/README.md)
covers degree zero for all \(\alpha=1\) counts. For degree one the
same forward-prefix argument gives \(\gamma\le3\), leaving precisely
\((\alpha,\beta,\gamma)=(1,2,3)\), excluded by the
[linear packet](../dirk11-thirteen-invisible-six-linear/README.md).
Thus those independent results plus this one cover degree at most
two, not arbitrary \(U\) on their own. Cubic zero reciprocal is a
different branch, excluded by the
[five-prefix proof](../dirk11-thirteen-invisible-six-alpha1-five-zero/README.md)
for \(\beta=0\) and the [zero-cubic proof](../dirk11-thirteen-invisible-six-alpha-one-zero-cubic/README.md)
for \(\beta=1,2\). The live cubic closures are not reproved here.

Run **bash verify.sh PATH/TO/ai-generated/research** with SymPy and
python-flint 0.9. The native row module checks the homogeneous
adjacent read and the second-root coordinates; the boundary module
also certifies the distinct-root divider. The rooted order-space
ingress and finite image arithmetic are exact written/source
proofs rather than one native end-to-end HasOrder theorem.
