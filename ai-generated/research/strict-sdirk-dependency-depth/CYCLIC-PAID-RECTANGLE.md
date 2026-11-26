# A paid rectangle recurrence and a nonzero diagonal obstruction at s=p

Mathematical proof, not kernel-checked. Let \(A=\gamma I+B\) be a common-
diagonal triangular RK tableau over a characteristic-zero field, with
\(B\) strictly lower triangular and passing every rooted order condition
through \(p=s\). Write \(e=1\), \(c=Ae\), \(x_i=c_i-\gamma\).
The cyclic branch is
\[
                   L=b^TB^{s-1}e\ne0.
\]
It implies \(b_s\) and all actual adjacent coefficients \(B_{i,i-1}\)
are nonzero. No sign, clock distinctness, or Laguerre-root assumption
is made in this branch.

**Main diagonal obstruction.** For \(s=p\ge8\) in the cyclic branch,
\(\gamma\ne0\) is necessary and an explicit nonzero polynomial
\(\mathcal P_s\in\mathbb Q[\gamma]\), of degree at most \(6s-18\), must
vanish at \(\gamma\). Thus no transcendental or higher algebraic-degree
common diagonal can attain order \(s\) on \(s\) stages in this branch.
Without assuming the earlier no-cancellation theorem, any
noncyclic branch just satisfies \(L=0\), a separate scalar polynomial.
Consequently multiplying by \(L\) gives an unconditional finite set of
possible diagonals already from the present proof. With the separate
no-cancellation theorem (\(p=s\ge7\)), \(\mathcal P_s\) alone suffices.
No existence is claimed for its roots.

**Clock geometry.** In the nondegenerate determinant branch all clocks
must form a single arithmetic progression, with nonzero step. In the
degenerate branch the rectangle recurrence factors; the only possible
failure of this progression has an arithmetic prefix and an affine
tail of the same nonzero step, with at most two unresolved boundary
clocks, or an arithmetic prefix through the third-from-last stage and
two unresolved final clocks. In particular, repeated clocks cannot
evade the diagonal obstruction. The proof does not use a clock
tomographic inverse.

## 1. Exact paid one- and two-hole moments

Let
\[
 \lambda_j=\sum_{u=0}^j\binom ju\frac{(-\gamma)^{j-u}}{(u+1)!},
 \qquad
 (j+2)\lambda_{j+1}=(1-2(j+1)\gamma)\lambda_j
                                  -j\gamma^2\lambda_{j-1}.
 \tag{1}
\]
The first is \(b^T B^j e\) when \(j+1\le p\), by expansion and the
tall rooted trees. The recurrence is a polynomial identity from
\(z\sum \lambda_j z^j=\exp(z/(1+\gamma z))-1\).
Use the five values
\[
  L=\lambda_{s-1},\quad M=\lambda_{s-2},\quad K=\lambda_{s-3},
  \quad R=\lambda_{s-4},\quad S=\lambda_{s-5},
\]
and set \(N=s-3\). The model operators on formal polynomials in \(y\)
are \(J f(y)=\int_0^y f(u)\,du\), \(T=J-\gamma I\),
\(X f(y)=yf(y)\); output is \(\int_0^1\). The actual word operators
are \(B\) and \(C=\operatorname{diag}(c)\). Indeed a stage tree \(t\)
has exact model \((|t|/\rho(t))y^{|t|-1}\), with \(\rho(t)\) the tree
factorial. \(J\) models a unary root, \(X\) adjoining a leaf at the
root, and the integral models \(1/\rho(t)\). Expanding \(B=A-\gamma I\)
shows that a word with \(d\) strict hops and \(j\) clock factors pays
at most tree order \(d+j+1\).

For convenience put
\[
\begin{aligned}
 \kappa&=L+2\gamma M+\gamma^2 K,\\
 \eta&=M+2\gamma K+\gamma^2 R,\\
 V_3&=L+3\gamma M+3\gamma^2 K+\gamma^3R,\\
 V_4&=L+4\gamma M+6\gamma^2 K+4\gamma^3R+\gamma^4S.
\end{aligned}
\]
They are respectively the integrals of the evaluations on 1 of
\(J^2T^N,\ J^2T^{N-1},\ J^3T^{N-1},\ J^4T^{N-2}\).
The clock-word formulas follow from
\([X,J]=J^2,\ [X,T]=J^2,\ [X,J^2]=2J^3\). In detail, for
\(0\le a\le b\le d\),
\[
\begin{aligned}
 T^{d-a}X T^a1 &= JT^d1+aJ^2T^{d-1}1,\\
 T^{d-b}X T^{b-a}X T^a1
   &=2J^2T^d1+(b+3a)J^3T^{d-1}1+a(b-1)J^4T^{d-2}1.
\end{aligned}
\tag{2}
\]
Terms with zero coefficient are omitted. The first follows by
commuting \(X\) through \(T^a\) and using \(X1=J1\); for the second
pass the second \(X\) through the resulting \(J\) and \(J^2\) terms.
The case \(a=b\) is the same-slot square. A word with \(d=s-2\)
and one clock, or \(d=N=s-3\) and two clocks, is therefore paid.

A strict path of length \(s-2\) corresponds to the one omitted
physical stage \(j\). Let \(\omega_j\) be its weight: the product of
actual strict entries on the path times the last retained stage's
output weight. Let \(T_k'=\sum_{j\le k}\omega_j\), with
\(\sum_j\omega_j=M\). Position \(k\) from the earliest retained stage
has physical index \(k+1\) if \(j\le k\), and \(k\) otherwise.
Thus the one-clock moment from (2), shifted by \(\gamma\), says
\[
           M x_k+T_k'(x_{k+1}-x_k)=A_k',
              \qquad A_k'=L+(k-1)\kappa.
 \tag{3}
\]

A strict path of length \(s-3\) corresponds to two omitted indices
\(j<k\). Write \(\Omega_{j,k}\) for its weighted product, and
brackets for summation over this signed path measure (total \(K\)).
For \(k-j\ge2\),
\[
                        L\Omega_{j,k}=\omega_j\omega_k.
 \tag{4}
\]
The two single-hole replacements in the full path affect separate
edges if the holes are separated: an interior omission bypasses
its two neighboring adjacent edges by a single skip edge; an
endpoint omission changes a path endpoint. The replacements may
share a retained vertex, but no edge. Dividing their weights by
the nonzero full-chain product \(L\) proves (4), including zero
weights. This fact is specific to one actual triangular matrix,
not a property of freely chosen joint path measures.

## 2. Rectangle identity without clock distinctness

Write \(Z_h\) for the shifted actual clock seen at position \(h\)
on a two-hole path. Take \(1\le h\le \ell\le s-2\). On this path the
test
\[
                   (Z_h-x_h)(Z_\ell-x_{\ell+2})
\]
vanishes unless \(j\le h\) and \(k>\ell+1\): if no hole is passed at
\(h\) the first factor is zero, and if both are passed at \(\ell\)
the second factor is zero. The surviving rectangle has exactly
one omission passed at each position, so the value there is
\(-(x_{h+1}-x_h)(x_{\ell+2}-x_{\ell+1})\). This reasoning also
holds when \(h=\ell\). If some clocks coincide, the rectangle may
have zero value as well, which causes no problem. All its hole
pairs are separated, so (4) and then (3) give
\[
 L\langle(Z_h-x_h)(Z_\ell-x_{\ell+2})\rangle
                 =(A_h'-M x_h)(A_{\ell+1}'-M x_{\ell+2}).
 \tag{5}
\]
More explicitly the rectangle weight before multiplication by its
constant value is \(T_h'(M-T_{\ell+1}')/L\). This is an exact
multiplication identity, not a division by clock differences.

Put \(a=h-1,\ b=\ell-1\), so \(0\le a\le b\le N\).
The paid shifted one-clock moments of the two-hole paths are
\(\mu_a=M+a\eta,\ \mu_b=M+b\eta\).
The paid shifted product moment from (2) is
\[
 \nu_{a,b}
   =L+(b+1)\kappa+a(2V_3+\kappa-V_4)+ab V_4.
\]
Indeed the unshifted product is
\(2\kappa+(b+3a)V_3+a(b-1)V_4\); subtract \(\gamma\) times each
unshifted single moment, add \(\gamma^2 K\), and use
\(V_3-\gamma\eta=\kappa\). Define
\[
 D=LK-M^2,\quad E=M\kappa-L\eta,\quad F=LV_4-\kappa^2,
 \quad H=M\kappa,\quad G=L(2V_3-V_4)-\kappa^2 .
 \tag{6}
\]
Expanding (5), cancelling the common \(L(L+(b+1)\kappa)\),
and dividing by \(a\) when \(a>0\), gives the central recurrence:
\[
 \boxed{\quad
 (D u_a+E)x_{b+3}+(E u_a+F)b+H u_a+G=0,\qquad
 1\le a\le b\le N,\quad u_a=\frac{x_{a+1}}{a}.
 \quad}
 \tag{7}
\]
Before the division, the four groups are
\(D x_{a+1}x_{b+3}\), \((H+bE)x_{a+1}\),
\(a E x_{b+3}\), and \(a(G+bF)\).
The index \(a=0\) is tautological since \(x_1=0\).

As a check and a separate unconditional consequence, at
\(\gamma=0\) one has \(L=1/s!,M=sL\),
\(D=-M^2/s,\ H=M^2/s,\ E=F=G=0\).
The nonzero \(x_2=B_{21}\) and \(a=1\) in (7) force
\(c_4=\cdots=c_s=1\). If \(s=p\ge5\) the equal adjacent pair at
\(k=4\) in (3) demands \(M=4L\), contradicting \(M=sL\).
This proves the classical \(s=p\) ERK exclusion for \(p\ge5\) by
these paid path identities. In what follows \(\gamma\ne0\).

## 3. Clock rigidity and the degenerate alternative

Let \(\Delta=DF-E^2\). If \(\Delta\ne0\), for every
\(1\le a\le N-1\) we have \(D u_a+E\ne0\):
otherwise the two distinct \(b\) values in (7) force
\(E u_a+F=0\), making \((u_a,1)\) a kernel vector of the
nondegenerate matrix with rows \((D,E),(E,F)\).
The \(a=1\) equation now gives an affine tail \(x_4,\ldots,x_s\)
as a function of \(b\), and the others give that same slope on
their shared, at-least-two tail positions. The fractional map
\((E u+F)/(D u+E)\) is injective under \(\Delta\ne0\), so
\(u_1=\cdots=u_{N-1}=\alpha\). Thus \(x_i=\alpha(i-1)\) for
\(i\le s-3\). At \(s\ge8\) the tail and prefix overlap on at
least \(i=4,5\), so the entire clock sequence is
\(c_i=\gamma+\alpha(i-1)\), with \(\alpha=x_2\ne0\).
Substitute \(u_1=\alpha\) and \(x_{b+3}=\alpha(b+2)\) in (7)
and compare the affine coefficients of \(b\):
\[
 D\alpha^2+2E\alpha+F=0,\qquad
                     (H-2E)\alpha+G-2F=0.
 \tag{8}
\]
In particular \((D\alpha+E)^2=-\Delta\); for real coefficients
this branch requires \(\Delta<0\).

Suppose \(\Delta=0\). Then \(D\ne0\). Indeed if \(D=0\) then
\(E=0\), and \(D=E=0,\gamma\ne0,L\ne0\) give
\(K=M^2/L\) and \(R=MK/L\), using
\(E=-2\gamma D+\gamma^2(MK-LR)\).
If \(M=0\), the top recurrence in (1) would give \(L=0\).
Otherwise \(R,K,M,L\) are geometric with nonzero ratio
\(\theta=L/M\). Comparing the two consecutive recurrence rows
after dividing each by its first sequence value yields
\(\theta^2=-2\gamma\theta-\gamma^2\). Then \(\theta=-\gamma\),
and substitution into either recurrence yields \(\gamma=0\),
a contradiction.

Now \(F=E^2/D\). If \(DG-HE\ne0\), no \(u_a=-E/D\) can solve (7),
even at one \(b\). All tails have slope \(-E/D\),
and by evaluating at the shared position \(b=N\), the fractions
\((H u_a+G)/(D u_a+E)\) coincide. They are injective under
\(DG-HE\ne0\), so all \(u_a\), including \(a=N\), coincide.
The prefix now extends through \(s-2\), and overlaps the tail at
two places for \(s\ge7\). It forces \(u_a=-E/D\), a contradiction.
Consequently \(DG-HE=0\), and the exact degenerate recurrence factors:
\[
              (D u_a+E)\left(x_{b+3}+\frac{E}{D}b+
                                           \frac{H}{D}\right)=0.
 \tag{9}
\]
Its possible common step \(\alpha_0=-E/D\) is nonzero. If \(E=0\),
then \(F=G=0\); since \(u_1=x_2\ne0\), the tail is constant
\(-H/D\). Two different zero adjacent gaps there in (3) would
give \(\kappa=0\), then \(H=0\), and applying (3) again would give
\(L=0\). These gaps exist for the claimed range.

If all \(u_a=\alpha_0\), the prefix through \(s-2\) is fixed
arithmetic and (9) leaves only the last two clocks unresolved.
Otherwise let \(a_0\) be the first index with \(u_{a_0}\ne\alpha_0\).
The prefix through physical index \(a_0\) is arithmetic, and (9)
fixes the tail from \(a_0+3\) onward with the same step \(\alpha_0\),
possibly with an offset. There are at most two unresolved
boundary clocks between the runs, of which the first is not the
prefix continuation by construction. Each run is individually
distinct in characteristic zero. This is a necessary form, not a
construction or a claim that the boundary clocks are unrestricted
by the other RK equations. In particular, an actual clock collision
in the cyclic range \(s=p\ge8\) forces the degenerate branch.

## 4. One nonzero polynomial also covers the degeneracy

Define
\[
 \begin{aligned}
 U&=MK-LR, & V&=LS-K^2,\\
 P&=H-2E=2L\eta-M\kappa,\qquad
 & Q_1&=-2LK+2\gamma(MK-3LR)+\gamma^2(K^2-3LS).
 \end{aligned}
\]
Then direct expansion gives
\[
 \begin{aligned}
 E&=-2\gamma D+\gamma^2 U,&
 F&=4\gamma^2 D-4\gamma^3 U+\gamma^4 V,\\
 G-2F&=-2\gamma P+\gamma^2 Q_1,&
 \Delta&=\gamma^4(DV-U^2).
 \end{aligned}
 \tag{10}
\]
For example \(G-2F=2L V_3-3L V_4+\kappa^2\); add
\(2\gamma P\) and expand to obtain \(\gamma^2Q_1\).
Also
\[
 DV-U^2=L\det
 \begin{pmatrix}S&R&K\\R&K&M\\K&M&L\end{pmatrix}.
\]
Thus degeneracy is exactly a consecutive 3-by-3 shifted tall
Hankel degeneracy in the nonzero cyclic case.

For the nondegenerate branch put
\(\beta=(\alpha-2\gamma)/\gamma^2\).
Equations (8) and (10) imply
\(D\beta^2+2U\beta+V=0,\ P\beta+Q_1=0\), even when \(P=0\).
In particular the following polynomial vanishes by eliminating
\(\beta\) without dividing by \(P\):
\[
                  \mathcal P_s=D Q_1^2-2U P Q_1+V P^2.
 \tag{11}
\]
For the degenerate branch, \(DG-HE=0\) and \(\Delta=0\) imply
\(D Q_1-PU=0\), since
\(DG-HE=2\Delta+\gamma^2(DQ_1-PU)\) by (10).
Use the identity
\[
           D\mathcal P_s=(D Q_1-PU)^2+(DV-U^2)P^2
\]
and \(D\ne0\) to obtain (11) there as well.

Finally \(\mathcal P_s\) is nonzero as a polynomial, without any
assumption on the allowed field. At the test value \(\gamma=0\)
write \(t_*=M(0)^2/s\); the factorial values give
\[
 D=-t_*,\quad U=2(s-1)t_*,\quad V=-2(s-1)(2s-3)t_*,
 \quad P=t_*,\quad Q_1=-2(s-1)t_*.
\]
Consequently \(\mathcal P_s(0)=2(s-1)t_*^3\ne0\).
For the degree bound, the first two highest terms of
\(\lambda_j\) are \((-\gamma)^j(1-j/(2\gamma))\) in
Laurent notation at infinity. Products with equal sums of
indices have those terms equal, hence
\(\deg D\le2s-6,\ \deg U\le2s-7,\ \deg V\le2s-8\).
The integral models above give
\(\deg\kappa\le s-3,\ \deg\eta,\deg V_3\le s-4,\
\deg V_4\le s-5\). Therefore
\(\deg P\le2s-5,\ \deg Q_1\le2s-6\) using (10), and
\(\deg\mathcal P_s\le6s-18\) follows. This is a bound on the
diagonal's degree over \(\mathbb Q\), not on the full coefficient
field of a tableau.

This proves the claimed obstruction at \(s=p\ge8\). If the earlier
no-cancellation result is not imported, \(L(\gamma)\mathcal P_s(\gamma)\)
is a nonzero unconditional polynomial obstruction of degree
at most \(7s-19\), with nonzero constant term. For real diagonals,
each fixed \(s=p\) in the range has an open interval around zero
excluded, since that polynomial is nonzero at zero and the zero
diagonal was excluded directly. Together with the separate
\(s\ge p\) common-diagonal theorem for \(p\ge5\), any prescribed
transcendental diagonal forces \(s\ge p+1\) for \(p\ge8\).
This last lower bound is for prescribed such diagonals, not for
an unrestricted search over all common diagonal values, and not
for differing-diagonal DIRK.

The earlier [nonvanishing theorem](COMMON-DIAGONAL-ONE-SLACK.md) supplies the strict full path automatically for common-diagonal order \(p=s\ge 8\). The polynomial remains a necessary test; it does not give a realization at any root.
