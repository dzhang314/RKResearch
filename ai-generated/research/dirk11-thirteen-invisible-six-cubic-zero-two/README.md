# No two-ghost gap in the zero-multiplier cubic DIRK11/13 chart

**Result.** In the same normalized invisible-six cubic DIRK11/13
chart and notation as the [five-initial-ghost packet](../dirk11-thirteen-invisible-six-cubic-zero-five/README.md),
there cannot be two ghosts between the fourth and fifth regular
reverse rows. This closes both remaining \(\alpha=0,\tau=0\)
cubic counts, \((0,2,4)\) and \((0,3,3)\). Combined with the
five-prefix proof the entire zero-reciprocal-multiplier cubic
chart with \(\alpha=0\) is impossible. We do **not** exclude
nonzero \(\tau\), another \(\alpha\), or arbitrary tableaux. The
unrestricted real DIRK11 interval is unchanged, **13–14**.

Use precisely the true rooted-space ranks and signed normalization
of that packet. In particular \(Z_5=G\mathcal P_2\),
\(Z_6=G\mathcal P_3+K H_{\rm bary}\); \(G_V=0\) at the fourth
ordinary reverse clock \(V\), while \(H_{{\rm bary},V}\ne0\).
Here \(Z_j=\operatorname{Ann}(E_{10-j})\). For each of the three
old regular clocks \(r\), \(G_r\ne0\) and, after one common
rescaling, \(k(r)=G_r/b_r=r(r-V)/D(r)\).
The old hull \(R_3\) is monic cubic; it is disjoint from every
ghost clock since \(U(X)=-R_3(1-X)\) is live on ghosts.
The first packet's ordinary clock reconstruction and hypotheses
of characteristic zero apply. No weight sign or field ordering
is used below.

## 1. Actual weighted matches and paid commutators

Put \(P_0=YR_3(Y)\) and \(m=(Y-V)/D(Y)\bmod R_3\).
For \(j=0,1\), let the degree-at-most-three polynomial
\(S_j=Y(Y^j m\bmod R_3)\), and subtract one multiple of \(P_0\)
to kill the fourth ordinary reverse donor:
\[
 P_j^*=S_j-P_0\,\frac{S_j(V)}{P_0(V)}.
\]
The denominator is live by distinct regular clocks. These
quartics agree with \(Y^j k\) on the old triple and vanish at
both the actual terminal and \(V\). Since there is no ghost
before \(V\), \(W(P_j^*)-Y^jG\) is identically zero on the
complete inclusive prefix through \(V\).

Let \(z\) and \(w\) be the physical first and second ghosts after
\(V\), both before the fifth ordinary reverse row \(B\). Their
clock values are distinct. Write \(N_D\) for the restriction of
actual transpose taps to that ghost block. On its rows
\[
 N_D(Y^jG)=G r_j(Y),
 \qquad r_j=I(P_j^*)/k\bmod R_3 .
\]
Indeed \(W(I P_j^*)-NW(P_j^*)\in Z_5\) by the actual quartic
primitive; \(N(Y^jG)\) is also in \(Z_5\). On the old regular
rows, \(NW(P_j^*)=N(Y^jG)\) by chronology, so the two
degree-at-most-two multipliers sum to the fitted quotient
\(I(P_j^*)/k\). At ghost rows the output weight is zero.
The weighted difference \(NW(P_j^*)-N(Y^jG)\) therefore
contributes exactly \(-N_D(Y^jG)\) and yields the stated
identity. It imposes no division by a ghost tap.

Now use the genuine commutator
\(\mathcal R=CA-AC-A^2\), with
\(\mathcal R^{\mathsf T}=YN-NY-N^2\).
The two differences
\[
 L_j=\mathcal R^{\mathsf T}\bigl(W(P_j^*)-Y^jG\bigr)
\]
lie in \(Z_6\). For the weighted part this is the actual pairing
\(4+6+1=11\) with \(\mathcal R E_4\subset F_6\).
For the marked \(G\) part, \(Y^j\mathcal R E_4\subset E_7\)
for \(j\le1\) and \(G\in E_7^\perp\).
Each \(L_j\) vanishes through \(V\) by the inclusive support cut
and triangularity of the commutator. Since \(G_V=0\) and
\(H_{{\rm bary},V}\ne0\), its barycentric multiplier is zero.
Its remaining cubic multiplier vanishes at the old three
live entries, so \(L_j=\lambda_j G R_3(Y)\) globally.

At the first ghost the only nonzero donor in each commutator
difference is the inclusive diagonal. The diagonal of
\(\mathcal R^{\mathsf T}\) is \(-d_z^2\).
Thus \(\lambda_j R_3(z)= z^j d_z^2\), whether or not \(d_z=0\).
Since \(R_3(z)\ne0\), \(\lambda_1=z\lambda_0\). The global
row \(L_1-zL_0\) is zero. At the physical second ghost,
the first ghost donor cancels and only the diagonal remains,
giving \((w-z)G_w d_w^2=0\), hence \(d_w=0\).
Neither the first ghost diagonal nor the first ghost clock is
assumed live.

At the first ghost the equations for \(N_D\) give
\(r_1(z)=z r_0(z)\). At the second, the only possibly nonzero
tap within the ghost block is to the first ghost (its diagonal
is zero), so \(r_1(w)=z r_0(w)\). Thus
\[
 r_1(Y)-z r_0(Y)
\]
has both distinct roots \(z,w\). No assumption that either
remaining tap is nonzero is used.

## 2. Independent quintic input and exact unit exclusion

The true grade-six primitive of \(P_5=(Y-V)P_0\) lies in
\(Z_6\):
\[
 W(I P_5)-NW(P_5)=G Q+eH_{\rm bary},\qquad \deg Q\le3.
\]
At each old regular row and \(V\), the tap term is zero.
At \(V\) the \(G\) term vanishes, so \(e=I P_5(V)/h(V)\)
when \(H_{{\rm bary},i}=b_i h(y_i)\) on ordinary nonendpoint
rows and \(h(Y)=YJ_4(Y)\). Consequently
\[
 Q\bmod R_3=Q_0,\qquad
 Q_0=(I P_5-e h)/k\bmod R_3 .
\]
All weighted donor values of \(P_5\) are zero on the complete
inclusive prefix through the two ghosts, and their output
weights and barycentric coordinates are zero. Thus \(Q(z)=Q(w)=0\).
Since \(Q=Q_0+\mu R_3\), a necessary undivided equality is
\[
 Q_0(w)R_3(z)-Q_0(z)R_3(w)=0. \tag{*}
\]

Start the finite-free arithmetic in the exact degree-24
ordinary-clock algebra of the first packet. Recreate both old
quadratic fits \(r_j\) and \(Q_0\); the auxiliary old cubic
only evaluates interpolation and does not choose their ordering.
The cubic \(r_1(z)-z r_0(z)\) has a unit cubic leader in the
residue algebra at 101 (the degree is not inferred from a
vanishing residue). Adjoin \(z\) by this monic cubic over the
localized ordinary-clock algebra. In the resulting rank 72,
the quadratic leader \(c_2\) of \(r_1(Y)-z r_0(Y)\) is also
a unit modulo 101. Thus the second root is reconstructed as
\(w=-c_1/c_2-z\), by the sum of roots, in every candidate.
The left side of (*) is a unit in the whole rank-72 residue
algebra. This is the contradiction for at least two ghosts,
without any assumption about a third.

Run `python3 replay.py` with SymPy. It can import the
sibling first-packet and constant-closure replays or accept
`--first-packet PATH` and `--arithmetic PATH`. All
inversions are multiplied back to one in the appropriate
residue algebra. As in the first packet, finite-free unit
lifting is solely in the prescribed clock algebra. It does
not require reducing any unknown tableau weight, diagonal,
ghost clock, or coefficient. A characteristic-zero candidate
gives an evaluation to its field, where the certified unit
cannot be zero.

The [Lean companion](../../lean/RKCert/ReviewedNative/DIRKOrderElevenInvisibleSixCubicZeroTwo.lean) certifies four scalar steps, including the second diagonal and crossing primitive. The [pinned Lean/Mathlib 4.36.0 audit](lean-audit-4.36.0.txt) reports standard axioms only. The finite elimination and rooted transfer remain separate.
