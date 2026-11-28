# Exact grade-five observer space and a terminal Möbius gate

This strengthens the rational split-host
[terminal cut](../erk10-fifteen-split-host-terminal/README.md)
in the only remaining ten-label geometry
\(0,1,b,c,c,d,e,f,g,h,R\).
Keep its notation for \(I,J,H,\boldsymbol w,\boldsymbol u,
\boldsymbol\eta,\boldsymbol L,\boldsymbol Z,\boldsymbol G_*,M,G_0,N\).
We use its unconditional \(u_e\ne0\), \(Z_e=0\),
and \(K_{e,d}=0\). No condition on \(A(H)\) or
on live scores at every singleton is added.

## The actual ten-dimensional grade-five space

Let \(H_5\) be the span of the true reverse words
through length five applied to \(\boldsymbol w\)
(equivalently, the nominal degrees through five
together with \(D_5\)). The actual size-five host
error \(\boldsymbol\eta\ne0\) annihilates it, so
\(\dim H_5\le10\). We prove
\[
 H_5=\boldsymbol w\odot{\cal P}_5(\boldsymbol Y)
            \ \oplus\
       \boldsymbol u\odot{\cal P}_3(\boldsymbol Y).
                                                        \tag{1}
\]
The two spaces on the right are included in \(H_5\):
nominal powers of \(Y\) are literal mark words;
\(\boldsymbol u\) is a true grade-two defect, so up
to three of its marks are paid.

The physical two rows at the early pair \(c\) have
independent restrictions of \(\boldsymbol w,\boldsymbol u\).
Otherwise a direction supported on those two rows
would annihilate \(D_4=\boldsymbol u\odot{\cal P}_2\)
and the nominal columns. Its support is in the
early reverse head, contradicting the
[off-prefix rank-three witness](../erk10-fifteen-split-host-rank/LARGEST-CLOCKS.md#three-annihilators-independent-off-the-early-reverse-head).
This works regardless of either individual score.

Suppose \(\boldsymbol w\odot P(\boldsymbol Y)
+\boldsymbol u\odot Q(\boldsymbol Y)=0\),
\(\deg P\le5,\deg Q\le3\).
At the live first endpoint \(0\) one gets \(P(0)=0\),
and pair independence gives \(P(c)=Q(c)=0\).
Pairing with \((H-Y){\cal P}_3\) kills the marked
\(\boldsymbol u\) term because the product tested
has degree at most seven and zero forward constant.
Scalar precision through nine then shows
\(I((H-Y)P S)=0\) for every cubic \(S\).
Since \(P(0)=0\), \(P/Y\) is degree at most four
and orthogonal to all cubics under the rescaled
positive weight \(y(1-y)\), \(y=Y/H\).
Its only possible line is the
[Jacobi quartic](../erk10-fifteen-tilt-fullmark-closure/DENSE-JACOBI.md#three-allowed-exceptional-site-sets-all-impossible)
\[
 L_4(y)=42y^4-84y^3+56y^2-14y+1 .
\]
The rational root \(P(c)/c=0\) is impossible
on that nonzero line. Hence \(P=0\), and \(Q=0\)
because \(\boldsymbol u\) has at least eight
nonzero aggregate sites. Thus the right of (1)
has dimension \(6+4=10\), proving equality.
In particular all ensuing polynomial decompositions
are unique. This deduction uses rational Jacobi
arithmetic, not coefficient positivity of the method.

## Both primitive nominal parts are uniquely determined

Define \(C_L(Y)=Y L_4(Y/H)\), with \(C_L(c)\ne0\).
Write
\[
 K\boldsymbol Z=\boldsymbol w\odot P_Z(\boldsymbol Y)
                  +\boldsymbol u\odot Q_Z(\boldsymbol Y),
 \qquad
 K\boldsymbol G_*=\boldsymbol w\odot P_G(\boldsymbol Y)
                  +\boldsymbol u\odot Q_G(\boldsymbol Y)
\]
by (1). The grade-five real defects relative to
\(JM,JG_0\) respectively annihilate
\((H-Y){\cal P}_3\); their marked \(\boldsymbol u\)
terms do too. The two nominal differences vanish
at \(0\) by strictness and the live endpoint.
As in (1) each is therefore a scalar multiple of
\(C_L\). At the pair \(c\) both literal outputs
are zero because both donors vanish earlier;
independence fixes \(P_Z(c)=P_G(c)=Q_Z(c)=Q_G(c)=0\).
Consequently
\[
 P_Z=JM-\frac{JM(c)}{C_L(c)}C_L,\qquad
 P_G=JG_0-\frac{JG_0(c)}{C_L(c)}C_L,
 \quad 4P_G+P_Z=(Y-d)M .
                                                        \tag{2}
\]
For the last equality, \(4JG_0+JM=(Y-d)M\)
and \(M(c)=0\).

The two actual transports \(K\boldsymbol Z\)
and \(K\boldsymbol G_*\) are both zero at
\(1,b,d,e\). There the four true ratios and
nonzero \(u_z\) values fix the cubic from (2) by
four evaluations:
\[
       4Q_G+Q_Z=-(Y-d)(Y-c)N(Y).
\]
It follows that the literal physical relation
\[
                   4K\boldsymbol G_*+K\boldsymbol Z
                                  =(Y-d)\boldsymbol Z  \tag{3}
\]
holds on all eleven rows. Since
\(\boldsymbol G_*=(Y-d)\boldsymbol L\) and
\(\boldsymbol Z=4K\boldsymbol L\), this is the
commutator \(K(Y\boldsymbol L)+K^2\boldsymbol L
=Y K\boldsymbol L\) on the actual precursor.
For example at the row \(f\), where \(KZ_f=0\),
it forces
\((e-f)K_{f,e}L_e=(f-d)K_{f,d}L_d\).
This is a relation on true taps, not just on
pooled response.

## A scalar Möbius gate on the two first tail sites

Factor \(P_Z=Y(Y-c)P_3\), \(Q_Z=(Y-c)Q_2\);
the subscripts bound the degrees. On the four
anchors \(z=1,b,d,e\), \(KZ_z=0\) with the known
ratio \(w_z/u_z\). Therefore
\[
       N(Y)P_3(Y)+Y(Y-c)Q_2(Y)
             =\chi (Y-1)(Y-b)(Y-d)(Y-e).                 \tag{4}
\]
Here \(\chi\ne0\), because evaluating at \(0\)
gives the nonzero \(N(0)P_3(0)\):
\(N(0)=-4b\kappa\), \(JM(c)=c^5/30\ne0\),
and \(P'_Z(0)=-JM(c)/C_L(c)\ne0\).

Evaluate (4) at \(c\) and \(0\). The paid head
formula has the exact scalar ratio
\(N(c)/N(0)=-(c-1)(c-b)/b\). Thus
\[
             (c-d)(c-e)=D(c/H)\, d e,\qquad
 D(v)=210v^4-336v^3+168v^2-28v+1 .                       \tag{5}
\]
Indeed the ratio obtained is
\(-P_3(c)/P_3(0)=P'_Z(c)/P'_Z(0)=C'_L(c)=D(c/H)\),
using \(M(c)=0\). The projective modulo-eleven
audit checks \(D\) is rationally rootless.
In particular \(e\) is determined by \(b,c,d,H\)
(in fact independent of \(b\) once \(c,d,H\)
are known):
\[
                 e=\frac{c(c-d)}{c+(D(c/H)-1)d} .
\]
The denominator cannot vanish in the physical
chart because \(c(c-d)\ne0\).
Neither this rational equation nor (3) excludes
the entire branch.

There is also a forced transition \(Z_f\ne0\).
If \(u_f\ne0\) and \(Z_f=0\), then the ratio at
\(f\) would extend the same four-anchor formula;
since \(KZ_f=0\) by strictness, (4) would vanish
at a forbidden fifth root. If \(u_f=0\), then
\(w_f\ne0\): a zero-score singleton at a root of
the affine cofactor was already
[excluded by the Jacobi argument](../erk10-fifteen-split-host-weighted/README.md#the-unscored-host-necessarily-has-nonzero-grade-two).
Here \(Z_f=w_f M(f)\ne0\).
When \(u_f\ne0\), \(P_3(f)\ne0\) as well:
otherwise \(KZ_f=0\) forces \(Q_2(f)=0\),
again contradicting (4). The exact ratio is
\[
       \frac{Z_f}{u_f}
        =-\frac{(f-c)\chi(f-1)(f-b)(f-d)(f-e)}{P_3(f)} .
\]
All these transitions are consequences of the
actual short-word and host probe identities.

## Reproduce

    python3 -B audit.py | diff -u exact-audit.txt -

From the overlay or repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-split-host-grade-five/sources.sha256

The replay checks the Jacobi scalar identities,
primitive head ratios, and Möbius algebra. The
full observer and physical bridge is mathematical;
the preceding terminal packet has its own native
finite scalar receipt.
