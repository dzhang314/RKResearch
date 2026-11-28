# DIRK11/13 live cubic: compact profile and global five-prefix reduction

**Scope.** This takes the normalized invisible-six, no-late-ghost, live
cubic chart from the sibling notebooks. In particular: actual rooted order
11, six distinct zero-weight and individually cubic-dirty ghosts, seven
distinct clean clocks including the endpoint stages, true forward C(2)
and reverse D(1), D(2), the stated surplus ranks, no ghost before the
fourth ordinary reverse stage, cubic \(U\), and \(\tau\ne0\).
Every characteristic-zero conclusion below holds over a field of
characteristic zero under these hypotheses. The real stage interval is
still **13–14**.

The compact profile applies to all remaining \(\gamma=3,4,5\).
The **global projection** applies to \(\gamma=5\), with five initial
forward ghosts and one ghost between reverse ordinary stages four and
five. The fifth ordinary reverse clock \(B\) must belong to the exact
degree-220 support in **gamma5-guard-support.txt**, with eight primitive
irreducible factors of degrees \(4,4,16,24,24,28,60,60\).
These are not realizations. A base factor can arise from a zero guard
at a *different* profile; it cannot be globally discarded.

## Reduced affine pivot

Reuse the [fourth clean notation](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md):
\(R(Y)=Y^3+c_2Y^2+c_1Y+c_0\), \(V\ne0\) the fourth ordinary reverse
site, \(c_0\ne0\), \(F_3(s)=0\), \(A_1(s)r+A_0(s)=0\),
\(A_1(s)\ne0\), and \(F_3'(s)\ne0\). Here
\(A_1r+A_0=120c_0\mathcal A\). Set
\[
 N=s[(c_2+4V)s+2Vc_1-c_0],\qquad D=V(c_0+c_2s).
\]
The exact smaller affine witness is
\[
 A_1N+A_0D=(-5c_0^2+5c_0c_2s-16s^3)F_3(s).
\]
At a contact \(c_0+c_2s=0\) we have \(c_2\ne0\), and
\[
 \begin{split}
 c_2^3 F_3(s)&=-2c_0 H^2,\\
 c_2^2 F_3'(s)&=H(12Vc_0-2Vc_1c_2+3c_0c_2),\\
 H&=2Vc_0-Vc_1c_2+c_0c_2.
 \end{split}
\]
Thus \(F_3(s)=0\) forces \(H=0\) on that contact, contrary to the live
derivative. We may use \(r=N/D\). These three identities and the domain
implication have Lean proofs.

## Reconstruction and the two actual five-prefix equations

The arithmetic uses a finite-free monic quotient tower over
\(\mathbb Q[B]\). Scale the reverse clock by the live
\(L=132J_4(B)\): the scaled fourth site \(v=LV\) satisfies a monic
quartic. If \(a_i\) are the coefficients of \(F_3\) in these clock units,
\(\sigma=a_3L^2s\) satisfies a monic cubic with lower coefficients
\(a_i a_3^{2-i}\). The actual \(a_3\) is live. The programmed marked
profile coefficients in scaled units are
\[
 m=(\sigma D_*,N_*,a_3 D_*),\quad
 D_*=v(c_0a_3+c_2\sigma),\qquad
 N_*=\sigma((c_2+4v)\sigma+(2vc_1-c_0)a_3).
\]
This multiplies the recovered marked polynomial by a common live scalar.

Below all polynomials use the scaled clock variable \(y\), and we omit
scale bars. Write \(P=ym,\ P_0=yR\), and let \(e\) be the first column
of the adjugate of old \(m\)-multiplication. Thus \(em=\nu\bmod R\)
and \(\nu\ne0\) by the three old live \(m\) values. Let
\[
 a=(e\,IP/y)\bmod R,\quad b=(e\,IP_0/y)\bmod R,\quad
 a_y=(e\,I(yP)/y)\bmod R,\quad d=\nu m_2/4-a_1.
\]
The old affine identity gives
\(IP=(a/\nu)P+(d/\nu)P_0\). At \(v\) the actual marked row has value
\(k_v=IP(v)\nu/a(v)\); \(IP(v),a(v)\) are live. The degree-four
interpolants \(P+tP_0,yP+vtP_0\), where \(t=d/a(v)\), match the true
two reverse marks through \(v\). Consequently the two normalized
readouts are \(A/D_A,F/D_A\), where
\[
 A=a(v)a+d b,\qquad F=a(v)a_y+v d b,\qquad D_A=\nu a(v).
\]
Scaling the clock also scales the primitive/readout by the corresponding
powers of \(L\), equivalently scaling the matrix by \(L\). The literal
first reverse ghost \(z\) has only its diagonal in the ghost subblock,
so \(C(z)=0\) for \(C(y)=F(y)-yA(y)\).

With \(h=yJ_4\) in the scaled units and \(u=(eJ_4)\bmod R\), the
nonzero-scale carrier numerator is
\[
 U_{\rm num}= u\,IP(v)R(v)+R[h(v)a(v)-IP(v)u(v)].
\]
It is cubic in this chart. If \(f'=(L-y)U_{\rm num}\) and \(f(0)=0\),
then \(J(y)=f(L)-f(y)\) is the actual forward primitive \(I(XU)\),
up to the same nonzero coordinate/scale factors. The
[proved prefix gate](../dirk11-thirteen-invisible-six-cubic-live-prefix-third/README.md)
has two live hull multipliers and gives the inverse identity
\[
 S_6/J \equiv \eta(z-y) \pmod{U_{\rm num}},\qquad \eta\ne0.
\]
The split clean hull \(S_6=(L-y)T_5(y)\) is a unit in the cubic
carrier quotient and \(J\) is a unit there as well. The inverse
identity uses the same literal first reverse gap ghost as \(C\).

For \(P_1,P_2,P_3\) of degree at most \(d\), write
\[
 [P_1,P_2,P_3]_d
 =\det(P_1,P_2,P_3,U_{\rm num},yU_{\rm num},\ldots,y^{d-3}U_{\rm num})
\]
in the ascending coefficient basis. Modulo the cubic, this is the
three-coordinate remainder determinant times \(U_3^{d-2}\).
Take \(W_2=[J,yJ,S_6]_6\),
\(W_0=[S_6,yJ,y^2J]_7\) and \(W_1=[J,S_6,y^2J]_7\).
Cramer's rule gives the two true necessary conditions
\[
 W_2=0,\qquad C^{\rm hom}(-W_0,W_1)=0 .
\]
The latter is the affine root relation \(W_0+zW_1=0\) followed by
\(C(z)=0\), with no division in the code. The direct determinants
avoid superfluous powers of \(U_3\).

Multiplication by an element that vanishes under evaluation at a
putative actual \(v,\sigma\) has zero specialized determinant:
evaluation is a nonzero linear functional annihilating that map.
No separability or distinctness of the *other* formal branches is
required in this projection implication.

## Characteristic-zero arithmetic ledger

1. The first determinant norm, after recorded common coefficient
   contents, has exact degree **5704** and squarefree degree **496**.
   Divide out exact gcds with the guard projections to obtain a
   degree-276 cofactor and the degree-220 guard support. Each removed
   polynomial content has radical dividing the same guard support.
   Thus no \(B\) fiber was lost by normalization.
2. The exact primitive cofactor has leading coefficient a unit at
   103. Rebuild the upstream coefficients exactly over \(\mathbb Q\),
   convert them and all monic quotient coefficients to
   \(\mathbb F_{103}[B]/(\bar F)\), and check their rational denominators.
   The downstream norm circuit uses only polynomial arithmetic, with
   no division by further coefficient contents. Its remainder and
   the monic \(\bar F\) satisfy the explicit Bézout identity. A separate
   Lean module checks all 551 coefficients with kernel reduction.
3. A monic factor of the cofactor over \(\mathbb Q\) lies in
   \(\mathbb Z_{(103)}[B]\): the monic cofactor lies in that integrally
   closed ring. A factor also dividing the raw second norm would
   retain its positive degree modulo 103, contradicting the Bézout
   check. No tap, tableau, individual clock, or actual residue \(B\)
   is assumed 103-integral.

## Compact divided gates for other prefix lengths

Write \(a+bY+cY^2=F(Y)-zA(Y)\). For its two distinct actual literal
gap roots \(z,w\), \(c(z+w)=-b,\ c zw=a\) without division.
For the clean quintic fit \(Q\), multiplying the divided \(U,Q\)
agreement by \(c^2\) yields the polynomial
\[
 c^2[0,1]-bc[0,2]+(b^2-ac)[0,3]+ac[1,2]-ab[1,3]+a^2[2,3],
 \qquad [i,j]=U_iQ_j-U_jQ_i .
\]
It is at most quadratic in the first ghost \(z\). For \(\gamma=4\),
the analogous prefix determinant contraction is \(cD_2+bD_1+aD_0\),
at most linear in \(z\). Both formulas preserve coincident residues
after applying actual distinctness before specialization. The
accompanying Lean scalar identities verify these reductions;
neither is by itself an exclusion of all \(\beta\ge2\) profiles.

## Reproduce

Use Python 3 with python-flint 0.9.0 and a temporary directory with
at least 35 MB free for this five-prefix receipt. Other optional
runner modes are not needed. From this notebook directory:

    d=$(mktemp -d)
    mkdir "$d/first" "$d/guards" "$d/proof"
    python3 project.py --p 0 --chart five --first-only --write "$d/first"
    python3 project.py --p 0 --trace-guards --write "$d/guards"
    python3 filter-exact.py "$d/first/five-curvature.txt" --guards "$d/guards" \
        --ledger "$d/first/ledger.txt" --output "$d/cofactor.txt"
    python3 check-support.py "$d/cofactor.txt" "$d/cofactor.guards" "$d/first/ledger.txt"
    python3 project.py --p 0 --chart five --verify-over "$d/cofactor.txt" \
        --verify-prime 103 --write "$d/proof"
    cmp gamma5-bezout-103.txt "$d/proof/five-first-gap-bezout.txt"

Lean checks the actual scalar identities and finite residue witness
as separate endpoints. The linked tableau/rank ingress and large
rational determinant/guard elimination remain written and replayed
by the exact source, not attributed to a Lean order theorem.
