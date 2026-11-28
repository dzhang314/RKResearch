# Eight distinct zeros: the last onsite affine roots in the finite-gap phases

Let \(A,\mathbf b\) be strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field. Put \(\mathbf c=A\mathbf1\), \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), and assume exactly eight physical zeros at eight distinct clocks. The [low-label census](../sdirk-eight-eight-zero-low-labels/README.md) gives the two distinct individually silent off rows at physical positions 1 and 2. Consider a nonconstant reverse barycentric numerator whose affine root \(q\) is an actual zero clock at physical row **6 or 7**. Its ordinary weight is nonzero by the [silent-root exclusion](../sdirk-eight-eight-zero-silent-pure-root/README.md). This packet concerns the silent-eighth and live reflected arithmetic phases.

**Result.** Both phases are impossible in this chart. Along with the early-component exclusions and the [late-star transport](../sdirk-eight-eight-zero-affine-late-star/README.md), an exactly-eight-zero candidate must therefore have eight distinct zero clocks and an affine numerator with a root **outside those eight labels**. The overall 10–11 stage interval is unchanged.

## 1. A phase-specific second row keeps both gap polynomials cubic

Normalize \(A'=A/\gamma\), \(\mathbf x=\mathbf c/\gamma\), \(D=1/\gamma\), \(I_D(T^j)=D^j/(j+1)\). In the finite-gap phases let the three rear labels be
\[
   s=D-1,\quad t=s-v,\quad r=t-v,\quad \kappa=1+2v-v^2 .
\]
Here \(v\) satisfies the ghost cubic \(H(v)=v^3-4v^2-v+2=0\), or the literal arithmetic compatibility sextic \(T_6(v)=0\) from the [early finite-gap proof](../sdirk-eight-eight-zero-affine-early-finite/README.md#1-the-affine-cardinal-rows-and-the-individual-jump). Let \(Q(v)=4v^3-12v^2+3v+2\).

Use \(Y=T-t\), \(q=t+\delta\), and \(x=t+\xi\) for the other late early label. The first three actual zero clocks \(a,b,c\) are distinct from \(q\). Write \(\sigma=(T-a)(T-b)(T-c)\). The eight-site polynomial is
\[
 P_8=\sigma(Y-\xi)(Y-\delta)(Y-v)Y(Y+v).
\]
Let \(B(\rho)=I_D(P_8/(T-\rho))\). With \(z_iP'_8(x_i)\) affine and zero at \(q\), the first ordinary row is the relative cardinal equation \(\kappa(s-q)B(t)-(t-q)B(s)=0\). The other ghost row is \(B(r)=0\). In the live arithmetic case the triple
\[
     (B(s),\kappa B(t),\kappa_3 B(r))
\]
is a common multiple of \((v-\delta,-\delta,-v-\delta)\), by the three literal pure/ordinary ratios. Thus \(B(s)+\kappa_3B(r)=2\kappa B(t)\). After multiplying by \(H(v)\) and using \(H(v)\kappa_3=-\kappa Q(v)\), the **second** row is
\[
 H(v) B(s)-2H(v)\kappa B(t)-\kappa Q(v)B(r)=0.
\]
This is independent of \(\delta\) in its coefficients on the three ordinary cardinals; no division by \(H\) is used. It avoids a quartic last-label determinant.

In both phases use the two mean masks \(R_1,R_2\) on \(\sigma(Y-\xi)\):
\[
\begin{aligned}
R_1&=(Y-\delta)\bigl[\kappa(v-\delta)(Y^2-v^2)+\delta Y(Y+v)\bigr],\\
R_2^{\rm ghost}&=(Y-\delta)Y(Y-v),\\
R_2^{\rm arith}&=(Y-\delta)\bigl[H\,Y(Y+v)-2H\kappa(Y^2-v^2)-\kappa Q\,Y(Y-v)\bigr].
\end{aligned}
\]
They are exactly the preceding ordinary rows. All their moments have degree at most seven; no extra degree-eight quadrature is assumed. Set \(A_j=I_D(Y^j\sigma R_1)\), \(B_j=I_D(Y^j\sigma R_2)\) for \(j=0,1\). Then \(A_1=\xi A_0,\ B_1=\xi B_0\), so \(J_0=A_0 B_1-A_1 B_0=0\). The first row has \(\delta\)-degree at most two and the second at most one, giving the desired cubic.

## 2. Actual pure transfer and both literal fourth reads

The front constraints \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0\) and the actual third-read transfer \(f(c)=\alpha(c)f(a)+\beta(c)f(b)\) are the same supported constraints as before. The basis for \(F_4|_U\) is [the two paid modes](../sdirk-eight-eight-zero-affine-early-star/README.md#1-the-single-live-root-has-a-split-free-pure-jump) \(L_4\) and the scaled reproducing kernel \(K(T,q)\), with the extra value \(-D^6/b_q\) at the actual \(q\) in the latter. All of \(a,b,c\) are different from \(q\), so transfer gives \(C_3(c;D)=0\) on \(L_4\) and the same cubic as in the last seven-label proof:
\[
     G(\delta)=\frac{K(c,q)-\alpha(c)K(a,q)-\beta(c)K(b,q)}{(c-a)(c-b)}=0.
\]

For the supported cubic \(\sigma\) define \(E\) as the nonzero first-two \(L_4,K\) evaluation determinant. Let \(C_L,C_K\) be the Cramer numerators for fitting its pure error at \(a,b\) in those modes, with data \(-J\sigma(a),-J\sigma(b)\). The cleared residual
\[
 E(\sigma-J\sigma)-C_L L_4-C_K K=\sigma Q_1
\]
divides by \(\sigma\) exactly by the two transfers; \(Q_1\) is at most linear. If \(q\) is physical row 7, actual row 6 is \(x\), so \(Q_1(x)=0\) from its literal diagonal read. This is the same \(\xi\)-line as in the earlier star proof.

If \(q\) is row 6, its diagonal read includes the live-root jump. Write \(n_j=I_D(Y^j\sigma)\), making
\[
 M=I_D(\sigma(Y-\xi)(Y-v)Y(Y+v))
   =(n_4-v^2 n_2)-\xi(n_3-v^2 n_1).
\]
Since \(b_q=M/P'_8(q)\), after clearing the actual jump denominator and canceling the nonzero \(\sigma(q)\), the equation is
\[
 Q_1(q) M+C_K D^6(\delta-\xi)\delta(\delta^2-v^2)=0.
\]
This is again a line in the same \(\xi\). No last-label moment or weight is inverted in the final test: in each chronology, both two-by-two minors with the ordinary lines must vanish.

## 3. Exact guarded projection without a bulky inner resultant

The exact field \(K_0=\mathbb Q(u,b,v)\) is regenerated with primitive \(u+b+2v\) and degrees 18 and 36 in the two phases, with irreducibility and inverse coordinates verified. Write \(C_3=\ell_2 c^2+\ell_1c+\ell_0\). At \(\ell_2\ne0\), set \(L=\ell_2 c\), with \(L^2+\ell_1L+\ell_2\ell_0=0\). Every coefficient of the two cubics \(G,J_0\) has degree at most two in \(c\). Scale each coefficient by \(\ell_2^2\) and reduce it in that monic quadratic algebra.

Form the three-by-three Bézout matrix of those cubics, namely the coefficient matrix of
\[
   \frac{G(X)J_0(Y)-G(Y)J_0(X)}{X-Y}
\]
in two dummy variables, using the scaled coefficients in the quadratic algebra. At an actual common root its evaluation against \((1,\delta,\delta^2)\) vanishes, so its determinant reduces to a necessary \(A+B L=0\). This definition does not divide by a gap leading coefficient, and avoids expanding a large \(D,c\) resultant. Its outer norm has degree 186 in \(D\). The code verifies exact division by \(\ell_2^{12}\) and \(D^{24}\), leaving degree 114, with no scalar collision factor contributing. No \(\delta\)-dependent guard is used in this projection.

The degree-114 projection is **exactly** \(D_{\rm H}^{\,2} N^3\) up to a scalar unit, with degrees \(30,18\). The shared degree-30 polynomial is the scaled norm of \(p_{45}g_3-p_{43}g_5\) after its \(\ell_2^3\) guard, as in the [last seven-label proof](../sdirk-eight-eight-zero-star-unequal-late/README.md#3-exact-guarded-diagonal-projection). The two exact divisions and the complementary monic cube root are verified by rational-polynomial arithmetic.

On \(D_{\rm H}\), the exact branch congruence for \(c=-A/(B\ell_2)\) forces the three-by-three Hankel determinant of \(n_0,\ldots,n_4\) to vanish. The replay checks this congruence before reduction. The [two-atom argument](../sdirk-eight-eight-zero-star-unequal-late/README.md#4-the-rank-factor-is-hankel-two-atom-not-a-finite-rank-discard) applies unchanged: the two ordinary masks here each contain \(Y-\delta\) times a polynomial of degree at most two. Where \(\Delta=n_0n_2-n_1^2\ne0\), the first two moment recurrences and the Hankel determinant give a monic quadratic \(Q_2\) with all three masked moments zero. In the quadratic gap algebra pick its other root \(\epsilon\) and take \(\xi=\epsilon\). Both ordinary masks then have mean zero. The geometric moment sequence of \((Y-\epsilon)\sigma\), normalized using the unit whose norm is \(-\Delta\), also gives its kernel interpolation: \(K(T,q)\) agrees with an \(L_4\) multiple at \(a,b,c\). Hence \(Q_2\) divides both gap cubics, and a root of \(Q_2\) is incompatible with the **literal first-two pure rank**. This reasoning works even for a repeated root in the quadratic algebra. The complementary linears are verified coprime below.

## 4. Fixed complete fibres for all exceptions

Each pair in the table is a fixed prime and simple primitive residue. All factors listed are simple, and the checks use complete finite extensions of their residue fields.

| Phase \((p,z_0)\) | \(D_{\rm H}\) factor degrees | \(N\) factor degrees | \(\ell_2=0\) factor degrees |
|---|---|---|---|
| Ghost \((17,6)\) | \(1,5,24\) | \(2,6,10\) | \(4\) |
| Arithmetic \((103,65)\) | \(1,2,2,10,15\) | \(1,17\) | \(1,1,2\) |

On \(D_{\rm H},N\) the preserved-degree reduction has \(B,\ell_2\) units, and on the leading drop \(\ell_2=0\) there is a unit \(\ell_1\) giving \(c=-\ell_0/\ell_1\). At each fibre at least one of the two original gap cubics has unit leading coefficient. On \(D_{\rm H}\), \(\Delta\) is a unit and the entire gap gcd equals \(Q_2\), with coprime complementary linears. On \(N\) the two pairs of fourth-read minors kill the entire common gap algebra, not merely its rational roots. In the separate leading-drop branch the original gap cubics are coprime.

The fixed simple primitive residue lifts to an embedding of the common exact field into a local characteristic-zero field. Preserved leading coefficients make every hypothetical diagonal and gap integral in any valuation extension; the checked pivots justify all recovered coefficients. Exhaustion of the geometric residue fibres then proves characteristic-zero nonexistence. There is no finite-grid inference or assertion excluding the residue characteristics themselves.

## 5. Replay and native scope

Run `python check_affine_late_finite.py PHASE` with `PHASE=ghost,arith`, SymPy 1.14 and Python-flint 0.8. The exact degree-36 arithmetic replay may take about two minutes. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroAffineLateFinite.lean) states the affine plane row and centered jump factors over an arbitrary commutative ring. Other scalar gates are the previously staged Hankel and fourth-read modules; the actual tableau and exact geometric reduction remain source proofs.

The companion is included as source; a new stock Lean replay has not been completed.
