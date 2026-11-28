# Arithmetic front, star rear, nonzero centered tail, interior silent placement

Consider the [constant nonzero nine-site reverse numerator](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md) for strict ten-stage SDIRK8 over a characteristic-zero field. Physical one is the sole nonzero quadratic-defect row and ordinarily silent; there are eight distinct ordinary clocks and an actual ninth distinct reverse clock for the other ordinarily silent row. Here that row is physical **5, 6, or 7**, the regular genuine mixed quintic has arithmetic front and ordinary star rear, and \(B\ne0\) in the centered star tail \(A+Bv^2=0\). This packet excludes those placements. The [identically zero tail](../sdirk-eight-silent-one-eight-reverse-live-arithmetic-star567-zero-tail/README.md) is separate. Literal silent 2/3/4, other phases, and the unrestricted **10–11** interval are not covered.

## Four fixed pegs and two small homogeneous remainders

Write \(a=\gamma A_0,b=\gamma B_0,q=\gamma s,x=1-\gamma\) for the actual ordinary pegs \(2,3,4,10\). These are all distinct. Write \(m=1-2\gamma\), \(c=m-\gamma v,d=m+\gamma v,w=v^2,k=2-w\); \(c,d\) are actual physical 9 and 8, ordinarily active and distinct from each other and from the four pegs. The regular exact shape \(H_*=\delta H\) has the same paid Bézout identity as in the [four-peg reconstruction](../sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed/README.md#fixed-known-peg-pivot-not-a-residue-assumption). Use the four ordinary nonconstant coefficient rows of \(H_*W_{E_4 X^j}-E_4X^j W_{H_*}\), where \(E_4\) is the four-peg monic product. This uses ordinary scalar precision **seven**, not eight or nine. These rows also work with the shifted basis \((X-m)^j\).

The first four columns are independent at any true solution. A lower-degree kernel would give an ordinary polynomial \(D'=E_4R'\) of degree at most seven with constant Bézout read \(\lambda'\). The true \(D_8\) has nonzero constant read \(\lambda\). The difference \(\lambda D'-\lambda' D_8\) is divisible by \(H_*\) because \(W_{H_*}\) is coprime to \(H_*\), and by \(E_4\). Those two divisors are coprime since \(H_*\) is nonzero at actual ordinary pegs. Their product has degree nine whereas the difference has degree at most eight. It is zero, forcing \(D'=0\) by degree. Thus the signed cofactors \(r_0,\ldots,r_4\) give a nonzero scaling of the true missing quartic in \(T=X-m\), with \(r_4\ne0\). The exact replay removes only the common \(\gamma^2 V_0^2\), where \(V_0\) is the regular nonzero fourth-anchor coefficient after its strict \(\gamma\) factors.

This quartic has both \(T=\pm\gamma v\) as roots. Reducing it modulo \(T^2-\gamma^2 w\) gives the two coefficients
\[
 r_1+\gamma^2 w r_3,\qquad r_0+\gamma^2 w r_2+\gamma^4 w^2 r_4,
\]
both zero. The exact homogeneous equations are
\[
 B r_1-\gamma^2 A r_3=0,\qquad
 B^2r_0-\gamma^2 AB r_2+\gamma^4A^2r_4=0.
\]
In addition to already fixed scales, divide only \(\gamma^2H_*(x)\) in the first and \(\gamma^4\) in the second. The actual terminal amplitude \(H_*(x)\ne0\) follows from the deflated ordinary identity. The two exact \((s,\gamma)\)-degrees are **(8,21), (14,42)**. The centered tail itself has only the usual \(v(v^2-1)\) padding removed, with each zero forbidden by distinct \(c,d,x\). These equations do not choose a rear sign or use a fifth-stage clock.

## Actual fifth, separately for its two physical roles

The paid determinant of \(\boldsymbol h,C\boldsymbol h,A\boldsymbol h,\boldsymbol\tau_4\) on literal rows 2–5 holds whether physical fifth is ordinary or silent. Its arithmetic-front literal third tap is \(m_0=\tfrac12+3t\), with \(A_0=2+2t,B_0=3+4t\) and \(2t^2=1\). In particular its third cubic amplitude is \((B_0-1-m_0)/2\); its \(A\boldsymbol h\) read includes the actual term \(m_0 H_a\), and its \(\boldsymbol\tau_4\) read includes \(m_0 A_0^3\). The replay uses these true arithmetic terms. The cleared fifth determinant vanishes identically at \(Y=A_0,B_0,s\), because the prospective fifth at each padded clock reproduces the actual corresponding earlier row. All three factors are forbidden at an actual fifth: it is either an ordinary distinct clock or the actual distinct ninth reverse site. Clear the predecessor denominators and divide these characteristic-zero factors to obtain the exact cubic \(F_5(Y)\) at \(Y=c_5/\gamma\).

* If **physical fifth is ordinary**, the actual missing polynomial has the true rear pair as a factor. Its other two roots are ordinary missing nodes. After clearing \(B\), the actual missing fifth satisfies the quadratic
  \[
  B r_4 T^2+B r_3 T+B r_2-\gamma^2 A r_4=0,\qquad T=\gamma Y-m .
  \]
  The padded degree-\((2,3)\) resultant of this quadratic and \(F_5(Y)\) vanishes, even when a leading coefficient reduces to zero.

* If **physical fifth is silent**, its actual clock is \(z\), not a root of an ordinary missing polynomial. The two actual affine reverse reads give \((x-z)(H_*(c)+H_*(d))/2=k(m-z)H_*(x)\). Write \(h_i=[U^i]H_*(m+\gamma U)\), and set
  \[
  E=B^2h_0-ABh_2+A^2h_4,\quad K=B(2B+A)H_*(x),\quad
  N=mK-xE,\quad D=\gamma(K-E).
  \]
  At a true solution \(K\ne0\), and \(K=E\) would force \((x-m)K=0\), impossible. Hence the exact paid scalar gate is the homogenization \(D^3F_5(N/D)=0\). No inverse of \(B\) or \(D\) is used in the finite arithmetic. In particular, no nonzero condition is placed on \(H(z)\).

## Exact orientation and retained guards

The full exact \(s\)-resultant of the two projected remainders has degree **630** in \(\gamma\) over \(\mathbb Q(t)\). For replay use \(z_0=2t,z_0^2=2\). After integer clearing, the Sylvester coefficient norm in the basis \(1,z_0\) is bounded by the corresponding product of row norms, using \(\lvert a\rvert+2\lvert b\rvert\) per coefficient. The bound is 2392 bits. Both split orientations preserve full Sylvester degrees at each of 40 CRT primes. Their product exceeds twice the bound, so centered coefficients give the exact integer pair. An independent split prime checks the entire pair. Remove only the exact strict factor \(\gamma^{92}\) and content; the rational norm has degree **1076** and six factors.

For the small norm factors the oriented piece is obtained by paired CRT proposals verified by exact division of both the norm factor and the actual oriented resultant. Its monic complement and oriented resultant are coprime at the whole \(p=1129,t=203\) place, excluding every characteristic-zero root in that complement. In each actual oriented field an exact proposed guard divisor \(D_0\) of the first fourth equation is accepted only after checking **both** \(D_0\mid P_0\) and \(D_0\mid G^{\deg D_0}\), where the actual guard \(G\) is nonzero. These guards are \(r_4\) (from fixed-peg uniqueness), \([X^5]H_*\) (genuine quintic), and \(B\ne0\) (the chart). No factor is discarded solely by an accidentally vanishing residue.

| Rational norm factor degree, exponent | Exact orientation degree | Exact fourth support removed | Degree removed | Full local components |
|---|---:|---|---:|---:|
| 24, 1 | 12 | Nodal leading | 1 | 8 |
| 522, 1 | Whole rational norm checked | None | 0 | 8 |
| 6, 3 | 3 | Quintic leading | 1 | 1 |
| 16, 6 | 8 | Nonzero \(B\) | 3 | 2 |
| 42, 8 | 21 | Nodal leading | 2 | 3 |
| 8, 10 | 4 | Nodal leading | 2 | 1 |

In each of the 15 retained small-factor components the exact monic fourth input has no common root of both projected equations. In the large-factor case keep all eight reduced diagonal components; seven contradict the actual oriented resultant, and in the remaining full fourth common-root model **both actual fifth gates** generate a unit. Monic gamma/fourth models ensure a genuine characteristic-zero candidate would survive at a residue place; integrality of the unknown tableau is not assumed. The selected embedding residue \(t=203\) is a place of the same \(\mathbb Q(t)\) for either actual orientation.

## Replay

Install `sympy==1.14.0` and `python-flint==0.9.0`, then run `python3 check_arithmetic_star567_regular_closed.py` from this directory with its declared siblings. The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveArithmeticStarQuartic.lean) checks the arithmetic literal gap unit, centered quartic division, opposite-root remainders, homogeneous projection and actual missing-node identity. The exact coefficient and finite proof remain source-level; the five native lemmas were checked on Lean/Mathlib 4.36.0.
