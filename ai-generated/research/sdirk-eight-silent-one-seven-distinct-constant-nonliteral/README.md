# The nonliteral reverse root with constant \(Q\)

This is the [detected seven-distinct active chart](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at the strict SDIRK8 ten-stage floor over a characteristic-zero field. Its only nonzero quadratic residual is at the individually weight-zero physical first row. Here \(k\ne0\), \(Q\) is constant, and the separate nonzero reverse aggregate is at a nonliteral silent clock \(z\). There is exactly one active literal front. If both literal fronts were silent, those would be the only physical candidates for the extra aggregate. The [constant literal-root packet](../sdirk-eight-silent-one-seven-distinct-literal-reverse/README.md) treats every literal placement and proves that the no-extra branch is impossible. This packet completes the constant case; it does not treat coprime nonconstant denominators.

Use \(\boldsymbol h=N\boldsymbol g,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M\) with \(N=A-\gamma I,\ M=CA-AC-A^2\). On the seven active sites \(h=\lambda L_4\), \(\lambda\ne0\), and \(w_i/b_i\) is proportional to \(L_4(c_i)/(c_i-z)\). The separate aggregate \(z\) lies outside all active clocks and is provided by a sole nonliteral physical silent, whose actual defect and pure-four reads equal the virtual profile. The other physical silent is a literal front, outside \(z\), with zero reverse weight; it is not transported. It is not necessary that \(L_4(z)\) be nonzero.

## Exact front-only projection

Let \(a\) be the known active literal normalized clock with actual \(h_a\ne0\). Use \(Q=L_4(\gamma a)\), \(P(Y)=h_a L_4(\gamma Y)\) in this normalization. The active sites and the sole transported physical silent satisfy \(Qh=P\). In particular fourth and fifth obey this common profile regardless of which one is silent (only one can be silent). The actual fourth has \(H_4(s)\ne0\): at a zero of \(H_4\) its proportional pure \(Ah\) would also vanish, contrary to their exact literal gcd. The fourth equation is the literal padded cubic \(\Phi=(QH_4-P)/(Y-a)\).

Use the [denominator-cleared pair of literal fifth reads](../sdirk-eight-silent-one-seven-distinct-gauss-nonliteral/README.md). The two removed padded factors are \(y-a,y-s\): a later active site cannot equal an earlier active site, and the transported silent is at a separate clock. The remainders on division by \(y-s\) are exactly the defect-free literal reads at \(s\) times \(\Phi\), checked symbolically. Thus the two remaining necessary fifth polynomials have degree at most three. Take their resultant in \(y\), keeping its coefficient content as an included diagonal factor. Reduce by the fourth cubic via a pseudo-remainder; retain the leading factor and take the resultant in \(s\). The guarded diagonal degree is 100 for every literal orientation, including multiplicities before the exact split.

The removed factors evaluate only to \(\gamma,\ L_4(\gamma a),\ L_4(x),\ x-\gamma a\), \(x=1-\gamma\). The exact \(H_4(s)=L_4(\gamma s)=0\) locus intersects the diagonal projection in degree 12. In that exact quotient remove the common \(H_4\) factor from the fourth cubic, leaving degree two. No reduced \(H_4=0\) point is guessed away. The complementary fourth retains degree three.

## Tail equations and actual-node masks

Write \(c=x-\gamma u,\ k=1+2u-u^2\). In active star eighth with \(d=x-\gamma(2-u)\), the literal ninth and eighth ratios eliminate \(z\) and give
\[
 (2-u)L_4(c)-u L_4(d)+k(2u-2)L_4(x)=0.
\]
Its exact \(u(u-1)(u-2)\) padding leaves a genuine quadratic in \(u\), because the profile is quartic. For arithmetic eighth with \(d=2c-x\), use \(H L_4(d)+2T L_4(c)-kT L_4(x)=0\), with the [literal \(H,T\) factors](../sdirk-eight-silent-one-seven-distinct-coprime/README.md), after exact zero-gap padding (degree five). With silent eighth, its individual nonzero reverse weight is at \(z\), and the actual geometry gives \(2(x-z)+\gamma k(u-2)=0\). Substituting yields \((u-2)L_4(c)-(2u+k(u-2))L_4(x)=0\); after exact \(u\) padding its degree is four. The exact leading coefficient branches are retained before reduction.

Use \(d_9=L_4(c)-kL_4(x)\), \(n_9=xL_4(c)-kcL_4(x)\), so \(d_9z=n_9\). The actual \(d_9\ne0\), because \(d_9=0\) would leave \(kL_4(x)(x-c)\ne0\). It is not inverted in the residual checks. Signed active moments through degree nine are known from the degree-seven quadrature and \(h^2,Ch^2\). With four known ordinary pegs the signed mask leaves three ordinary sites, giving a cleared missing cubic by the six Hankel/Cramer moments. With five known pegs it leaves two, giving a cleared quadratic and rank at most two in the \(3\times3\) Hankel.

* **Silent fourth, active eight**: impose its actual clock \(\gamma d_9s=n_9\), and test actual active fifth by both padded pure resultants with the missing cubic on pegs \(\gamma a,x,c,d\).
* **Silent fifth, active eight**: use the two literal fifth equations homogenized at \(y=n_9/(\gamma d_9)\) and the signed rank-two gate on actual ordinary pegs \(\gamma a,x,c,d,\gamma s\).
* **Silent sixth or seventh, active eight**: use the rank-two gate and actual ordinary fifth's two padded resultants against the same mask's missing quadratic.
* **Silent eight**: fourth and fifth are active, and the four pegs \(\gamma a,x,c,\gamma s\) give the missing cubic containing actual fifth.

All needed residuals generate the unit ideal in the retained finite algebras. Nodes and weights need not be positive.

## Replay

Run `python3 check_constant_nonliteral.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the repository sibling proof tree. The runner lists its finite six-clock, literal and Gauss dependencies. All 12 modes use \((1103,t-161)\), \(2t^2=1\), after exact padding, factor guards and degree splits. Every irreducible diagonal factor and full retained gap/fourth quotient is checked; no reduced collision is discarded. Unit determinants in the finite reduced algebra lift by the local-unit argument of the previous packets without reduction of an actual tableau.

The [native Lean lemma](../../lean/RKCert/ReviewedNative/SDIRK8ConstantQuarticTail.lean) kernel-checks the quartic star factor on Lean/Mathlib 4.36.0. The full saturation, front projection and exact arithmetic are source-level. Together with the literal-root and zero-factor cases, constant \(Q\) is now covered in this detected seven-distinct chart. The unrestricted strict SDIRK8 interval remains **10–11**.
