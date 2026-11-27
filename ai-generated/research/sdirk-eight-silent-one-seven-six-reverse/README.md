# Reverse projection for the detected independent six-clock Gauss double

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, assume only stage one has nonzero quadratic residual and its weight is zero. There are seven nonzero physical weights and six distinct active clocks, and the active restrictions of \(\boldsymbol h=(A-\gamma I)\boldsymbol g\) and \(C\boldsymbol h\) are independent. This is the [Gauss double chart](../sdirk-eight-silent-one-seven-six-anchored/README.md): the sole doubled active clock \(r\) is a root of \(L_4\), the two actual defects there differ, and each singleton has an actual defect given by a nonzero common multiple of
\[
 p_0(Y)=\frac{L_4(Y)}{Y-r}.
\]
Every pure-four read on the active positions is an affine clock multiplier of the actual cubic defect. At the double we retain the individual physical defects and do not substitute \(p_0(r)\) for either one.

**Result.** The remaining one-front \(k=0\) case, with singleton terminal \(x\) different from the literal silent front clock, is impossible. So is the entire **neither-front-active \(k\ne0\)** case. With the earlier [anchored](../sdirk-eight-silent-one-seven-six-anchored/README.md) and [one-front](../sdirk-eight-silent-one-seven-six-one-front/README.md) cuts, this leaves only some placements with exactly one literal front active and \(k\ne0\) in the independent six-clock chart. The dependent case, seven or more distinct active clocks, and other quadratic-residual families are not addressed. The unrestricted interval remains **10–11**.

## Zero reverse factor with the sole silent balance at the singleton terminal

Put \(N=A-\gamma I,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M,\ x=c_{10}=1-\gamma,\ c=c_9=x-\gamma u\), and \(k=1+2u-u^2\). Here \(M=CA-AC-A^2\). Physical stages nine and ten are active and \(u\ne0\). The actual reverse row is \(\boldsymbol w(C-xI)=-k\boldsymbol wN\); its last entries are \(w_9=-\gamma^2 b_9 k,\ w_{10}=-\gamma^2 b_{10}\ne0\). The row \(\boldsymbol h^{\mathsf T}B\) is in the span of \(\boldsymbol w,\boldsymbol wN\), so write it as \(\alpha\boldsymbol w+\beta\boldsymbol wN\).

At \(k=0\), \(\boldsymbol w\) is physically supported at \(x\). If \(x\ne r\) and \(x\) is not the literal silent front, only one other eligible stage \(s\) can carry its nonzero balance there. Its \(w_s=-w_{10}\). The paid \(\boldsymbol w\)-pairings make its **actual** \(h_s\) and each pure-four value equal the terminal's. Thus both physical rows four and five are on the active profile, regardless of whether one of them is this sole silent stage. The other literal front is silent and is not put on the profile.

* **Physical eighth active.** Then \(s\le7\), so \((\boldsymbol wN)_9=w_{10}A_{10,9}\), \((\boldsymbol wN)_8=w_{10}A_{10,8}\), while \(w_9=w_8=0\). Let \(A',B'\) and \(m'\) be the normalized two reflected clock ratios and third-stage middle tap from the actual three-coordinate trailing block with nonzero weights. Then \(u=A'-1\), \(d=c_8=1-\gamma B'\), \(b_{10}A_{10,9}=b_9\gamma u\), and \(b_{10}A_{10,8}=b_8\gamma(B'-1-m')\). Taking the two actual entries of \(\boldsymbol h^{\mathsf T}B\) gives
  \[
  u h_8=(B'-1-m')h_9.
  \]
  When \(c,d\ne r\), the common scale cancels, giving an exact degree-three diagonal equation \(u p_0(d)-(B'-1-m')p_0(c)=0\).
* **Physical eighth silent.** Then \(w_8\ne0\) by the already established actual two-successor equation; \(s=8\), \(c_8=x\) and \(w_8=-w_{10}\). The actual weighted taps satisfy \(b_9A_{9,8}+b_{10}A_{10,8}=0\) and \(w_8=2\gamma u b_{10}A_{10,8}\). Hence \(2u A_{10,8}=\gamma\). The equation at the silent eighth is \(0=-\alpha w_{10}+\beta w_{10}A_{10,8}\); the terminal and penultimate have \(b_{10}h_{10}=\alpha w_{10}\), \(b_9 h_9=\beta w_{10}A_{10,9}\). They give
  \[
  h_9=2u^2 h_{10}.
  \]
  For \(c\ne r\) this is again an exact degree-three equation in \(\gamma\). No reflected normalization at the silent eighth is used.

The active literal front clock is \(\gamma A_0\) with \(A_0\) from its front phase (equivalently use \(B_0\) if the other front is active). Equality of one of the known active clocks with \(r\) gives a direct diagonal formula, without a singleton substitution there. At most one of these known active clocks is \(r\): the two reflected clocks are distinct, and equality with the active literal front would put \(r\) in \(\mathbb Q(\sqrt2)\) by the two linear clock formulas. The exact Gauss quartic is irreducible over that field. All no-hit diagonal factors are guarded as before by nonzero diagonal, singleton terminal, the literal silent front not at \(x\), and singleton nonzero front defect.

For a non-Gauss active literal front, its actual nonzero \(h\) fixes the common scale of \(p_0\). On the six ordinary *clock pegs* include \(r\), even when its two active weights have zero ordinary aggregate. If physical eight is active, the active front together with \(x,c,d,r\), deduplicated only at the designated \(r\), gives four or five distinct pegs. If physical eight is silent and \(c\ne r\), the active front, \(x,c,r\) give four unless the active front is itself at \(r\); that last possibility (and the active-eighth case with the front at \(r\)) already fails the necessary tail polynomial in its prescribed diagonal field. Four pegs reconstruct the remaining two singleton nodes by the signed two-node Hankel solve. Five give a signed rank-one minor; any branch not already excluded also reconstructs its single missing singleton. See the common literal front test below. Row four or five may be the silent \(x\)-copy when eight is active; its profile matches the actual terminal as proved above. We keep those finite clock choices.

In the sparse case \(b_8=0,\ c=r\) the three known pegs are the active front, \(x\), and \(r\). Here \(\gamma=(1-r)/(1+u)\) is prescribed. If physical row four is the other \(r\), both of its actual pure-four reads fix affine profiles together with the active front, and their exact common row-five polynomial has no root outside the padded or occupied clocks. Otherwise row four is an unpegged singleton; \(H_4-P\), with the exact occupied roots removed, is a degree-two or smaller polynomial for that row. Adding it as the fourth peg reconstructs both remaining singleton clocks. Physical row five must be one of those or the second \(r\). The checks retain its actual defect if it is at \(r\). [Replay](one_front_zero.py).

## Nonzero reverse factor, both literal front weights zero

Both silent quadratic-zero rows are the literal fronts, at different clocks, and all physical rows four through ten are active. There must be a separate root \(z\) of the affine reverse multiplier: it has nonzero aggregate \(w\), off all active clocks. Here precisely one literal front is at \(z\). Its actual \(h_z\) and pure-four profile equal the transported values, so its nonzero literal \(h_z\) fixes the scale of \(p_0\). The second literal silent front may remain off-profile.

The actual last three clocks \(x,c,d\) are distinct. With normalized penultimate gap \(u\), star has \(d=x-\gamma(2-u)\) and reflected quadratic ratio \(k_d=k\). Arithmetic has \(d=x-2\gamma u\), and its literal cleared third ratio is
\[
 H k_d=-k T,\quad H=-2+u+4u^2-u^3,\quad T=4u^3-12u^2+3u+2.
\]
The replay checks \(\gcd(H,T)=1\); as \(k\ne0\), the actual equation implies \(H\ne0\). In star take \(H=1\), \(Hk_d=k\). The affine reverse row, whose root is \(z\) and whose terminal normalization is nonzero, gives
\[
 (x-z)h_9=k(c-z)h_{10},\qquad
 H(x-z)h_8=(H k_d)(d-z)h_{10}.
\]
These are scalar comparisons of the physical rows, not stage-defect formulas assumed for an aggregate.

### A tail clock at the double

If \(c=r\) or \(d=r\), use its linear clock equation to express \(\gamma\) in \(u\) over \(\mathbb Q(\sqrt2,r)\), and keep only the other singleton equation. If \(x=r\), use \(\gamma=1-r\) and cross-multiply the two equations to eliminate the *actual* \(h_{10}\), leaving a relation between the two actual singleton profiles. No tail copy at \(r\) is assigned the singleton amplitude. After clearing the indicated denominators and deleting only known impossible factors, the exact monic gap degrees are \(5,5,2\) in star and \(5,8,5\) in arithmetic (for \(d,c,x\) respectively). The three tail pegs already include \(r\).

If row four is \(r\), the actual anchored pure-four slopes give two row-five polynomials at an unpegged singleton. Their padded \(z\)-factors are removed exactly and the remaining polynomials have unit resultant. If row four is itself singleton, use its exact \(H_4-P\) condition, remove the padded \(z\) root, and append it as the fourth peg. For each row-five singleton choice and the possible second \(r\), the two pure-four comparisons close the branch. [Replay](no_front_nonzero.py).

### All three tails singleton, star

Here put \(y=x-\gamma,\ v=u-1\), so the two nonterminal clocks are \(y\pm\gamma v\) and \(k=2-v^2\). Subtract and add the fixed-profile equations. The odd part gives
\[
 (x-z)(p'_0(y)+p_3\gamma^2v^2)=(2-v^2)p_0(x),
\]
where \(p_3=[Y^3]p_0\). Eliminating the common right side from the even part gives
\[
 a(\gamma)v^2+b(\gamma)=0,\quad
 a=\gamma^2([Y^2]p_0+p_3(2y+z)),\quad
 b=p_0(y)-(y-z)p'_0(y).
\]
Here \(v,\gamma\) are nonzero by chronology. The exact \(\gcd(a,b)=1\), so \(a\ne0\). Substitute \(v^2=-b/a\) into the odd part to obtain the degree-three diagonal projection after exact forbidden factors. Its finite quadratic for \(v\) retains both orientations.

### All three tails singleton, arithmetic

Substitute the singleton cubic into the ninth equation. Eliminate \(p_0(x)\) from the eighth using that equation and \(H k_d=-kT\). The resulting exact polynomials, after dividing the common factors \(u\) (which cannot vanish), are
\[
 F=\frac{(x-z)p_0(c)-k(c-z)p_0(x)}u,\qquad
 J=\frac{H(c-z)p_0(d)+T(d-z)p_0(c)}u.
\]
Treat them as polynomials in \(u\) over \(\mathbb Q(\sqrt2,r)[\gamma]\). Their degrees are two and five. With \(F=c_2u^2+c_1u+c_0\), pseudo-divide \(J\) by \(F\), retaining a linear remainder \(\ell+m u\). The only common factors of \(\ell,m\) lie in \(c_2\); exact quotient cancellation is made only on \(c_2\ne0\). Thus \(m\ne0\) on the main chart, and \(u=-\ell/m\) gives
\[
 c_2\ell^2-c_1\ell m+c_0m^2=0.
\]
Guarded exact polynomial division removes only zeros forbidden by diagonal, chronology, separation of the inactive root, or singleton amplitudes (including both checks against \(r\)). The retained monic degree is 17. On the separate \(c_2=0\) branch the exact guarded leading polynomial has degree three; its linear pivot \(c_1\) and remaining \(J\) residual are units in the whole finite quotient. This retains the leading-degree-loss branch, rather than relying on a generic resultant. The main lifts keep all coefficients and both exact tail equations checked. [Replay](arithmetic_nonzero.py).

Both singleton-tail phases have four known distinct pegs \(x,c,d,r\). The signed two-node reconstruction yields the two missing singleton clocks. Either row four is \(r\) or it is at a missing singleton root. For row five retain both residual singleton choices as applicable and the other actual \(r\) if chronology permits it. The common literal tests below are units in the corresponding finite quotients.

## Common signed and literal tests

Use the monic nodal mask \(D\) of already known sites. With four known sites, the moments \(m_j=\int_0^1 X^jD(X)\,dX\) for \(0\le j\le3\) are precisely the two unpegged singleton weights times their respective nodal factors and powers. Both masks and weights are nonzero, and the signed determinant \(m_0m_2-m_1^2\) is nonzero by the two-by-two Vandermonde factorization, not by positivity. It gives the recurrence of their monic quadratic. With five pegs only one singleton remains and the signed rank-one equation and recovery apply. A pegged \(r\) need not have nonzero aggregate.

Work in normalized time \(Y=c_i/\gamma\), and normalize \(h_i\) by \(\gamma^3\). Write \(H_4\) for the exact cubic from the literal row-four three-tap solve. The earlier anchor and row four fix the affine slopes for the two physical reads \(\tau_4\) and \(Ah\), because the anchor and the row-four \(h\) are both nonzero in these tested fibers. The actual row-five first three strict scalar moments at its normalized clock \(y\), after stage one's fixed strict feed \(2H\), are
\[
 y-1-2H,\quad y^2/2-y-2H,\quad y^3/3-y^2-4H/3.
\]
They fix its three actual taps at the distinct literal predecessors \(A_0,B_0,c_4/\gamma\). Reading \(\tau_4\) and \(Ah\) from these taps gives two affine equations in its actual \(H\). On a singleton use \(P(y)\), the normalized common scale of \(p_0(\gamma y)\). On a new \(r\)-copy keep \(H\) unknown and test their affine inconsistency determinant. If an earlier \(r\)-row is already one of these actual predecessors, the padded earlier row is a solution at its own \(h\). A nonzero difference slope of at least one equation forces this same actual \(h\), thus the exact padded taps and a literal duplicate. This is forbidden by the saturated stage bound; it is not an assertion that two equal clocks are duplicates without coefficient tests.

## Replay and Lean scope

Run `python3 -m pip install -r requirements.txt` and `python3 check_reverse_projection.py` from this directory in the repository. The script uses the listed prior sibling sources, needs no network after dependency installation, and checks 88 zero-factor orientations, 28 nonzero repeated or star orientations, and four nonzero singleton arithmetic orientations. Exact rational quadratic/Gauss field polynomials establish the finite projections; all final unit tests and exceptional pivots are verified at \(p=1009,\ t=285,\ 2t^2=1\), using finite monic polynomial bases. Some exact coprimality checks use another good reduction with explicit preserved leading coefficients. This establishes characteristic-zero exclusion by multiplication determinants and exact guards, not by assuming reduction exists for the proposed tableau.

The [native Lean file](../../lean/RKCert/ReviewedNative/SDIRK8GaussDoubleReverseProjection.lean) verifies the weighted active eighth identity, unnormalized silent eighth identity, star symmetric cubic elimination, and the denominator-free arithmetic quadratic projection. These receipts compiled on Lean/Mathlib 4.36.0 with standard axioms. The full saturation reductions and finite arithmetic above are source-level.
