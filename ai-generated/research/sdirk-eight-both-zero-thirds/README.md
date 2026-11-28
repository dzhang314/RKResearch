# Both zero thirds are impossible in the asymmetric three-zero SDIRK8 graph

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field or a field of characteristic greater than seven. Its diagonal is a nonzero common $\gamma$, with $c=A1$ and $g=Ac-c^{\odot2}/2$. There are exactly three physical $g_i=0$ entries at three distinct clocks. Assume a nonzero supported degree-two column gives a centered monic quadratic trace $r(y)=y^2+ky+q$, $y=2c-1$, with $k\ne0$ and no zero clock $y=0$. The [preceding paid proofs](../sdirk-eight-asymmetric-singular-pivots/README.md) imply that all weights are live, the seven off-zero rows have distinct clocks and obey the residual graph, and the actual two second-gap denominators are nonzero. Both reflected and literal forward first and second physical rows are off-zero. This packet rules out the **Z/Z chronology**, in which each orientation's actual third physical row is zero. It does not exclude A/A or A/Z in this remaining graph.

## 1. Exact two-end solving without a diagonal normalization

Let $u,v$ be the normalized second gaps in the forward and reflected orientations, respectively. An actual zero third row is arithmetic, with gap $2u$ (or $2v$), and the [literal first-three-row identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) give
$$Q(u)=Q(v)=0,\qquad Q(X)=4X^3-12X^2+3X+2.$$
Put $s=2\gamma-1$, so $s+1\ne0$. In the appropriate orientation the first residual is a fixed nonzero multiple of $r$ at its first clock. Applying the actual second-gap equation to that graph gives the two *linear* reads
$$ A_u k+B_u q=C_u,\qquad -A_v k+B_v q=C_v,$$
where
$$A_t=s(1-t)-1,\qquad B_t=2-t,\qquad C_t=t(2s^2+2s+1)+2s.$$
The two outer zero clocks are literally
$$a=(s+1)(1+2u)-1,\qquad b=1-(s+1)(1+2v),$$
in original centered coordinates. They are distinct and nonzero in this stratum. Both belong to the true signed-moment zero polynomial $P=T y^3+p_2y^2+p_1y+p_0$ (with $T,p_0\ne0$), defined by the signed Cramer formula in the [singular-pivot packet](../sdirk-eight-asymmetric-singular-pivots/README.md). The grade-seven three-site symmetry still gives $90(s+1)\mathcal A-\mathcal B=0$; we do not divide by $\mathcal A$ in this proof.

## 2. Equal gaps

If $u=v$, then the difference of the two reads forces $A_u=0$ because $k\ne0$. Consequently $s=1/(1-u)$ and $q=C_u/(2-u)$. Both divisions are safe ($Q(1)=-3$, $Q(2)=-8$). The two physical zero clocks are $a,-a$ with $a\ne0$. Substitution in the cubic gives
$$p_1+T a^2=0,\qquad p_0/k+(p_2/k)a^2=0.$$
Both are linear in $x=k^2$. Their resultant in $x$ has primitive gap-field norm numerator supported, outside paid primes, on $79^2 83^2$. The script checks the equal-gap inversions and all rational coefficient coordinates. In characteristics 79 and 83, all three actual $Q$ roots in the splitting field are tested. The two linear pin equations and the division-free diagonal gate have no common root after discarding only zero guard factors. The candidate variable is $k^2$, so a missing square root in the prime field is not used as a reason to reject. This is a geometric no-solution test.

## 3. Unequal gaps: singular linear determinant and regular arithmetic

When $u\ne v$, set $\Sigma=u+v$, $\Pi=uv$. The two-read determinant and Cramer numerators are
$$\begin{aligned}
D&=(4-3\Sigma+2\Pi)s-(4-\Sigma),\\
K_n&=2(u-v)(s+1)(2s+1),\\
Q_n&=[s(\Sigma-2\Pi)-\Sigma](2s^2+2s+1)+2s[s(2-\Sigma)-2].
\end{aligned}$$
This $D$ is the determinant of the *two-end linear read*, not one of the separate actual gap denominators.

If $D=0$, a genuine read requires $K_n=0$; $u\ne v$ and $\gamma\ne0$ then force $s=-1/2$. The remaining determinant condition is $12-5\Sigma+2\Pi=0$. Its norm over the oriented unequal gap-pair algebra has paid-prime-stripped numerator $107^2$. In characteristic 107 the full splitting-field census leaves two directed gap pairs. In each, recover $q=(C_u-A_uk)/(2-u)$ at this fixed $s$ (no gap zero at 2) and use the two actual outer pins and diagonal identity as univariate polynomials in the *otherwise free* $k$. Both guarded gcds are 1. No division by the vanishing determinant is made.

If $D\ne0$, substitute $k=K_n/D$ and $q=Q_n/D$ into the two actual outer pins and the diagonal identity. Clear the cubic coefficients by $D^3$ and the two diagonal coefficients by $D^5$ before taking resultants in $s$. All guard factors divided out are exact common factors with the literal product of $s+1,D,K_n,T_{\rm cleared},p_{0,\rm cleared}$, the two graph and actual gap normalizers, and $a,b,a-b$. The computation checks the coefficient denominators of each exact quotient as well as the factors themselves, so no extra specialization primes are suppressed.

The oriented gap algebra is specified by $Q(u)=0$ and the quadratic polynomial $(Q(v)-Q(u))/(v-u)=0$; the latter is literal polynomial division before specialization. Its primitive coordinate is $\theta=u+2v$. The script proves the coordinate expressions in the original two-variable quotient and guards their denominators and the reduction quotients. Only paid primes occur. In particular all six directed pairs over an algebraic closure are represented, not just prime-field gaps. The three ordinary pairwise resultants in $s$ of the cleared polynomials, followed by the $\theta$ norm and gcd of their integer numerators, give after removing only paid primes
$$13^6\,59^2\,107^{18}\,1129^2\,6011194025914915991^2.$$
All listed factors, including the last, have exact recursive Lucas primality receipts.

In each of the five remaining characteristics the code constructs a finite splitting field of the full cubic $Q$, evaluates all six ordered distinct pairs, and computes the univariate gcd in $s$ of the two pins, diagonal, and clean primitive reads at those literal third zeros. Only roots of known nonzero guards are discarded. Every such gcd is 1, including the characteristic 107 regular determinant branch. This excludes roots in any field extension of that splitting field, so concludes the complete Z/Z exclusion without assuming an ordering or prime-field coefficients.

## Reproduction and native scope

Run `python check_norms.py`, `python prime_certificates.py`, and `python check_fibers.py` with SymPy 1.14 and Python-flint 0.8. The primality verifier alone needs only the standard library. `RKCert.Research.SDIRKEightBothZeroThirds` proves the Cramer determinant and first numerator identities over general rings, the paid singular implication, and the symmetric literal pin identities over fields. The full causal-to-scalar reduction and exact arithmetic projections are the source proof and replay above, not one native `HasOrder` theorem. Lean/Mathlib 4.36.0 axiom audit attached.
