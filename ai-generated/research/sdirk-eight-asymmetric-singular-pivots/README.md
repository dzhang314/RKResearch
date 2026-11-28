# Singular endpoint and diagonal pivots in the asymmetric paid SDIRK8 three-zero graph

Let a strict ten-stage SDIRK tableau have ordinary order at least eight over a field of characteristic zero or greater than seven, with nonzero common diagonal $\gamma$. Let $c=A1$ and $g=Ac-c^{\odot2}/2$. Exactly three physical entries of $g$ are zero at three different clocks. A nonzero supported grade-two vector has centered quadratic trace $r(y)=y^2+ky+q$, $y=2c-1$. In this note $k\ne0$ and none of the zero clocks is $1/2$. The [earlier support proofs](../sdirk-eight-three-zero-silent-paid/README.md) imply that all ten weights and all three supported trace evaluations are nonzero, with seven distinct off-zero clocks on the quadratic graph.

**Result.** Both actual second-gap denominators are nonzero, and the scalar diagonal denominator $\mathcal A$ below is nonzero. The result removes only these singular subcases, not the remaining asymmetric, no-midpoint regular graph.

Use the signed degree-five moment fit of $I(r\,\cdot)$ at the three zero sites. Cramer normalization gives the cubic $P=T y^3+p_2y^2+p_1y+p_0$, with $T\ne0$ and $p_0\ne0$ (no midpoint). The [asymmetric midpoint companion](../sdirk-eight-asymmetric-midpoint-zero/README.md) gives the same pure support identities before substituting its *extra* midpoint relation; no such relation is used here. Write $x=k^2$. In the original centered-quadratic chart,
$$
T=-105xq-15x+175q^3+255q^2+105q+9,
$$
$$\begin{aligned}
p_0&=\tfrac37 k(-21x+35q^2+42q+15),\\
p_1&=-\tfrac37(-175xq-21x+245q^3+385q^2+171q+15),\\
p_2&=-3k(-5x+15q^2+10q+3).
\end{aligned}$$
The clean three-site symmetry identity gives $180\gamma\mathcal A-\mathcal B=0$, with the explicit polynomials in the scripts (equivalently $I(r^2P')=2\mathcal A/7$, $I(r\omega)=\mathcal B/315$). Reflection sends $k$ to $-k$. The scalar anchor in each orientation is the exact common-root condition of $P$ and
$$H(y)=2y^3+(3k-12\gamma)y^2+(6q-12\gamma k)y+
2-3k+6q-12\gamma q.$$
Both ends have live first two rows and nonzero first two quadratic defects; either zero second defect would force the seven off-zero clocks to coincide. For an end put $R=r(2\gamma-1)$, $D=R+4\gamma^2$, $U=2R-2\gamma(4\gamma-2+k)$. Its actual normalized second gap $u$ satisfies $Du=U$. With $D\ne0$ the star is impossible: distinct star clocks having equal nonzero residual give $k=2-8\gamma$, $U=2D$, $u=2$, duplicating the first clock. The remaining arithmetic off-zero (A) or actual zero (Z) third phases obey the literal homogeneous gates $F$, or $(Q,\mathrm{pin})$, used in the previous paid midpoint projection, with the original cubic $P$ here. All these order constraints apply to the fully reflected live tableau without assuming any reflection symmetry of the method.

## Singular second gap

Reflect the degenerate end to the front. Then $D=U=0$ gives $k=2-8\gamma$ and $q=8\gamma^2-8\gamma+1$. Both ends cannot be singular: if the reflected $D^*=0$, its $R^*$ equals $R$, and $U-U^*=-4\gamma k$ contradicts $U=U^*=0$. Thus the opposite end has one actual regular phase A or Z. Substitute the forced $k,q$ into the division-free diagonal equation, both literal anchor resultants, and the two possible opposite-end gates. The univariate coefficient factors removed are only integer primitive factors of known nonzero guards: $k,\gamma,T,p_0$, both graph normalizers, and the opposite gap denominator and numerator. Integer contents are retained; all cleared inverse primes are paid.

The diagonal and two anchor polynomials (degrees 11, 27, 27) give paid characteristic support $13^3 131^3$ by the gcd of their exact resultants. Intersecting this support with the opposite actual A gate's resultant gives gcd 1; intersecting with the Z cubic and its clock pin also gives gcd 1. Hence no algebraic extension in any paid characteristic can restore this branch.

## Singular diagonal

If $\mathcal A=0$ we also need $\mathcal B=0$. These are quadratic polynomials in $x=k^2$. Their $x$ resultant is $-1344 J_1 J_2 J_3$, where
$$J_1=35q^2-3,\qquad J_2=35q^2+30q+3,$$
$$J_3=1225q^8+9450q^7+24640q^6+25230q^5+9639q^4-480q^3-1212q^2-360q-36.$$
The exact linear elimination minor yields $5 D_0 x=N_0$, with
$$D_0=175q^4+588q^3+279q^2+72q+6,\qquad
N_0=J_2(35q^4+140q^3+131q^2+40q+6).$$
If $D_0\ne0$, the identity $5D_0 T=20 q^2(q+3)J_1J_2$ after this substitution eliminates both $J_1$ and $J_2$. If $D_0=0$, then $N_0=0$; their resultant has only the paid-characteristic exceptions 59 and 6359. The full exceptional univariate gcds force $(p,q)=(59,9)$ or $(6359,2219)$. Reinsert into $\mathcal A,\mathcal B$ and discard the $T=0$ roots: the remaining $x$ values are respectively 50 and 3726. These need not split in the prime field.

For the remaining $D_0\ne0,J_3=0$ fiber, work in the free degree-eight rational quotient by $J_3(q)$ and the free quadratic extension $k^2=N_0/(5 D_0)$. The script obtains and checks an exact inverse of $D_0$ modulo $J_3$. Its coefficients, and the other computed coefficients needed for the norm specialization, have denominators supported in $2,3,5,7,59,6359$. Thus 59 and 6359 are direct coordinate exceptions, including their other $J_3$ roots even if $D_0$ is nonzero at that particular root. There is no assumption that either quotient remains a field after reduction. Norms of actual polynomial values are taken by the quadratic conjugation and the fixed resultant against $J_3$, whose leading coefficient $1225$ is a unit.

For a formal diagonal variable $\gamma$, the two chronological anchor resultants $h_{\rm f}=\operatorname{Res}_y(P,H)$ and its mirror $h_{\rm r}$ are cubic in $\gamma$. The nested norm of their $\gamma$ resultant must vanish. The forward end additionally needs its A equation $F=0$ or the Z equations $Q=\mathrm{pin}=0$. Take the gcd of the first nested norm numerator with those of the respective $\gamma$ resultants of $h_{\rm f}$ against these gate polynomials. Away from the guarded inversion primes these gcds are **11** for A and **1** for Z. Fixed-size Sylvester determinants are computed by addition and multiplication only, so the necessary vanishing under reduction is valid despite any degree drop.

Consequently the only residual tests are in characteristics 11, 59 and 6359. The direct exact code factors the complete reduced $J_3(q)$ and, for each irreducible factor, picks a root in its degree extension. All its other roots are conjugate, so one representative covers them. Then it adjoins both square roots for $k$ when needed and a common splitting extension of the two degree-three zero-site polynomials (least common multiple of their factor degrees over that base). It also handles the two separately determined $D_0=0$ fibers. Any possible $\gamma$ is already determined there by the ratio $Jr/r$ at its physical earliest zero, not by an extra unsearched field element. Each oriented distinct pair of zero roots is tested against the rear $J^*r/r$ anchor. There are **no compatible ordered anchor pairs** after the required nonzero and distinctness guards. Thus even a nonsplit ambient field yields no singular diagonal solution.

## Exact replay and native scope

Run `python check_gap.py`, `python check_diagonal_minor.py`, `python check_diagonal_norms.py` and `python check_census.py` with SymPy 1.14 and Python-flint 0.8. `RKCert.Research.SDIRKEightAsymmetricSingularPivots` checks the actual singular gap algebra and a small native projection receipt. The rank-to-scalar and modular computations are the source proof and exact replays above, not a single native `HasOrder` lower theorem. Lean/Mathlib 4.36.0 audit attached.
