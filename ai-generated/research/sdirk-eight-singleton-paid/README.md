# The exactly-one-zero SDIRK8 branch is empty in every paid characteristic

Let $A,b$ be a ten-stage strict SDIRK tableau of ordinary order at least eight over a field. Its quadratic residual is $g=Ac-c^{\odot2}/2$, where $c=A1$. If the field has characteristic greater than seven, **exactly one literal zero in $g$ is impossible**. The [characteristic-zero proof](../sdirk-eight-singleton-exclusion/README.md) already excludes that branch in characteristic zero. The other zero patterns and the unrestricted ten-stage question are not decided here. In particular no alternate-domain ten-stage upper is claimed.

Only factorial-paid fields are used: $8!$ is a unit. As a consequence, a nonzero commutative ring with $8!$ a unit, unit common diagonal, and all nine other quadratic residuals units also cannot have exactly one literal zero. Reduction at any maximal ideal preserves those hypotheses and all rooted order identities. The units hypothesis on the other residuals is needed for this corollary.

## Actual rooted-order consequences

The [singleton saturation argument](../sdirk-eight-saturation/README.md) and the [affine-graph and weighted-reflection argument](../sdirk-eight-singleton-exclusion/README.md) apply in characteristic greater than seven with the same algebra. The Hilbert pairing determinants through size four, all factorials through eight, the monic shifted Legendre recurrence, and the scalar primitive determinants are nonzero with precisely these denominator primes. The proof uses no signs or inequalities. More explicitly:

* The unique zero row has Gauss clock $a$ with $L_4(a)=0$, common diagonal $\gamma=(4+35a(1-a))/72$, weight $2\gamma$, and physical position 5 or 6. Its early-prefix and late-suffix tests need only $a,1-a\ne0$ (since $70L_4$ is unit-valued at 0 and 1) and determinant factors dividing $8!$. Also $\gamma^{-1}=(864-3456\gamma)/49$.
* The supported $E_3$ profile with scalar trace $\Pi_a(x)=L_4(x)/(x-a)$ has pure part in $G E_1$, where $G=\operatorname{diag}(g)$. This is an affine graph for every off-zero pair. All weights are nonzero by the same two-sided support-rank proof: scalar probes detect the trace, and at least two active off-zero clocks detect the pure $g\langle1,c\rangle$ line and its linear multiple. The last fact follows from the degree-three scalar pairing rank, which requires at least four distinct active clocks.
* After chronologically reversing the weighted adjoint, the clocks are reflected, the residuals are divided by the single nonzero factor $\tau=g_{10}/g_1$, and order eight is unchanged. The proof uses weighted duality of the Volterra spaces and exact scalar reverse integration, not real positivity.

Normalize clocks and the matrix by $\gamma$ and residuals by $\gamma^2$. Write $x$ for a normalized clock, $z=1/\gamma$ for the integration endpoint, $a_0=a/\gamma$ for the zero clock, and $P(x)=\Pi_a(\gamma x)$. The graph is $D(x)g=P(x)$ on every off-zero row, with $D(x)=2[p+\ell(x-1)]$ and $p=P(1)$. The normalized first row is $(1,1/2)$. In the reverse chart use $p',\ell'$ and $L=z-2$. The actual graph reflection gives
$$
 p'=-\tau(p+L\ell),\qquad \ell'=\tau\ell.
$$
These equations hold even when $p=0$ or $p'=0$. The front variable $u=x_2-1$ gives $\ell=K(u)/\kappa(u)$, with $\kappa=1+2u-u^2$, and the same star and arithmetic third-row gates as in the earlier proof. The star requires $p+d_2+2d_3=0$, where $P(1+u)=p+d_1u+d_2u^2+d_3u^3$. Otherwise $u$ is a root of the exact arithmetic cubic $Q_3$. All computations of $K,Q_3$ are literal in `resultant_data.py` and `splitting_fields.py`.

## The two physical fourth rows and the missing clock

Let $T$ be the quadratic interpolating the first three residuals. With $J_T$ its zero-constant primitive, the local fourth gate is
$$
 g-T(x)+J_T(x)-g[\Lambda(x)-T_1-T_2\Delta(x)]=0,
 \quad
 \Lambda=1+(x-1)/\kappa,\quad
 \Delta=4/3+2(\kappa+1)(x-1)/(3\kappa).
$$
It follows by applying $A$ to $g-T$ and using the actual common diagonal one after its three earlier zero reads. This uses $F_3=G E_1$, which remains true in the singleton branch. If the fourth row repeats an earlier **pair** exactly, its strict first-three taps must repeat that earlier row's padded taps: the actions on $1,x,x^2$ are fixed by the same $(x,g)$, and their three-column prefix Vandermonde is invertible. Then all true rooted profiles are identical on those rows by induction with the common diagonal, contradicting full stage rank. This does not forbid unequal residuals at the same clock.

The graph and fourth gate give a degree-at-most-four clock polynomial. It has all three distinct literal earlier clocks as roots, verified before dividing. After they are divided out, at most one further root remains. At a common root of $D,P$, solve the original gate for the residual, without dividing by $D$. This retains a distinct residual at a repeated clock.

In the regular case $D,P$ are coprime. The functional $\Phi(R)=\sum_{\text{off-zero }i} b_i R(x_i)/D(x_i)^3$ is determined on all polynomials of degree at most ten by the paid scalar and pure residual moments. For affine $D$ this follows by successive division: at its root subtract multiples of $P^3,P^2,P$ on the three iterations and divide by $D$ at each step. The three removed pieces have zero paid pure moments. The resulting degree-at-most-seven polynomial $J$ satisfies
$$
 \Phi(R)=I(J)-2\gamma J(a_0),\qquad I(x^j)=z^j/(j+1).
$$
The small-field replay also computes $\Phi$ from the full linear system, allowing constant $D$. Once both fourth rows are obtained, eight of the nine off-zero clocks are known; write $T_8$ for their product polynomial, with multiplicity allowed. Only one off-zero clock remains because the unique zero occupies row 5 or 6. Its addition would make the monic nine-node polynomial and its multiple by $x$ annihilate $\Phi$. Thus the necessary pencil is
$$
 \Phi(T_8)\Phi(x^2T_8)-\Phi(x T_8)^2=0.
$$

In the two exceptional common-root profiles that survive the ends, the two fourth pairs are at the **same** vertical clock $r$ and have distinct residuals. Write $H=P/D$ after canceling the common linear root. On all other off-zero clocks $g=H(x)$. The moments of powers $1,2,3$ of the defect $g-H(x)$ are paid; subtract the contribution of the unique zero row to get $M_1,M_2,M_3$. If there were only the two known vertical rows with deviations $v_1,v_2$, their moments would satisfy $M_3-(v_1+v_2)M_2+v_1v_2M_1=0$. The exact check contradicts this, forcing the third off-zero row at $r$ as well. All ordinary mass then lies on eight known distinct clock sites; Vandermonde quadrature fixes the mass at $a_0$, and it is not its required $2\gamma$.

## Why this covers every paid prime

In $\mathbb Q(a)$, compute the three exact norms of $p$, the star scalar $p+d_2+2d_3$, and the slope resultant. Their reflected counterparts have equal norms for the first two scalars. If neither constant nor star guard fails, the two physical slopes require a common root of
$$
 F_a(h)=\operatorname{Res}_{U}(Q_3(U),K(U)-p\kappa(U)h),\qquad
 V_a(h)=(1+Lh)^3 F_{1-a}(-h/(1+Lh)),
 \quad h=\ell/p.
$$
These fixed Sylvester polynomials specialize with only paid denominators, even when specialized degrees drop. Their top-level resultant is $R(a)=\operatorname{Res}_h(F_a,V_a)$. Any underlying prime not dividing a numerator of these norms is impossible. This is just monic resultant specialization: a genuine shared root would make the specialized determinant zero. It does not require the unknown tableau to have an integral lift.

The two guard norms give the primes $29,101,613,1453,118709,523357,5428349$. The numerator of the slope resultant norm is $(601\cdot6277\cdot N)^2$, where $N$ is a specific 229-digit integer coprime to those nine named primes and to $8!$. It is not necessary to factor $N$.

For each named prime, use exact arithmetic in $\mathbb F_{p^{24}}$: all four Gauss roots and all possible entrance-gap solutions lie there. Indeed Gauss factor degrees are 1, 2 or 4; when both ends are arithmetic the two cubics split in extension degree dividing six over the field of the Gauss root. When a star occurs, an arithmetic side is enumerated first, and the reverse slope determines the star gap by a quadratic, with all degenerate zero-pivot cases expressly checked. Finite field arithmetic checks every branch and does not assume the tableau's field is itself finite. Both fourth polynomials have at most one as-yet-unaccounted root after their three known roots; hence they add no extension. The determinant and mass tests are then nonzero in every field extension. The exact branch counts are:

| Prime | Matched ends | Nodal pencil contradictions | Vertical mass contradictions |
|---:|---:|---:|---:|
| 29 | 0 | 0 | 0 |
| 101 | 0 | 0 | 0 |
| 601 | 2 | 0 | 2 |
| 613 | 12 | 12 | 0 |
| 1453 | 0 | 0 | 0 |
| 6277 | 2 | 0 | 2 |
| 118709 | 12 | 12 | 0 |
| 523357 | 0 | 0 | 0 |
| 5428349 | 12 | 12 | 0 |

## No factorization of the remaining modulus

Reflection gives $R(a)=r_0+r_1a(1-a)$, checked exactly in $\mathbb Q[a]/(L_4)$. The denominator of $r_1$ is paid, its numerator is coprime to $N$, and $Y=-r_0/r_1\bmod N$ satisfies $70Y^2-20Y+1=0\bmod N$. At any prime dividing $N$, a surviving Gauss root therefore factors through the common quadratic algebra
$$
 \mathcal A=(\mathbb Z/N)[a]/(a^2-a+Y).
$$
All operations in the following check are exact operations in $\mathcal A$. A coefficient is inverted only after its quadratic norm is proved coprime to $N$, so every step specializes at every such field point.

Ordinary Euclidean remainders for the two slope polynomials in $\mathcal A[h]$ end at a monic degree-one polynomial. Its root fixes $h$ in every specialization. The two pairs $(Q_3,K-p\kappa h)$, with the true reflected slope on the second, each give the same degree-one recovery for their gap. The gate checks again recover each actual fourth clock linearly. The coprime affine graphs determine $\Phi$ by the three divisions above. The resulting pencil value is $C_0+C_1a$, with
$$
 (C_0+C_1a)(C_0+C_1(1-a))=C_0^2+C_0C_1+YC_1^2
$$
a unit modulo $N$. Thus the pencil cannot vanish in any specialization. No assumption that $N$ is prime, squarefree, or fully factored enters the argument.

## Verification scope

Run `PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint python check_small.py` and `PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint python check_composite.py` with SymPy 1.14 and Python-flint 0.8. The latter reconstructs the rational norms, computes all modular ring divisions with unit checks, and matches its exact cofactor and pencil receipts to the Lean source.

`RKCert.Research.SDIRKEightSingletonPaid` proves over arbitrary commutative rings the scalar complement and norm identities, the nodal pencil implication, and the two-atom cubic relation. It kernel-checks the sample prime residues and the cofactor norm/inverse, and proves nonvanishing of the reconstructed cofactor pencil under the scalar ring hypotheses. The complete enumeration, Euclidean elimination, and rooted-order flag bridge are the exact computation and argument above, not a native end-to-end `HasOrder` theorem. The native module was checked on Lean 4.36.0 with pinned Mathlib.
