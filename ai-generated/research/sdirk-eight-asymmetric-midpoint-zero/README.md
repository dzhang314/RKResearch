# No asymmetric quadratic graph with a midpoint zero at the paid SDIRK8 floor

Consider a ten-stage strict SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven, with common diagonal $\gamma\ne0$, $c=A1$, and $g=Ac-c^{\odot2}/2$. Assume exactly three physical residual zeros at three distinct clocks, one of which is $c=1/2$. Assume a nonzero grade-two vector supported on those three coordinates has centered monic quadratic trace $r(y)=y^2+ky+q$, with $y=2c-1$ and **$k\ne0$**. This packet rules out this stratum over every paid field. It does not assume tableau reflection, nor rule out arbitrary asymmetric traces with no midpoint zero.

The [previous paid support proofs](../sdirk-eight-three-zero-silent-paid/README.md) show that all ten weights and all three values of $r$ on the zero group are nonzero. Every off-zero residual is proportional to $r(y)$, and its seven clocks are distinct. Thus both actual time orientations are available; reflection sends $k$ to $-k$ and does not change $q$ or $\gamma$.

## 1. Exact Cramer relation and the true diagonal

Let $I$ be the normalized centered integral on $[-1,1]$, and $m_j=I(r y^j)$. The zero group with signed weights $b_i r(y_i)$ matches these moments through degree five. Its $3\times3$ Hankel is nonsingular by the three distinct nodes and nonzero signed weights. Multiply the Cramer nodal polynomial by the harmless factor $23625/4$ so that $P=T y^3+p_2 y^2+p_1 y+p_0$ with
$$T=-105k^2q-15k^2+175q^3+255q^2+105q+9.$$
The exact column-replacement determinants are checked directly from the three moment equations in the replay. In particular
$$p_0=\frac{3}{7}k(-21k^2+35q^2+42q+15).$$
The actual midpoint zero is $y=0$, so $p_0=0$ and, since $k\ne0$,
$$k^2=K(q):=(35q^2+42q+15)/21.$$
Substitution gives $T=4(35q^2-3)/7\ne0$ and
$$p_1=-\frac37(-175Kq-21K+245q^3+385q^2+171q+15),\qquad
p_2=-3k(-5K+15q^2+10q+3).$$
In particular $p_1\ne0$ by distinctness of the other two roots and $q\ne0$ by the supported trace at the midpoint.

The [three-site diagonal symmetry proof](../sdirk-eight-even-quadratic-trace/README.md#1-three-site-hankel-and-a-diagonal-identity) also works without evenness of $r$. For clarity, restrict $BA+A^{\mathsf T}B-bb^{\mathsf T}$ to the zero group, then scale its $ij$ entry by $r(y_i)r(y_j)$. Its row sums vanish by the clean $Jr,J^*r$ reads and its $y$ quadratic form vanishes by the paid grade-seven self-pair. Weighting its diagonal by $P'(y_i)$ therefore gives
$$
2\gamma I(r^2 P')=I(r\omega),\qquad
\omega(y)=I_z\!\left(r(z)\frac{P(z)-P(y)}{z-y}\right).
$$
Indeed $\omega(y_i)=b_i r(y_i)P'(y_i)$ by the signed moment functional at a root. In centered coordinates $J$ integrates from $-1$ with normalization $1/2$. The exact replay checks that $I(r^2P')=2\mathcal A/7$ and $I(r\omega)=\mathcal B/315$, with the specialized factorizations
$$\mathcal A=-4(q+1)(7q^2-3)(35q^2-3)/21,$$
$$\mathcal B=-4(35q^2-3)(105q^3+175q^2-33q-51)/21.$$
Cancel the guard $35q^2-3\ne0$. Then necessarily
$$L\gamma=N,\qquad L=180(q+1)(7q^2-3),\quad
N=105q^3+175q^2-33q-51.$$
No division by $L$ is used for its singular branch.

## 2. Endpoint geometry and the regular one-variable projection

In either physical orientation the first two residuals are nonzero: a zero second residual would localize all off-zero clocks to the first, contradicting the graph census. In the forward orientation write
$$R=(2\gamma-1)^2+k(2\gamma-1)+q,\quad D=R+4\gamma^2,\quad
U=2R-2\gamma(4\gamma-2+k).$$
The normalized nonzero second gap $u$ satisfies $Du=U$; use $-k$ for the reverse end. For $D\ne0$ a star third is impossible: the same nonzero residual at the two distinct star clocks gives $k=2-8\gamma$, hence $U=2D$ and $u=2$, a repeated first clock. Thus the physical phases are **A** for an off-zero arithmetic third and **Z** for an actual zero arithmetic third. At an A end the actual arithmetic tap identity and quadratic graph give the homogeneous gate
$$F=-2D^3+UD^2+4U^2D-U^3-2R(3U-2D)D=0.$$
At a Z end use the cubic
$$Q=4U^3-12U^2D+3UD^2+2D^3=0$$
and the actual third-site pin $P(2\gamma(1+2u)-1)=0$, homogenized using the actual gap.

In each orientation, the clean earliest zero read gives the centered anchor
$$H(y)=2y^3+(3k-12\gamma)y^2+(6q-12\gamma k)y+
2-3k+6q-12\gamma q=0.$$
The latest physical zero is distinct from the earliest, so at least one orientation has a **noncentral** anchor. Write $H_{\rm cent}=H(0)$ (including any common homogenizing power of $L$). For the other two sites use $P_*(y)=T y^2+p_2 y+p_1$. Reduce $T^2H(y)$ modulo $P_*$ as $a y+b$. A noncentral anchor forces
$$H_{\rm nc}=T b^2-p_2 a b+p_1a^2=0,$$
without dividing by $a$. Every end therefore pays $H_{\rm cent}H_{\rm nc}$, and at least one pays $H_{\rm nc}$.

For $L\ne0$ and with both gap denominators nonzero, substitute $\gamma=N/L$ *homogeneously*. Then perform literal products and reductions in the free algebra $\mathbb Z[1/(2\cdot3\cdot5\cdot7)][q,k]/(k^2-K(q))$. Each polynomial is $e(q)+k o(q)$; reflection flips the odd component. Whenever both reflected values vanish, $e=o=0$ since $k\ne0$. A single vanishing value implies its norm $e^2-Ko^2=0$. When two given signed values vanish together, their two-component minor also vanishes.

The source records the exact univariate systems:
* AA uses both components of $F$, both components of $H_{\rm cent}H_{\rm nc}$, and the norm of $H_{\rm nc}$.
* AZ reflects if necessary so that A is forward; use norms of $F,Q,\mathrm{pin}$, the minors of forward $F$ with reverse $Q,\mathrm{pin}$, and the same anchor guards.
* ZZ uses the two components of $Q,\mathrm{pin}$, and the same anchor guards.

Every integer polynomial is obtained by clearing denominators supported only in $2,3,5,7$. Retain its integer content; divide only primitive common factors with the nonzero guard product of $q,K,T,p_1,L,N$ and both normalized graph, gap denominator and gap numerator factors. The three gcds of the chosen exact Sylvester resultants, after stripping only paid primes, are respectively $13^6,13^{12},13^{12}$. A common root in any algebraic extension makes the same resultant vanish; this does not require $k$ or $q$ in a prime field. The exact reduced polynomial gcd over $\mathbf F_{13}$ of each entire univariate system is $(q+1)^2$, which has only the root $q=-1$ even over algebraic extensions. This conflicts with $L\ne0$, so no regular branch survives.

## 3. The independent singular tests

If either gap denominator $D$ vanishes, then its numerator $U$ vanishes. Reflect that end to the front if necessary. The actual second-gap equations give $k=2-8\gamma$, $q=8\gamma^2-8\gamma+1$. Substitute these expressions into $21k^2-35q^2-42q-15$, $L\gamma-N$, and the necessary front anchor product $H_{\rm cent}H_{\rm nc}$. The latter uses the same quadratic remainder and retains the center alternative. The two resultant numerators against the first polynomial have stripped gcd 1. This closes the singular-gap branch before any gap division or choice of phase.

If $L=0$, then also $N=0$. At $q=-1$ the numerator is 52, leaving only characteristic 13. On $7q^2=3$ it is $12(q+2)$, so a common root would give $25=0$, impossible in paid characteristic. Thus the singular diagonal forces characteristic 13 with $q=-1$, $k^2=1$. The noncentral zero clocks satisfy $y^2-ky-1=0$ in centered coordinates; the discriminant 5 is nonsquare in $\mathbf F_{13}$ so they lie in its quadratic extension.

One can already reject both possible chronological anchors over that extension. For a noncentral root $y$, $r(y)=2ky$ and $1/y=y-k$. The forward and reverse diagonal read ratios at such a root are respectively
$$
\frac{1+2(k-2)(y-k)}{24k},\qquad
\frac{-1-2(k+2)(y-k)}{24k}.
$$
At the center they are $1/3+k/4$ and $1/3-k/4$, in the prime field. If both chronologically outer roots are noncentral, they are $y,z$ with $z=k-y$. Equality of the two ratios would force $2y=k$, and $y^2-ky-1=0$ would give $5=0$. If exactly one is central, the other ratio has nonzero prime-field slope, so equality to the center read would force its noncentral root into the prime field, contradicting nonsplitting. Both outer roots cannot be central. The finite replay independently checks all six ordered distinct pairs for each $k=\pm1$ in the full splitting field; neither $r$ nor the denominator factors vanish there.

## Replay and native scope

Run `python check_projection.py` and `python check_f13.py` with SymPy 1.14 and Python-flint 0.8. The projection includes explicit Cramer and diagonal substitution checks and all singular denominator cases. `RKCert.Research.SDIRKEightAsymmetricMidpoint` proves the noncentral opposite-root arithmetic contradiction, the prime-field nonsquare check, and the exact singular characteristic gcd. The rank and chronology bridges and resultant computations are the exact source proof and reproducible arithmetic above, not one native `HasOrder` nonexistence theorem. Native audit checked on Lean/Mathlib 4.36.0.
