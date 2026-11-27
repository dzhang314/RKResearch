# The eleven-stage rational DIRK10 method must have at least two dirty clocks

**Result.** A lower triangular eleven-stage tableau with rational coefficients and actual rooted order ten cannot have all of its nonzero cubic defects at one numerical clock. Let \(c=A1\), \(g=Ac^2-c^3/3\). At least two distinct values of \(c_i\) must occur on \(\{i:g_i\ne0\}\). No exclusion of the remaining multiple-dirty-clock case is claimed. The real eleven-stage endpoint is unchanged.

This concludes the [rational single-clock reduction](dirk-order10-rational-clock-gates.md) and the [positive fourth-power coset](dirk-order10-rational-local-and-coset-cuts.md) by a global genus-two obstruction. The exact point and rank computation below is not a search up to a height, nor a failed local split test.

## 1. Only two residue disks matter

The previous work proves for a rational single-clock tableau, up to inversion of the ratio,
\[
 s=a+b,\quad t=s/u,\quad R=a/b=3x^4,\quad T=5t-3=27z^4,
 \qquad (s,t)\equiv(8,8)\pmod {11}.
\]
Here \(a,b,u\) are the first three distinct nonzero exterior clocks and \(t=4-R-R^{-1}\). Inverting the ratio in the arithmetic reduction does not change \(t\). The excluded possibilities include all other one-clock bands, including a shared terminal pole.

Set \(W=3z\), \(U=3x^2-x^{-2}\), \(V=3x^2+x^{-2}\). The relations
\[
 W^4=3T,\qquad 5U^2=21-W^4,\qquad 5V^2=81-W^4
\]
are direct expansions from \(T=17-5(R+R^{-1})\). Thus
\[
 X=W^2,\qquad Y=5 W U V
\]
give a rational point on the smooth projective genus-two curve with model
\[
 C:\quad Y^2=F(X)=X(X^2-21)(X^2-81).
\]
Use \(\infty\) as its rational point at infinity. The finite-field reduction at 11 is good: \(\operatorname{disc}F=16\cdot81^3\cdot21^3\cdot60^4\) has prime support \(2,3,5,7\). Since \(t\) is 11-adically integral of residue 8, \(T\equiv4\) and \(W^4\equiv1\pmod {11}\). Consequently \(W\) is integral and \(X=W^2\equiv1\pmod{11}\). The only possible \(Y\) residues are \(7\) and \(4\), those of the two actual rational points \(P=(1,40)\), \(P^-=(1,-40)\).

We prove that each of these two residue disks contains only its indicated rational point. It will follow that \(X=1\), whence \(T=1/3\) and \(t=2/3\). The exact [two front cases on that fiber](dirk-order10-rational-clock-gates.md) already rule out \(t=2/3\), including the case of an additional physical clock one.

For completeness, there is no empty dirty support in a rational order-ten DIRK tableau: the ordinary moment forces at least one nonzero clock; at its first occurrence the exact row \(Ac=c^2/2\) gives diagonal \(c_i/2\) and hence \(g_i=c_i^3/6\ne0\). Thus excluding the single numerical dirty clock does imply the stated at-least-two necessary condition.

## 2. Exact two-descent on the genus-two Jacobian

Let \(J=\operatorname{Jac}(C)\). Use the standard odd-degree \(X-\theta\) map for hyperelliptic Jacobians. The required facts are [Stoll, *Implementing 2-descent for Jacobians of hyperelliptic curves*, §4](https://www.impan.pl/shop/publication/transaction/download/product/83397), in particular Proposition 4.2, Lemmas 4.3/4.4/4.8 and Corollary 4.7. The map injects \(J(\mathbb Q)/2J(\mathbb Q)\) into the norm-square part of
\[
 L^\times/L^{\times 2},\qquad
 L=\mathbb Q[X]/F \simeq\mathbb Q^3\times K,\quad K=\mathbb Q(\sqrt{21}).
\]
We order the three rational slots by roots \(0,9,-9\), and write \(\omega=(1+\sqrt{21})/2\) for the last slot. Outside the four primes \(2,3,5,7\), the valuations of every component of an image are even by good reduction; at infinity and those four primes the classes must belong to their actual local images. For the divisor \((x,y)-\infty\) we use the class of \((x,x-9,x+9,x-\sqrt{21})\). At an exact Weierstrass point, replace the single zero rational slot with \(F'(x)\); this follows also by continuity of the square class in the branch parameter \(y\).

Here is the entire global square-class group used for the upper bound. \(K\) has discriminant 21 and class number one: Minkowski gives norm bound \(\sqrt{21}/2<3\), and 2 is inert, so every class has a norm-one representative. The smallest positive unit larger than one is \(2+\omega=(5+\sqrt{21})/2\): norm minus one is impossible modulo 3, and with norm one the least possible positive square-root coefficient is attained by this unit. Positive units are its powers by the least-unit argument, and the other sign is independent modulo squares. The following list therefore spans all classes with even valuations outside the required places:

| Slots | Square-class generators |
|---|---|
| Each of the three rational slots | \(-1,2,3,5,7\) |
| \(K\)-slot | \(-1,2+\omega,2,1+\omega,3+\omega,\omega,1-\omega\) |

Indeed 2 is inert; \(1+\omega,3+\omega\) generate the ramified primes of norms 3 and 7 (element norms \(-3,7\)); \(\omega,1-\omega\), of norm \(-5\), generate the two distinct primes over 5. In total this is a 22-dimensional square-class space.

For each of the five places the complete local image is witnessed by the following points, specified by their \(x\)-coordinates. These are **local** points, not claimed as rational points on \(C\). At \(x=20\), \(F(20)\) has 2-adic valuation 2 and unit 1 modulo 8. At \(x=24\), \(F(24)\) has 5-adic valuation 2 and unit 1 modulo 5. At \(x=1\) the ordinate 40 is rational. Other listed coordinates are rational branch points.

| Place | Witness \(x\)-coordinates | Dimension of witnessed image |
|---|---|---:|
| \(\infty\) | \(-9,0\) | 2 |
| \(2\) | \(0,9,-9,1,20\) | 5 |
| \(3\) | \(0,9,-9\) | 3 |
| \(5\) | \(9,-9,1,24\) | 4 |
| \(7\) | \(0,-9,1\) | 3 |

These dimensions equal the full image dimensions, so this is a completeness check rather than a list of sampled points. In odd degree the 2-torsion dimension is the number of irreducible factors minus one. This follows by using the representative even subset of branch points not containing \(\infty\), then taking Galois-invariant subsets. There are four factors over \(\mathbb Q,\mathbb Q_2,\mathbb Q_3,\mathbb Q_7\), five over \(\mathbb Q_5,\mathbb R\). By the local \(J/2J\) dimension formula we add the genus 2 at the dyadic place; at the real place we subtract 2; at the odd finite places the dimension is that of the 2-torsion.

The [exact arithmetic replay](check-dirk10-genus-two-closure.py) encodes the square classes in finite binary vectors and checks each span and preimage. At a rational local slot it uses valuation parity and the residue square class (unit modulo 8 at 2, sign at infinity). The \(K\)-slot at 2 is unramified of degree two, and its units are classified by their cosets modulo squares in the unit group of \((\mathbb Z/8)[\omega]\); units congruent to 1 modulo 8 are squares by Hensel. At 3 and 7 use the uniformizer \(2\omega-1=\sqrt{21}\), valuation computed by the norm, and residue \(1/2\) for \(\omega\). At 5 use the two simple \(\omega\) lifts from residues 0 and 1, taken to one digit beyond the valuation of the normalized norm, so no zero place is mistaken for a unit. At the real place use exact signs at each embedding.

Intersecting the norm-square constraint and the local preimages gives the following dimensions:

| Conditions included | Norm | \(\infty\) added | \(2\) added | \(3\) added | \(5\) added | \(7\) added |
|---|---:|---:|---:|---:|---:|---:|
| Remaining binary dimension | 17 | 15 | 10 | 7 | 4 | 4 |

Thus \(\dim J(\mathbb Q)/2J(\mathbb Q)\le4\). Its rational 2-torsion has dimension 3, so \(\operatorname{rank}J(\mathbb Q)\le1\). No assumption on the Tate–Shafarevich group, conjectural rank, or a found Mordell–Weil basis is used.

## 3. Exact direction of the rational Jacobian in the 11-adic logarithm

Let \(D=[P-\infty]\), with the **global** point \(P=(1,40)\). Put \(B=[P+(9,0)-2\infty]\). The same replay uses [Cantor’s exact addition algorithm](https://doi.org/10.1090/S0025-5718-1987-0866101-0) for reduced Mumford divisors in \(\mathbb Q\) and \(\mathbb F_{11}\), with no floating-point root computations. For this model, a reduced pair \((u,v)\) has \(u\) monic of degree at most two and \(u\mid F-v^2\). To combine two pairs, compute \(d=\gcd(u_1,u_2,v_1+v_2)=e_1u_1+e_2u_2+e_3(v_1+v_2)\), compose with \(u=u_1u_2/d^2\) and
\[
 v=\big(e_1u_1v_2+e_2u_2v_1+e_3(v_1v_2+F)\big)/d \pmod u,
\]
and, if needed, reduce by \(u\mapsto\operatorname{monic}((F-v^2)/u)\), \(v\mapsto-v\bmod u\). Every stated exact quotient and resulting divisor identity is checked. Binary and sequential computations of \(28D\) agree over \(\mathbb Q\).

The reduced order of \(D\) in \(J(\mathbb F_{11})\) is 28. Independently, the rational pair for \(28D+B\) has 11-integral coefficients and reduces modulo \(11^2=121\) to
\[
 u=X^2+34X+97,\qquad v=72X+67.
\]
The two simple \(u\) roots have associated \((X,Y)\) residues modulo 121 of \((78,117)\) and \((9,110)\). Modulo 11 these are \(P\) and \((9,0)\), respectively.

Write \(\omega_0=dX/(2Y)\), \(\omega_1=X\omega_0\). Since \(28D\) reduces to zero, compute its Abel–Jacobi logarithm as the difference between the two support points of \(28D+B\) and the matching points of \(B\). The formal group logarithm agrees on a residue disk with integrating the pullback differentials. To first order at \(P\), use \(X-1\), giving \(7/(2\cdot40)\) after dividing the \(\omega_0\)-logarithm by 11. At \((9,0)\), use \(Y\), so \(\omega_0=dY/F'(X)\); the second contribution is \(10/F'(9)\), with \(F'(9)=2\cdot81\cdot60\). The \(\omega_1\) read multiplies these by 1 and 9, respectively. The two sums are
\[
 \frac{\log(28D)}{11}
 \equiv (6+3,\ 6+9\cdot3)=(9,0)\pmod {11}.
\]
Here the first-order logarithm is valid because \(p=11\) and both parameters are in \(11\mathbb Z_{11}\), so all nonlinear integral terms are in \(11^2\mathbb Z_{11}\). The first coordinate is nonzero, which proves \(D\) is **not** torsion in \(J(\mathbb Q)\). Together with the upper bound this also proves the exact rank is one. Finite-field order 28 alone would not prove this.

## 4. Two disks and the contradiction

By rank one, every rational Jacobian class has logarithm in the \(\mathbb Q_{11}\)-line spanned by \(\log(28D)\). Consequently the form
\[
 \eta=\omega_1-
 \frac{\log_1(28D)}{\log_0(28D)}\,\omega_0
\]
annihilates the logarithms of all rational classes. Its coefficients are integral at 11, and it reduces to \(X\,dX/(2Y)\). This is the local rank-one [effective Chabauty](https://doi.org/10.1215/S0012-7094-85-05240-8) step; no global integral evaluation is needed.

At \(P\) and \(P^-\), the parameter \(u=X-1\) is uniformizing and the local power series for \(\eta\) has integral coefficients and constant coefficient a unit modulo 11. Indeed \(Y\) is the integral unit branch of the implicit square-root equation on each disk, and \(X=1\) in the reduction. For any point in its disk with \(u\ne0\) and \(m=v_{11}(u)\ge1\), the first term in the local integral has valuation \(m\). The term of degree \(j+1\), for \(j\ge1\), has valuation at least \((j+1)m-v_{11}(j+1)>m\). Hence the integral cannot vanish except at the base point. For a rational point in that disk the integral necessarily vanishes, being the logarithm pairing with its difference from the rational base point. Thus the only rational points in these two disks are \(P,P^-\).

The rational clock point from §1 must therefore have \(X=1\). This forces the already excluded front value \(t=2/3\), completing the rational one-clock contradiction.

## Verification boundary

- [Exact Python replay](check-dirk10-genus-two-closure.py): verifies the local point square classes and complete span ranks, the global binary intersections, the rational and mod-11 Cantor computations and the leading local logarithm. No numerical group rank search.
- [Init-only Lean receipts](../../lean/RKCert/ReviewedNative/DIRKOrderTenGenusTwoReceipts.lean): check the finite binary Gaussian elimination, the two support residues and their leading logarithm read, and the complete mod-11 target disk list. The number-field transport, Jacobian and local analytic interpretation, and the inherited tableau reductions are mathematical arguments, not a native Lean proof of the full \(\mathtt{HasOrder}\) contradiction.
- No claim is made about rational tableaux with cubic defects on two or more distinct numerical clocks.
