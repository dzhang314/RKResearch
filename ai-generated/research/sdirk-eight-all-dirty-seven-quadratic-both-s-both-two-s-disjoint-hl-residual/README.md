# High/low disjoint \((1,1)\): the off-curve residual chart is empty

This completes the **A2/A3 and A2/star** unequal-law disjoint \((1,1)\) charts over every characteristic-zero field, when combined with the independent [lost-scale-rank and regular \(Q=0\) packet](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl/README.md). The setting is strict ten-stage SDIRK of ordinary order at least eight, exactly seven clock labels, every literal quadratic defect nonzero, genuine quadratic singleton graph, two literal singleton endpoints, exactly one later singleton and one doubled label used in each actual first-three prefix, and different observed doubled labels. Reverse the orientation using the genuine weighted mirror. Equal later singleton offsets are allowed in these unequal-law charts. The high/high off-diagonal and disjoint mixed-count charts are separate.

The previous packet's bivariate gcd identified \(Q\) as a common component of three projections, not as the full common locus. In this packet \(Q(H,a)\ne0\) and \(M\ne0\) are **branch assumptions**. We cover the possible isolated common points outside the common curve by a full univariate projection. No direction in the implication depends on a bivariate gcd.

## Genuine partner degrees and exact projections

Use \(H,a,b,\lambda\), the high/low partner \(\Gamma=c_0+c_1b+c_2b^2\), and the paid equations \(E,G,Y\) of the [shared scale setup](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-scale/README.md) and the earlier packet. In particular \(E,G\) are the two actual cubic graph rows and \(Y\) compares \(B\lambda\) at the two unshared physical doubled reads. All numerators already have their actual denominators audited. The previous scale reduction proves that \(\Gamma\) cannot lose *all* coefficients at a true base, so the nonzero polynomial at such a base can have degree one or two if it has a root.

**Degree one, \(c_2=0\).** Project \(c_0+c_1b\) against each of \(E,G,Y\), canceling only true \(b\)-independent guards including \(Q\), then project each of those rows against \(c_2\) in \(a\). The remaining common univariate \(H\) factors have (degree, multiplicity) \((23,2),(8,5),(12,5),(4,15)\) for both phases. In the corresponding exact \(H\) fields, a joint \(a\)-divisor is the exact gcd of \(c_2\) with, respectively, \(Q\), \(N(a/2)\), \(N(a/2)\), and \(D(a/2)\). The exact degrees are \(1,1,1,3\). The replay verifies exact division of all three projected rows by this divisor.

At fixed good places \((p,H\bmod p)=(997,650),(1031,655),(997,471),(997,961)\), the specialized \(c_2\) retains its full \(a\)-degree with nonzero leading coefficient, and the finite joint gcd degrees are respectively \(1,1,1,3\). These are upper bounds on the characteristic-zero fibre gcd degrees: divide \(c_2\) by its unit leading coefficient to make it monic over the valuation ring. Every monic divisor of it in the fraction field is integral, since its roots are integral, and monic division preserves integrality of each quotient. Thus the exact known common guard divisor already exhausts the common locus. No curve or denominator is dropped from the degree-one case.

**Degree two, \(c_2\ne0\).** At any simultaneous zero, every pseudo-remainder operation \(P\mapsto c_2P-\ell b^j\Gamma\) preserves vanishing. Remove only stated true \(b\)-independent factors at each step. Reduce \(E,G,Y\) to three affine polynomials in \(b\). Their three coefficient minors \(X_0,X_1,X_2\), in pair order \(EG,EY,GY\), must vanish. Also take the separate \(b\)-resultants \(U_0,U_1,U_2\) of \(\Gamma\) against \(E,G,Y\), removing only factors nonzero on this branch. All six are necessary two-coordinate rows. We take an actual single-coordinate elimination in \(a\):
\[
\begin{array}{c|c|c|c}
\text{phase} & \text{univariate projection} & \deg_H & \text{irreducible factors after true pure }H\text{ guards}\\\hline
\text{A2/star} & \operatorname{Res}_a(X_1,X_2) & 2378 & 18\\
\text{A2/A3} & \operatorname{Res}_a(X_0,U_1) & 3486 & 18
\end{array}
\]
A nominal resultant vanishes at any common finite root even if the highest coefficient subsequently vanishes. The exact resultant reconstruction uses a proved Hadamard coefficient bound, good-degree modular interpolation, and signed CRT with modulus greater than twice the bound. It does not stop at apparent stabilization.

## How fixed places exclude every irreducible factor

For each rational irreducible factor \(f(H)\) of the actual univariate eliminant, a characteristic-zero candidate with \(f(H)=0\) has coefficient field \(\mathbb Q[H]/(f)\) at that coordinate. A specified simple root in \(\mathbb F_p\) gives an embedding into \(\mathbb Q_p\) by Hensel. Use an algebraic closure of that valued field, without assuming the method's field is real or that any polynomial splits over the residue prime field. At each tested place at least one of the six necessary \(a\)-rows keeps its full positive nominal degree, so an actual \(a\) is algebraic over \(\mathbb Q(H)\) and integral at the place. If their residue gcd is a unit, no such \(a\) exists. Otherwise the replay explicitly checks that all its geometric roots are from the listed prime field and examines *every* one. At each such root at least one necessary \(b\)-row keeps its full positive nominal degree, making the actual \(b\) integral there; its common residue gcd is a unit. The affine remainders are available among the \(b\)-rows. No true nonzero guard is assumed to stay nonzero modulo \(p\).

For A2/star, 15 factors have unit \(a\)-gcd directly. The remaining three factors, of degrees \(8,12,4\) and multiplicities \(9,16,27\), have split \(a\)-gcds of degrees \(2,4,6\) and unit remaining \(b\)-gcd at each root. For A2/A3, 15 factors have unit \(a\)-gcd directly; two factors of degrees \(8,12\) and multiplicity \(20\) have split \(a\)-gcds of degree \(4\) with the same unit \(b\) conclusion. The last factor is \(f(H)=H^4-12H^3-6H^2+12H+6\), with multiplicity \(82\). For it, remove all factors supported on the true nonzero \(D(a/2)\) **exactly** in \((\mathbb Q[H]/(f))[a]\). The six degrees go \(46\to34,78\to54,78\to54,54\to39,54\to39,77\to53\). At \((p,H\bmod p)=(1109,466)\) their exact quotient coefficients are integral and their degrees preserved, with unit gcd in \(a\). This is exact saturation in a finite extension of \(\mathbb Q\), not an inference from a vanishing guard in a residue.

## Replay and scope

With SymPy 1.14 and python-flint 0.8, from this directory run:

```sh
SYMPY_GROUND_TYPES=flint python check_degree_drop.py
SYMPY_GROUND_TYPES=flint python check_quadratic.py
```

The second command reconstructs both exact univariate resultants with no cache. You can select a phase with `--mode S` or `--mode A3`. On Linux LP64 the optional `--fast-library` accepts the [previous packet's exact multipoint C accelerator](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-final/README.md#replaying). Using it, the two projections take roughly two minutes together and modest memory; the default direct modular FLINT implementation is slower and requires no compiler. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHLResidual.lean) states the pseudo-remainder and affine minor identities; the tableau ingress, projections, degree guards and place census are not all native Lean. This is a characteristic-zero chart exclusion, not a finite-characteristic stage lower bound. The general numeric stage interval is unchanged.

The root publication audit independently reran both exact projections and the complete place census. The scalar Lean companion is a draft and was not kernel-checked for this release.
