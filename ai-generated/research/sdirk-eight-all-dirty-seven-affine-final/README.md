# The affine singleton-residual graph is impossible at the all-dirty seven-clock floor

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with all ten physical quadratic residuals nonzero and exactly seven different clock labels. Three labels are doubled (D), and four are singleton (S). Use the [seven-clock graph \(g=R(t)\)](../sdirk-eight-all-dirty-seven-clock/README.md) on those four singleton labels; neither copy at a doubled label has that graph residual.

**Conclusion.** \(R\) cannot be affine nonconstant. The [constant graph](../sdirk-eight-all-dirty-seven-constant/README.md) is already impossible, so exactly-seven all-dirty tableaux, if they exist, must have a **genuinely quadratic** singleton-residual graph. This does not exclude quadratic graphs, more than seven labels, or ten-stage strict SDIRK8 in general. The proof is valid for signed weights over every characteristic-zero field. The local residues below certify a characteristic-zero exclusion, not a stage bound over the named residue fields.

## Exhaustion of literal endpoint possibilities

The prior [one-double-end exclusion](../sdirk-eight-all-dirty-seven-affine-one-double-end/README.md) and the original affine parity argument make both literal endpoint labels singleton. No actual opening has three singleton labels, by the [first off-graph chronology test](../sdirk-eight-all-dirty-seven-affine-openers/README.md). The [both two-singleton exclusions](../sdirk-eight-all-dirty-seven-affine-two-singletons/README.md) rule out two singleton labels in both openings; the [both S,D,D exclusion](../sdirk-eight-all-dirty-seven-affine-two-double-prefixes/README.md) rules out two doubled labels in both openings. By true weighted mirror duality, we may orient the remaining case so the forward prefix is S,D,D and the reverse prefix contains exactly two S labels. That reverse prefix is one of:
- A, literal S,S,D arithmetic, with the doubled offset \(4-2/b\);
- S, either star ordering S,S,D or S,D,S, with doubled offset \(1/b\);
- T, literal S,D,S arithmetic, with doubled offset \(u\) and \(b=D(u)/[2(u-2)(u^3-3u^2+1)]\).

Here \(b\) is the reverse affine graph offset determined by the zero and the first physical reverse singleton, and \(D(u)=-2+u+4u^2-u^3\). The equality of the two star pair sets does not permute a proposed tableau. These calculations use only the genuine residuals and clock labels paid by those prefixes. The separate A/S/T list and the true weighted mirror cover both possible endpoint orientations.

## Degree-six norm in the graph-zero parameter

Normalize the diagonal to one and set \(\ell=1/\gamma\). Use dimensionless coordinate \(v=(2x-\ell)/\ell\). The graph zero is \(s\), the first and terminal labels are \(-e,e\) with \(e=(\ell-2)/\ell\), and the three D labels are \(\alpha,\beta,\chi\), with \(\alpha,\beta\) the physical second and third labels. They are the three simple roots of the exact polynomial \(K(v,s;1)\) from the [affine divided difference](../sdirk-eight-all-dirty-seven-affine-openers/README.md). Its leading coefficient \(L=-35J_3(s)\) is nonzero. The forward phase determines \(e=\beta-2\alpha\) in arithmetic or \(e=(2-\alpha-\beta)/4\) in star.

For the reverse D label choose \(\rho\) among \(\alpha,\beta,\chi\), as an original dimensionless label. Set \(w=e-\rho,\ d=1-e,\ z=s-e\). Its actual reverse offset is \(w/d\), while \(b=z/d\). Substitution into the three stated reverse tests gives the following exact polynomial equations, with \(d\ne0\):
\[
 \begin{array}{ll}
 \mathrm A: & z(w-4d)+2d^2=0,\\
 \mathrm S: & zw-d^2=0,\\
 \mathrm T: & 2z(w-2d)(w^3-3w^2d+d^3)
                        -d^2(-2d^3+w d^2+4w^2d-w^3)=0 .
 \end{array}
\]
This covers all \(2\times3\times3=18\) forward-phase, reverse-phase, and reverse-label choices. None divide by \(K(s,s;1)\), and a common root of \(R,P\) is not forbidden.

Let the equation selected above be \(\Phi(\alpha,\beta,s)\) after substituting \(\chi\) using the sum of D clocks. To project its possible solutions in \(s\), let \(\Sigma,\Tau\) denote the sum of D labels and sum of their pair products. For fixed \(\alpha\), the two possibilities for \(\beta\) are the roots of
\[
 \beta^2-(\Sigma-\alpha)\beta+\Tau-\alpha(\Sigma-\alpha)=0 .
\]
In \(\mathbb Q(s)\) reduce \(\Phi\) by this monic quadratic in \(\beta\) and the monic \(K(\alpha,s;1)/L\) in \(\alpha\). The result is \(A(\alpha)+D_1(\alpha)\beta\); its product over the two remaining D labels equals
\[
 A^2+(\Sigma-\alpha)A D_1+(\Tau-\alpha(\Sigma-\alpha))D_1^2 .
\]
Take its resultant in \(\alpha\) with the monic cubic. This is the product over all six ordered choices of \(\alpha,\beta\), so its value must be zero at any actual tableau. Its only possible denominator factors are those of \(J_3(s)\); the replay explicitly checks that property. Exact rational factorization yields exactly one irreducible numerator factor for each chart. The possible degrees are 18, 28, 30, 36, 45, 66, and 90, with multiplicity two precisely in the three forward-star charts using the unused D label as the reverse D. The factor degrees and multiplicities are fixed in the replay.

## Why one good reduction excludes a whole characteristic-zero field

For a given chart let \(f(s)\in\mathbb Z[s]\) be its irreducible projection factor after clearing rational content. All relevant pair coordinates are algebraic over \(\mathbb Q\): \(f(s)=0\), the three D labels solve the cubic over \(\mathbb Q(s)\), and the clock positions, forward residuals, mirror scale, and the other known reverse singleton then follow rationally. This remains true if the ambient coefficient field is transcendental or non-ordered.

Choose the listed small prime \(p\) and simple residue root \(\bar s\) of \(f\); the leading coefficient of \(f\) is a \(p\)-unit. A hypothetical characteristic-zero solution may be embedded into \(\overline{\mathbb Q_p}\) with its graph parameter sent to the Hensel lift of that very \(\bar s\), because \(f\) is irreducible over \(\mathbb Q\). Extend the embedding to the algebraic labels. The monic D-clock cubic over this lift has integral coefficients, since \(J_3(\bar s)\ne0\); all three roots are therefore integral. Its reduction has exactly three distinct roots, each in \(\mathbb F_p\). Hence the three lifted labels reduce to a permutation of these roots, preserving distinctness. The true polynomial phase equation \(\Phi=0\) must still hold in the residue field. No existence of a lifted tableau or uniform reduction at every prime is used.

The fixed local ledger enumerates **every** permutation with \(\Phi=0\) at \(\bar s\). For each it verifies the nonzero denominator and distinct-clock guards before taking any division in the following actual formulas. With \(a=-(e+s)/(1-e)\), \(R(x)=(x-1+a)/(2a)\) and mirror conversion \(\lambda=-b/a\), the original first and last singleton and the reflected additional singleton are now known. Their values \(C=L_4/R\) uniquely fix the quadratic \(C=A_2+B R\). The literal forward second D pair determines \(B\) from
\[
 B=\frac{L_4(x_2-\ell/2)-g_2 C(x_2)}
           {g_2(g_2-R(x_2))},
\]
where this denominator is checked to be a \(p\)-unit. Thus \(C,B\) from any hypothetical characteristic-zero solution at this prime reduce to the directly computed values. The replay **does not** discard a candidate merely because \(B\) reduces to zero. It evaluates the other known forward D and reverse D equations \(U=L_4-gC-Bg(g-R)=0\). Every possible permutation has at least one nonzero obstruction (in the fixed ledger both values are nonzero in all cases). This contradicts the required reduction of a zero equation. The argument never divides by \(R\) at a doubled label.

## Fixed audit ledger and replay

The exact residue pairs are stored in `check_mixed_good_reduction.py`. For reference the prime/root choices, in order \(\rho=\alpha,\beta,\chi\), are:

| Forward / reverse | Three \((p,\bar s)\) certificates |
|---|---|
| A / A | \((41,8),(31,29),(41,8)\) |
| A / S | \((13,11),(13,11),(13,2)\) |
| A / T | \((29,13),(31,11),(29,16)\) |
| S / A | \((29,16),(29,16),(41,12)\) |
| S / S | \((41,26),(37,10),(37,27)\) |
| S / T | \((53,8),(53,8),(59,5)\) |

Run `python check_mixed_good_reduction.py` (SymPy 1.14 and python-flint 0.8 tested). The sibling `mixed_sdd_norm.py` regenerates the exact irreducible projections, including denominator-factor assertions; the audit verifies the fixed primes, their simple roots, all literal reductions and nonzero incompatibilities. No bounded search is used in the replay. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenAffineFinal.lean) stages compact scalar identities, not the full projection, Hensel and chronology theorem. No stock Lean build is asserted here.
