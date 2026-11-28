# DIRK12/15: three earlier terminal-clock repeats excluded on the nine-site early-return chart

Work in the real ordinary fifteen-stage order-twelve \(C(2),f_5=3\) weighted-invisible four-distinct-dirty-ghost frame, with the [actual nine-distinct-nonterminal-site early reverse return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md). Suppose the numerical clock \(1\) of the literal ordinary terminal is also read at one of the first five distinct nonzero ordinary live clocks \(a,b,c,e,f\). Previous exact proofs exclude \(f=1\), in the [first-root](../dirk12-fifteen-rank3-invisible-nine-site-first-root-zero-exclusion/README.md) and [nonroot](../dirk12-fifteen-rank3-invisible-nine-site-nonroot-zero-exclusion/README.md) cases.

Here \(a=1,\ b=1,\ c=1\) are excluded with no assumption on individual signed weights or ghost geometry. The possible repeated-terminal branch \(e=1\) is not addressed by these exclusions, nor is any branch in which the literal terminal is the only such stage. Other nine-site chronologies are not included. The real DIRK12 interval remains **15–16**.

## The two true fourth zero-diagonal equations

The [both-chart proof](../dirk12-fifteen-rank3-invisible-nonzero-fourth-exclusion/README.md) gives the actual fourth nonzero live diagonal zero. In normalized ordinary variables \(T=X/a,\ x=b/a,\ y=c/a,\ t=e/a\), use
\[
  P_0(T)=T(T-1)(T-x)(T-y).
\]
Both \(P_0,TP_0\) have numerical value zero on all available prior live sources and their own tap has zero diagonal. Excluding the four literal ghost taps, the real normalized outputs \(\mathcal A(P_0)(t),\mathcal A(TP_0)(t)\) vanish. Their polynomial projections are the actual first-three [root or nonroot scalar two-mode formulas](../dirk12-fifteen-rank3-invisible-all-ordinary-prefixes/README.md); their numerators are divisible by \(P_0\) by exact origin and first-three guard values. The quotient equations have degree at most three. Since \(t\) is distinct from \(0,1,x,y\), both quotient equations vanish.

Let \(L=L_6'\), \(D=2xy-x-3y^2+2y\), \(S=3x^2-2xy-2x+y\), and \(P(x,y)\) the explicit [third ordinary polynomial](../dirk12-fifteen-rank3-invisible-third-ordinary-live/README.md). The exact prefix conditions for \(L(a)\ne0\) are
\[
 (2x-1)L(ax)-x^3(2x^2-6x+5)L(a)=0,\qquad
 (2x-1)D L(ay)+y^2 P(x,y)L(a)=0.
\]
For \(L(a)=0\) the corresponding third gate is
\[
 x^2(x-1)^3D L(ay)+y^2(y-1)^3 S L(ax)=0 .
\]
When adjoining \(y\) for a known \(a,x\), remove the genuine factors \(y-1,y-x\) in each third polynomial. The residual degree is five with its checked polynomial leading coefficient; no root at an unavailable site is kept.

## Exact finite algebras, including both Legendre branches

* **First clock \(a=1\):** \(L(1)=42\ne0\). The second equation is \(42(x-1)\) times a quintic; remove the excluded \(x=1\) and adjoin a root of the quintic. Then adjoin \(y\) by the first nonroot third residual.
* **Second clock \(b=1\):** \(x=1/a\). If \(L(a)\ne0\), the second equation is \(-42(a-1)/a^5\) times a sextic, and \(a=1\) is prohibited. If \(L(a)=0\), adjoin \(a\) by \(L(a)\) instead. Then adjoin \(y\) by the relevant third residual.
* **Third clock \(c=1\), first Legendre root:** put \(y=1/a\), with \(L(a)=0\). The cleared third polynomial has the excluded factor \(ax-1\), since \(x=y\) is forbidden. Its quotient has \(x\)-degree six, with leading coefficient a nonzero rational constant times \(a^5(a-1)^3\). It vanishes at \(x=1\) modulo \(L(a)\) because the first term of the third equation has \((x-1)^3\) and the second has \(L(ax)\). Remove that excluded factor too. The retained exact degree-five polynomial determines \(x\).
* **Third clock \(c=1\), first nonroot:** substitute \(y=1/a\) and remove the known \(x-1\) factor in the second equation and \(a-1\) from the cleared third. The third is quadratic in \(x\). The resultant in \(x\) has factors \(a L(a)\), the preceding sextic for \(b=1\), and a remaining \(a\)-factor of degree 30, up to constant. The linear \(x\)-subresultant \(U(a)x+V(a)\) has \(U\) coprime to the sextic and \(U+aV\) divisible by it. Hence that factor forces \(x=1/a=y\), forbidden. The entire remaining projection is the degree-30 polynomial with the same linear subresultant, not an assumption of generic nonvanishing.

For the five exact branches the following prime receipts check every residue field:
\[
\begin{array}{c|r|r|r}
\text{literal clock}&p&\text{number of fields}&\text{sum of field degrees}\\ \hline
a=1&17&5&25\\
b=1,\ L(a)\ne0&19&6&30\\
b=1,\ L(a)=0&19&6&25\\
c=1,\ L(a)=0&19&6&25\\
c=1,\ L(a)\ne0&19&2&30
\end{array}
\]
All selected leading coefficients at each base and secondary normalized branch are units. In the last line the carried linear \(x\)-subresultant coefficient is a unit on both degree-11 and degree-19 fields. In every field the literal scalar three-mode interpolation and all ordinary primitive denominators are units. The first of the two fourth quotients has degree exactly three after reduction, its maximum possible characteristic-zero degree, and the two fourth quotients are coprime.

For an actual algebraic \(a,x,y,t\) choose a prime of its number field above the indicated \(p\). The unit leading coefficients first give integrality of the base coordinate and the monic secondary coordinate (or the linear formula for \(x\)); all checked units make the literal formulas integral. The unit cubic leading coefficient then gives integrality of \(t\). Its reduction would be a common root of the two retained fourth equations, contradicting the exact unit gcd in whichever residue field applies. This reduces finite scalar coefficient algebras only. It does not reduce an unknown tableau, assumes no sign of any weight, and uses no scalar degree-twelve moment.

## Replay

    python3 -B rebuild.py    # exact symbolic characteristic-zero identities, SymPy
    python3 -B verify.py     # independent standard-library field replay

The first program verifies the discarded factors, exact resultants and characteristic-zero degree logic, and regenerates or verifies the stated projection coefficients. The second verifies every base factor product and irreducibility, the full next-layer factor products and irreducibility, all guards, and the actual fourth quotient coprimeness. There is no asserted Lean theorem for this separate five-branch closure; a previous portable module covers the related fourth-supported mask.
