# Arithmetic filters for one factorial-localized eleven-stage method

A separate unresolved problem is whether one **eleven-stage** exact order-eight tableau has every entry in \(U=\mathbb Z[1/210]\). The [three-chart local portfolio](../erk-eight-local-rings/README.md) does not give such a tableau. The four-support rank-three chart already gives rational methods and its unresolved problem is divisibility, not real feasibility. The following constraints address its endpoint six-site scalar rule, without claiming that every conceivable eleven-stage method has this scalar shape.

## The two scalar equations and the 7-adic classification

Center the endpoints at \(-1,1\), and write \(a,b,c,d\) for the four additional rational scalar sites. Let \(s_i\) be their elementary symmetric functions. If the rule integrates degrees through seven, its six-site nodal polynomial and that polynomial times \(X\) integrate to zero. Odd and even terms in the uniform integral on \([-1,1]\) give
\[
       7s_2+35s_4+3=0,\qquad 3s_1+7s_3=0.
\]
A rational endpoint quadrature cannot have an additional site at the center: if \(s_4=0\), the monic quartic of additional sites is \(X(X-s_1)(X^2-3/7)\), which does not split over \(\mathbb Q\).

Exactly **two** of the four sites have negative 7-adic valuation. All integral is impossible by reducing the even equation. For one pole, divide the odd equation by that pole: its residue modulo 7 is 3. For three poles, divide the odd equation by their product: the term from their triple product is 7 modulo \(7^2\), and all other terms vanish modulo \(7^2\). For four poles, divide the even equation by the product of the four: the term 35 has valuation one and the other terms have higher valuation. All three counts are impossible.

Take \(a,b\) 7-integral, \(u=1/c,v=1/d\) the two pole reciprocals, \(S=a+b,P=ab,C=3+7P\), and \(\sigma=u+v,\pi=uv\). The two scalar equations become
\[
 7S\sigma+C\pi=-7(1+5P),\qquad C\sigma+3S\pi=-7S .
\]
Since \(u,v\) are multiples of 7, reduction of the first equation after dividing by 7 gives \(P\equiv4\pmod7\). The four unordered residue pairs for \(a,b\) are \((1,4),(2,2),(3,6),(5,5)\), so \(S\not\equiv0\pmod7\). Thus \(\nu_7(\sigma)=1\), and at least one of \(u,v\) has that valuation. The denominator-cleared identities yield
\[
 \sigma=\frac{56SP}{C^2-21S^2},\qquad
 \pi=\frac{49S^2-7C(1+5P)}{C^2-21S^2}.
\]
The denominator is a 7-adic unit. In particular, for \(T=(1+5P)/7\), splitting requires
\[
 (\sigma/7)^2-4\pi/49\equiv 2S^2-T\in\{0,1,2,4\}\pmod7 .
\]
A reflection-symmetric six-site rule would have \(b=-a\) for its two integral sites, giving \(a^2\equiv3\pmod7\), which is impossible. The same exclusion follows directly from the equation \(7(a^2+b^2)-35a^2b^2=3\) for the two opposite-site pairs: if both are 7-integral reduce modulo 7, and if one is not, clear denominators, divide by 7 and reduce to a nonsquare relation for the numerator and denominator of the other.

## Restrictions at the non-factorial primes

If the six sites and weights are \(p\)-integral for \(p\ge11\) with \(21\) nonsquare modulo \(p\), all six sites stay distinct in reduction. Otherwise pad the reduced rule to five available sites including \(-1,1\) and use its nodal polynomial, times \(X\) and \(X^2\). If \(X^3-rX^2+sX-t\) is the monic cubic of the three nonendpoint sites, these three moments give \(r+5t=0,\ 7s=-3,\ 3r+7t=0\). Hence the cubic is \(X(X^2-3/7)\), which cannot split. The same quartic factorization as above forces the four interior residues to avoid the center zero.

In particular all four additional sites must reduce to the unique **unordered** centered quadruples
\[
  \{2,5,6,9\}\pmod{11},\qquad
  \{4,6,7,9\}\pmod{13}.
\]
Thus their sum is divisible by both 11 and 13 in the factorial localization. This is a necessary integrality filter, not a local obstruction: the denominator portfolio already gives bona fide 11- and 13-integral rational witnesses separately.

The [Lean module](../../lean/RKCert/ReviewedNative/ERK8CenteredQuadratureConstraints.lean) kernel-checks the vanishing centered sum in the two residue characteristics, the direct rational nonsquare obstruction for the symmetric pair equation, and the denominator-cleared reciprocal coefficient identities. It does not certify nonexistence over \(U\). The valuation and inert-prime arguments above are mathematical proofs stated separately from those native lemmas.

## Bounded diagnostic

The supplied C++ exact search included every candidate for the two 7-integral sites with reduced numerator and denominator absolute values at most 6,500. It uses the necessary small-prime residue restrictions at \(11,13,19,23,31\), \(ab\equiv4\pmod7\), and the mod-49 square test. Other factors of the exact integer discriminant are filtered by elementary square residue tests, and any surviving square is tested as an exact 128-bit integer. No bound on the two pole heights is imposed by this pair search. Among 44,062 filtered rational abscissae and 1,667,830 compatible pairs, there were no exact square discriminants. This is **only bounded evidence** for the six-site chart, not exhaustion of its \(U\)-points and not a tableau obstruction outside this chart.

    g++ -O3 -std=c++17 scan_factorial_sites.cpp -o /tmp/scan_factorial_sites
    /tmp/scan_factorial_sites 6500
