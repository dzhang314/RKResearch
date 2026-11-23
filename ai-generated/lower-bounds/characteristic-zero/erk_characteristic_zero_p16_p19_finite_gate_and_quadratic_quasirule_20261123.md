# The elementary finite-order ERK inequalities p=16,17,18,19 hold over every characteristic-zero field

23 November 2026. This audits precisely the four-order theorem in pass2245_finite_analytic.md, not the stronger real stage-count ledger. For any K of characteristic zero its conclusion is s_K(p)≥ceil(3p/2), i.e. 24,26,27,29 stages, respectively. The two difficult nonreal ratios are genuinely allowed by its isolated 3+2 moment minor, so dismissing them via its negative discriminant is invalid. At p17 one unrestricted quasi-Jacobi parameter also need not be real. We resolve both issues below.

## Structural ingredients and budgets

Work with a hypothetical s=ceil(3p/2)−1 and q=floor(p/2)=8 or 9. Sections 1–3 of pass2245_finite_analytic.md are algebraic after the following repairs: use all available degree-bounded scalar test polynomials and invert the fixed rational moment Gram wherever the source used a single positive square, including the odd prefix e_s test and reversed-polynomial independence. Use the one-head filtration in erk_field_independent_surgery_one_head_and_p12_baselines_20261123.md, not a Euclidean projection; the projected effective-head argument and eventual mask algebra in this particular finite proof are already stated without projected orthogonality. Strong Hermite and the resulting r≥2 are proved field-free in erk_characteristic_zero_logarithmic_stage_bound_rodrigues_boundary_jets_20261123.md. The D and J orthogonal families refer to fixed rational positive-weight moments: their ranks, simplicity, neighboring-recurrence nonvanishing and coprimality can be verified over R once and transported as nonzero rational/algebraic facts. The free parameter θ in the odd prefix/no-alias case is NOT restricted by this observation: only the coefficients of the two fixed D polynomials are rational. The grade-10 shifts and elimination of leakage in pass2245_finite_analytic.md use those nonzero rational recurrence coefficients, not a purported sign of θ.

All three physical cases of that note (even full; odd with ell_1≠0 full; odd ell_1=0 prefix, with or without polynomial alias) give a cleaned nonzero head w=P(c) on support S disjoint from the mask set T, with deg P≤4, and w,Cw∈F5. When the prefix has an alias, its factorization in the source already improves deg P≤3. Under NO alias the source's polynomial G of degree q+1 has G(c) in U+wP_(r+q−5)(c) on the retained coordinates, and U consists of the node masks T. Thus G vanishes at every physical coordinate R outside S∪T. On S we have G=P Q for deg Q≤r+q−5. Since deg P≤6−r and the number of distinct S nodes is at least r+p−8>q+1, this equality is a formal polynomial identity. At the two actual contrast endpoints u and v, which are in R, the construction gives u,v nonzero distinct and P(u),P(v) nonzero. Therefore P, x−u and x−v all divide G, and these two linear factors are coprime to P.

The grade audit for a mask of degree k in the final contrasts is as follows. For k≥1, the w contribution has grade at most 5+(k−1) since Cw∈F5; the polynomial contribution has grade ≤4+k; the mask contribution is in the invariant grade-5 U. Its A-primitive is thus available in F_q for k≤q−5. The positive-degree test mask may be xR or x(x−u)R. When q=9 we may take ALL four first moments (k=1,2,3,4) and all three second moments (k up to 4), not just the 3+2 needed over R. When q=8 we get 3+2 exactly. For all these cases the contrast is genuinely nonzero by the existing separation through grade q; its first nonzero coordinate is in R, and the A-primitive, by causal chronology, vanishes there.

## Eliminate all but one quadratic extension calculation

If q=9, use the two-endpoint Rodrigues/jet lemma with m=4 and deg P≤4. It eliminates every branch, including any complex odd-prefix quasi-parameter. If q=8 and deg P≤3 (in particular every prefix-alias case), use the same lemma with m=3 and 3+2 tests. Here test spaces are ∫_0^1 x R P=0, deg R≤2, and ∫_0^a x(x−1)R P=0, deg R≤1; jets through order two still contradict the simple nonzero critical point. It remains only q=8, no alias, with quartic P. Normalize a=v/u. For a quartic the 3+2 determinant in pass2245_finite_analytic.md is proportional to a^6(a−1)^6(15a²−24a+10), hence a=(12±sqrt(−6))/15.

In the even p16 case, G is proportional to x(1−x)D7, where D_n is the degree-n orthogonal polynomial for x(1−x) dx. Both u,v are roots of this fixed rational all-real polynomial, by the preceding physical R observation, so their ratio cannot be either exceptional nonreal value. The same argument works in the full-tableau p17, ell_1≠0 case, where G/x is the fixed rational Jacobi polynomial of degree 8 for weight x. It is legitimate to make this argument after embedding the finitely generated coefficients in C: here “all-real” is a fact about fixed rational polynomials, not about the tableau coefficients. The last free-θ prefix at p17 requires an actual new calculation.

## p17, ell_1=0, no alias: exact obstruction, regardless of θ

Here G/x, up to normalization, is D8+θD7, where we may take D_n=(shifted Legendre of degree n+1)' and absorb the normalization into θ. Write h²=−6 and t=(12+h)/15, taking its conjugate as needed. The unique surviving *monic* normalized quartic (in X=x/u) is
    P_t(X)=X^4−(49+2h)X³/20+(72+6h)X²/35−(47+6h)X/70+(23+4h)/350.
Direct formal integration checks ∫_0^1 X^k P_t=0 for 1≤k≤3 and ∫_0^t X^k(X−1)P_t=0 for k=1,2. Uniqueness: after the first three tests the space is span(J3,J4) for weight X. The second system's coefficient on J3 at k=1 is t²(t−1)²(5t−2)(7t−6)/6, nonzero at both t, so the nullspace is exactly a line. In particular P_t(0)≠0 (the numerator 23+4h has rational norm 625). The necessary coprime-factor relation from the no-alias stage chart now says, for some original nonzero u and free θ,
    E(X)=(X−1)(X−t)P_t(X)  divides  D8(uX)+θD7(uX).
This is stronger than the abstract two-endpoint 3+2 minor: the same two real-or-complex chronology witnesses force the five coefficients into a six-root portion of ONE finite quasi-rule.

Let A_i(U), B_i(U) be the coefficients of X^i in the remainders of D8(UX), D7(UX) modulo monic E in K0[X], K0=Q(h). Then N1=A0 B1−A1 B0, N2=A0 B2−A2 B0 must vanish at U=u. They contain factors U,U² respectively because the second/third coefficients of each power-series vector begin in degrees at least 1,2. Exact Euclidean computation over Q(sqrt(−6)) yields
    deg(N1/U)=14,  deg(N2/U²)=13,  gcd(N1/U,N2/U²)=1.
Thus there is no nonzero u, even when θ is completely unrestricted.

A compact exact replay in SymPy (all coefficients are algebraic, not floats):

    import sympy as S
    x,U=S.symbols('x U')
    h=S.sqrt(-6); t=(12+h)/15
    P=x**4-(49+2*h)*x**3/20+(72+6*h)*x**2/35-(47+6*h)*x/70+(23+4*h)/350
    E=S.Poly((x-1)*(x-t)*P,x,extension=h)
    def D(n):
        return [(-1)**(n-j)*(j+1)*S.binomial(n+1,j+1)*S.binomial(n+j+2,j+1)
                for j in range(n+1)]
    rem=[S.Poly(x**j,x,extension=h).rem(E) for j in range(9)]
    def vec(n,i):
        return sum(z*rem[j].nth(i)*U**j for j,z in enumerate(D(n)))
    A=[vec(8,i) for i in range(3)]
    B=[vec(7,i) for i in range(3)]
    N=[S.Poly(S.cancel((A[0]*B[i]-A[i]*B[0])/U**i),U,extension=h) for i in (1,2)]
    assert [v.degree() for v in N]==[14,13]
    assert S.gcd(*N).degree()==0

Independent direct exact K0 arithmetic (triples of integers (a,b,d) for (a+b h)/d) gave degrees [14,13] and monic gcd [1]. A separate modular replay at 97 checks both conjugates. For h=24, t=80 modulo 97, the two stripped minors in ascending coefficient order are
    [74,0,0,0,0,0,84,93,60,0,0,0,52,48,41]
    [73,0,0,0,58,69,77,17,19,0,0,0,94,14].
For h=73, t=38 modulo 97, they are
    [74,0,0,0,0,30,35,55,49,0,0,0,67,48,85]
    [73,0,0,0,33,23,64,26,43,0,0,41,10,11].
Both pairs have gcd one, both leading coefficients survive, and the resultant is therefore nonzero even independently of the rational-extension gcd replay. This calculation exhausts the field-dependent obstruction, proving the stated four bounded-order inequalities.
