# A characteristic-zero proof of the logarithmic unrestricted ERK stage bound

23 November 2026. Let K be any characteristic-zero field. For ordinary classical explicit RK order p≥10 let q=floor(p/2), and let h be the largest integer such that 5·2^h≤q. Then
    s_K(p) ≥ ceil(3p/2)−1+h.
In particular s_K(20)≥30. This is the coefficient-field generalization of worker_log_standalone.md, not a larger integer lower bound over the reals. The only place the old proof actually needed order on its variable nodes was its last sign-changing-root count; we replace that step by a rational Rodrigues identity and boundary jets.

## Exact prerequisites

The pair algebra, ordinary separation through q, strict defect flag growth and compressed endpoint counting of worker_log_standalone.md, §§1–6, transport as specified in erk_field_independent_surgery_one_head_and_p12_baselines_20261123.md: use all tests and invert a fixed rational moment matrix, not a single possibly isotropic variable square. In particular f_5≥5, f_(k+1)≥f_k+1, and s≥ceil(3p/2)−2+f_q−(q−1). If F_k is C-invariant under separation through k, then f_k≥ceil(3k/2)−3 by its k distinct nonzero chronological completion rows and the earlier-primitive order-k stage bound on the prefix.

For precision, the stronger gain valid for every C-invariant U⊂F_j is
    f_(j+1) ≥ dim U + floor((j+1)/2).
This is the forward specialization of the lemma in pass2245_finite_analytic.md, paragraph beginning “For clarity”. Here are details excluding any hidden inner product. Compress the independent coordinate evaluations on P_j(c)+U; on its compressed coordinates U splits by c-block and its row annihilator has dimension j+1, with at most one independent row per node (another linear combination kills the constant and all P_j(c), hence the entire compressed space). There are exactly j+1 normalized node rows lambda_u, with lambda_u 1=1. Restriction does not increase the dimension of the image of F_(j+1); A on inputs in the compressed space is exactly obtained by strict earlier-coordinate substitution. Thus proving the gain there suffices. Take the first floor((j+1)/2) *nonzero* node rows, ordered by their latest nonzero chronological coordinate. They are independent on F_(j+1) modulo U in this sense: if a nonzero combination lambda of those rows annihilated F_(j+1), lambda A would kill U and be supported before the latest node u in that combination. It therefore lies in the span of the node rows completed strictly earlier, because their supports are node-disjoint. Take P=x²∏_(earlier nonzero nodes y)(x−y)² if zero has already completed, or P=x∏_(earlier nonzero nodes y)(x−y)² otherwise. Here “earlier” refers to all completed nodes before u, at most floor((j+1)/2)−1 of them nonzero. Then deg P'≤j, P'(y)=0 at each earlier node, and lambda P(c)≠0 via P(u)≠0 and the latest coefficient. But AP'(c)−P(c)∈F_(j+1) and lambda A P'(c)=0, a contradiction. Since all node rows kill U, the gain follows. Only Vandermonde, strict chronology and a formal derivative were used.

## Flat-band consequences and the two legitimate contrast budgets

Assume all j increments on [j,2j] equal one, j≥5, with separation through 2j. By the preceding gain F_j,…,F_(2j−1) cannot be C-invariant. Assume the endpoint F_(2j) noninvariant as well. The rank-one filtration proof in §2 of erk_field_independent_surgery_one_head_and_p12_baselines_20261123.md gives the maximal C-invariant U⊂F_j and w with r=dim F_j−dim U:
    F_(j+a)=U ⊕ w P_(r+a−1)(c),  0≤a≤j.
Indeed, writing F_j=U+span(w,…,C^(r−1)w), noninvariance makes each next C power exhaust the unique new dimension until a C-invariant whole span is reached; this is ruled out through 2j. There are at least N≥r+j+1 effective c nodes (otherwise the last displayed grade would saturate). Since f_(j+1)=dim U+r+1, the strong Hermite gain forces r≥floor((j+1)/2)−1≥2. The real argument that only bounded the head polynomial by j threw away this last piece of rank information.

For every f∈F_j, diag(f) F_j⊂F_(2j) by genuine product closure. These joint diagonal multipliers preserve U: the image of any node-local member can have a chain polynomial of degree ≤r+j−1, but that polynomial must vanish modulo U at ≥N−1 effective nodes, hence is zero. Use a complement to U respecting all multipliers and C by their joint coordinate blocks, choosing w in that complement without changing the chain spaces. The multiplier lemma there now gives f_i=P_f(c_i) on support S of w, with deg P_f≤j: use diag(f)C^k w=C^k diag(f)w for 0≤k<r and compare polynomials at N supported nodes. A node-local f∈U is zero on S because its polynomial vanishes at all other N−1>j support nodes, so U vanishes there. In particular w=P(c) on S for a nonzero P of degree ≤j. Apply the same statement to C^(r−1)w∈F_j. The polynomial x^(r−1)P agrees on N≥r+j+1 nodes with one of degree ≤j; since its degree is at most r+j−1, the identity is exact and
    deg P≤j−r+1≤j−1.
This is also valid when w was changed by an element of U.

For Q=x and then Q=x(x−u), set z_Q=(QP)(c)−Q(C)w. This is a genuine lift of nonzero QP through grade j+deg Q≤2j; separation through 2j says z_Q is not in U. Pick the first chronology prefix not matching U, and a matching h∈U on the preceding prefix. The mismatch occurs outside S, because U and z_Q vanish on S. Splitting U by c-block isolates a row lambda in the mismatching prefix on a single node xi, outside S, annihilating U but lambda z_Q≠0. On that block z_Q is constant Q(xi)P(xi), so lambda 1≠0 and Q(xi)P(xi)≠0. The row kills every power of the head and all of F_(2j). For any R with deg R≤j−deg Q−1, the stages before this prefix endpoint satisfy R(C)z_Q=R(C)h there; strictness means lambda A sees only those earlier inputs, and AR(C)h∈F_(j+1). The primitive on R(C)z_Q has grade ≤1+deg R+deg Q+j≤2j. Therefore
    ∫_0^xi R(x)Q(x)P(x) dx=0   for ALL deg R≤j−deg Q−1.
The first Q gives u≠0; the second gives v distinct from both zero and u. No ordering of the two scalar knots is used.

## Two-endpoint algebraic lemma

Put m=j−1≥4, rescale x by u, let a=v/u∉{0,1}, and reuse P for the rescaled nonzero polynomial of degree ≤m. The first budget gives
    ∫_0^1 x R P=0 for all deg R≤m−1;
the second gives
    ∫_0^a x(x−1) R P=0 for all deg R≤m−2.
These are formal polynomial primitives, not Lebesgue integrals over K. Fixed rational moment nonsingularity on x dx forces P to lie on the single degree-m Jacobi line. Its Rodrigues identity can be checked without naming a special function: F=x^(m+1)(x−1)^m, and F^(m)/x is deg m and nonzero, orthogonal to every R of deg ≤m−1 by m integrations by parts (lower boundary order m+1, upper order m). Thus xP is a nonzero scalar multiple of F^(m).

The second test says that the functional T(H)=∫_0^a H F^(m) vanishes on the exact codimension-one kernel of evaluation at 1 inside P_(m−1), since H=(x−1)R with deg R≤m−2 is precisely H(1)=0. It follows T(H)=lambda H(1) for some scalar lambda and ALL H∈P_(m−1). Integrate by parts m times, noting F^(k)(0)=0 for 0≤k<m and H^(m)=0. Taking H=(x−a)^k, k=0,…,m−1, obtains
    (−1)^k k! F^(m−1−k)(a) = lambda (1−a)^k.
Equivalently, the 0th through (m−1)th derivatives of F at a are those of lambda(x−1)^(m−1)/(m−1)!. Division by (x−1)^(m−1) is legitimate in the jets at a≠1, so x^(m+1)(x−1) agrees there with a constant through derivative order m−1. Its first and second derivatives must both vanish (already for m≥3). Its first derivative is x^m[(m+2)x−(m+1)], whose only nonzero root is simple in characteristic zero. This contradiction rules out the assumed noninvariant endpoint.

## Conclude

Thus a flat band ending at 2j has C-invariant F_(2j). In that case its surplus f_(2j)−2j is ≥j−3 by the invariant chronological completion bound. Otherwise the nondecreasing integer surplus f_k−k increases by at least one across the band. Starting at j=5 with surplus ≥0 and doubling, f_q−q≥h. Substitution in the first inequality gives the stated theorem.

This repair does not assert that every freely varying two-endpoint moment problem is field independent: with only three first and two second moment tests and an unrestricted quartic (mismatched degree), the corresponding determinant has two nonreal exceptional ratios. Here the Hermite bound r≥2 and the sharpened degree of P supply exactly the matching number of tests.
