# Closing the characteristic-283 order-12 pure quartic branch

**Scope.** This excludes the characteristic-283 *pure rank-two quartic omitted-root chart* of the published order-12, 17-stage proof, including coefficients in arbitrary extensions of the prime field. It does not claim that every other characteristic-283 chart, or every other prime in the order-12 endpoint proof, has been audited. No tableau search, Lean run, or repository modification was performed.

Let K be a field of characteristic 283, A a strictly lower matrix on 17 rows, b an order-12 output. In this branch the saturated chart has an invariant coordinatewise core U of dimension 3, a head w in F4, and a degree-four polynomial P with P(0)≠0. Here F_j is the space of numerical pure defects in the ordinary rooted pairs through degree j (tree order j+1). Let T be the core support, S the head support after subtracting the core. They are disjoint and w=P(c) on S. We use the chart relations
  F4=U+Kw, F5=U+w P_1(c), F6=U+w P_2(c),
  E7=P_6(c) ⊕ (U+w P_3(c)), E10=P_6(c) ⊕ (U+w P_6(c))=K^17,
where P_j(c) means polynomial evaluations of degree at most j. The polynomial component of F7 in E7 lies on the line spanned by H7=x(462x^5−1260x^4+1260x^3−560x^2+105x−6): indeed the component vanishes at 0 and is orthogonal to all degrees ≤4, so the shifted paid Hankel gives the unique degree-six line. These are the pure branch hypotheses of ../proof-dependencies/pass0045_q6_even.md and the OrderTwelvePureRankTwo/RankTwoClosure modules in source commit c1d29976a37f7f264f7123bf0cd69a8126a107b3. They are not inferred solely from the scalar gate.

The terminal coordinate e_17 lies in E6, represented by xD5 and an F6 defect, where
  D5=132x^5−330x^4+300x^3−120x^2+20x−1.
Its clock is 1; F6 vanishes there and at every row outside S∪T. At any nonterminal off row its clock is 0 or a root of D5. The pure-case factorization is P∣D5; rescale the head to make P=D5/(x−u) for the sole omitted root u. This rescaling preserves the chart.

## 1. Exact residue data and physical support

Each class of the coordinatewise algebra U has a support indicator in U. This follows by interpolating a polynomial vanishing at zero on the distinct values of one vector at a time, then intersecting their value classes, and taking unions by e+f−ef. Because U is C-invariant, all coordinates in one class have the same clock. In the complete E10 chart they also have the same U and head values; therefore each class is a single physical row. There are exactly three mask rows, and b vanishes at each because its indicator belongs to F4. The same E10 chart shows that any clock occurs at most once on S, and at most once off S∪T. The first row is the off coordinate at clock zero; the last is the off coordinate at clock one.

For a scalar mask M define the supported contrast
  z_M=(MP)(c)(1−e_T)−M(C)w,
where e_T is the core support indicator. It has profile MP, and is zero on S∪T. Its degree is at most 4+deg M whenever used below, because w∈F4 and the core is invariant. For z=z_x, separation and the exact terminal polynomial degree 6 force a nonterminal off row of clock u: otherwise z would be a nonzero multiple of e_17 with polynomial degree 5. Its uniqueness was just shown. Thus z is supported exactly on that off row i and the terminal row. Strictness makes Az zero up to and including i. The rooted profile of Az is J(xP), degree 6, and its F6 deviation vanishes at i, so J(xP)(u)=0.

The normalized residues from this last equation are exhaustive even over extensions. Over F283 the gcd of D5 and the reduced moment numerator 1650x^4−3060x^3+1860x^2−413x+25 is x²−x+190=(x−106)(x−178). The two cases and their synthetic quotients, ascending coefficients, are:
  u=106: P=[275,224,78,78,132], (J(xP))/x²=[279,169,161,242,22], H7(u)=177.
  u=178: P=[221,273,255,243,132], (J(xP))/x²=[252,91,276,275,22], H7(u)=105.
For both u values, gcd(P,(J(xP))/x²)=1. Thus any earlier nonterminal off row other than the origin would have a nonzero P-root as its clock, but the zero numerical Az and exact F6 profile there would force that root to annul J(xP), impossible. Therefore every row before i is either the origin, a head, or a mask. The row at i is exact for every rooted pair through F6, so its incoming row realizes an order-six method on its own strict prefix after rescaling by u. The paid generic order-six stage floor is seven. Thus i≥8 and there are at least three preceding heads.

All three masks precede i. Otherwise the last mask t would be later than at least two earlier heads (there are at least three before i). Its column A e_t belongs to F5=U+wP_1. The affine head polynomial vanishes at those two distinct earlier head labels by strictness, hence vanishes identically. No later mask is available, and the column is zero at every off row. Therefore A e_t=0, and b_t=0 was shown above. Deleting this row and column preserves the full rooted equations by induction on trees, but order 12 needs at least 17 stages over this field by the paid fifth-degree surplus. This is a contradiction. In fact the last mask must precede the second head.

## 2. The first three active head positions cannot suffice

Write ℓ=e_i^T A. It is supported on the origin and earlier head rows, because it kills each mask indicator (A U⊂F5, whose vectors are zero at i). Let h be the number of head rows up to and including its last nonzero head entry, counting all intervening head rows. A nonzero head entry is necessary from ℓ c=u²/2. Truncating the exact order-six prefix at the last nonzero entry of ℓ preserves all its order conditions; therefore h≥3 (at most three masks and one origin can precede or accompany the h heads). Let their clocks be η_1,...,η_h in chronological order.

Suppose h=3. Since z_1 has profile P and is supported off S∪T, A z_1 at i sees only the origin and equals J P(u). Thus the origin coefficient of ℓ is J P(u)/P(0). The exact scalar moments up to degree five of this incoming row give a quadrature on the origin and the first three heads. Scale x by u and put γ=J P(u)/(uP(0)). The monic cubic N whose roots are η_j/u must satisfy
  ∫_0^1 x N=∫_0^1 x² N=0,  ∫_0^1 N=γ N(0).
The first conditions give the monic pencil N=S3+t S2, where S2=x²−6x/5+3/10 and S3=x³−12x²/7+6x/7−4/35. In the third condition the coefficient of t is 1/30−3γ/10; it is nonzero in both cases. For u=106, γ=67,t=254 and N=[68,68,131,1]. For u=178, γ=24,t=96 and N=[247,201,256,1]. Both cubics are irreducible over F283. The arithmetic checks below include the Frobenius reductions, so no brute-force chart search is needed. In particular all three clocks are nonzero and the unscaled cubic also is irreducible.

Consider the first three actual head rows. For each mask t, A e_t lies in U+wP_1, so its coefficient on these heads, divided by P(η_j), is affine in the head clock. For k=1,2,3 the column A c^k−c^(k+1)/(k+1) lies in F_(k+1); its head value after division by P is zero for k=1,2 and constant for k=3. Here F3⊂U follows also directly: for v∈F3, both v and C²v lie in F5=U+wP_1, and equality of x² times its degree≤1 head polynomial with another degree≤1 polynomial on the ≥7 effective head clocks forces the head part to vanish. The origin's contribution to c^k is zero, and there is no earlier nonzero off clock. Hence the second divided difference on the first three head clocks removes all mask contributions and all these head corrections. It leaves
  ∑_(j=1,2) r_j η_j^k = a_k   (k=1,2,3),
  a_k = [∑_(j=1..3) η_j^(k+1)/(P(η_j)∏_(l≠j)(η_j−η_l))]/(k+1)
for some two coefficients r_j independent of k. The only head inputs to those rows lie among the first two, by literal strict chronology. The values a_k lie in the prime field: the sums are symmetric rational expressions in the roots of the fixed unscaled cubic, with nonzero denominators (equivalently the sums are traces from its root algebra). Let s1,s2 be the first two elementary symmetric coefficients of that cubic. A sequence of two exponential sites necessarily has a_3−(η_1+η_2)a_2+η_1η_2 a_1=0. As η_3=z, this says
  a_3−(s1−z)a_2+(s2−s1 z+z²)a_1=0.
This is a nonzero polynomial of degree ≤2: a_1,a_2,a_3 cannot all vanish because the three nonzero distinct η_j give an invertible Vandermonde on the powers 2,3,4 with nonzero coefficients 1/(P(η_j)∏ differences). It cannot vanish at a root of the irreducible cubic over the prime field, even after extension. Thus h=3 is excluded.

## 3. Four earlier heads force a new head after i at the same clock

There are now at least four head clocks before i. The formal scalar commutator xJ−Jx equals J². Consequently
  d=(CA−AC−A²)z
is a degree-seven pure defect. It is zero through row i by strictness. Its F7 polynomial coefficient must vanish because its component at i is a multiple of H7(u)≠0; the core and head both vanish there. Thus d∈U+wP_3. All masks precede i, so its core part is zero. Its degree≤3 head polynomial vanishes at four distinct earlier head clocks; hence d=0. Now (C−u)z is supported only at the terminal row, so A(C−u)z=0. Setting g=Az yields the actual identity
  A g=(C−u)g.
The column g is not zero, as shown below. Its first nonzero row j follows i and has clock u by strictness and that identity. It cannot be an off row or a mask: the off label u already occurs once, and every mask is earlier. Hence there is a head of clock u strictly after i.

## 4. The weighted marked suffix needs seven physical rows

Let f=xP. For each polynomial R of degree ≤5, the fixed orthogonality of D5 gives
  ∫_0^1 (1−x) f(x) R(x) dx = a R(u),   a=∫_0^1 (1−x)f(x) dx≠0.
Indeed R−R(u) is divisible by x−u with quotient degree ≤4. If a were zero, P would be orthogonal to every polynomial of degree ≤4 under x(1−x); the paid shifted Hankel is invertible there. The ordinary b test gives b g=a, so g≠0.

For a word W in J and multiplication by x of length ≤5, formal polynomial interchange of the two integration limits gives
  ∫_0^1 W(J,x) Jf = ∫_0^1 f(t) K_W(t) dt,
  K_W(t)=∫_t^1 W(J_t,x)1 dx,   J_t v(x)=∫_t^x v(y)dy.
This follows by induction on the word, using primitive evaluations over the integration simplex. The polynomial K_W vanishes at t=1 and has degree at most length(W)+1 in t, so the preceding cardinal formula gives a K_W(u)/(1−u). All word tests are paid: g has degree 6 and the word has length at most 5. Restrict to rows from the first nonzero g entry j onward; all words starting from g stay zero before j. Normalize the operators N=A/(1−u), Y=(C−u I)/(1−u) on this suffix and the row L=b/a there. Changing variables from [u,1] to [0,1] gives L W(N,Y)g=∫_0^1 W(J,x)1 for every such word. The first of these physical coordinates has Y=0 and g≠0.

For clarity, this is a seven-stage lower bound for a *one-input word system*, not an unproved assertion that it is a full order-six RK method. Its word pair space through degree three has a unique polynomial component: a zero numerical relation with polynomial P has P(0)=0 by the first coordinate. The three tests with Y^k, k=0,1,2, give the nonsingular shifted Hankel for P/x of degree ≤2. Its pure defect space at degree two contains 2NYg−Y²g, which is nonzero. Indeed if it were zero, putting v=Yg and multiplying by the diagonal partial inverse for Y gives v=2Y†Nv; the right-hand operator is strictly triangular and nilpotent, contradicting Lv=1/2. If the grade-two and grade-three defect spaces were equal, that common space would be invariant under Y,N and its diagonal partial inverse; the same argument in the quotient puts Yg inside it, again contradictory. Thus degree-three pure defects have dimension ≥2, and the four independent scalar monomials give numerical degree-three rank ≥6.

The row R=2L(I−Y)N−L(I−Y)² annihilates this rank-six space by formal integration by parts, with word budget three plus two. It is nonzero by the same strict nilpotent argument on rows: if 2vN−v(I−Y)=0 for v=L(I−Y), then v=2vN(I−Y)† forces v=0 despite vg=1/2. Therefore the suffix has at least seven physical rows. In particular i≤10. Since precisely three masks and the off origin precede i, at most five physical heads precede it, and h≤5.

## 5. The second receiver tap forces an earlier head at the same clock

Let m=ℓ A=e_i^T A² for the literal incoming row ℓ. Both kill U because AU⊂F5 and A²U⊂F6, which vanish at i. The origin coefficients are related by m_1=uℓ_1: applying A and A² to z_1 before/at i reads only the off origin, and J²P(u)=uJP(u)−J(xP)(u)=uJP(u). The exact scalar rooted pairs through degree six imply
  ℓ c^k=u^(k+1)/(k+1) (0≤k≤5),
  m c^k=u^(k+2)/[(k+1)(k+2)] (0≤k≤4).
Thus m−ℓ(u I−C) annihilates the powers c^k for k=0,...,4, and its support is confined to the first h head rows: mask and origin entries are zero, and m is strictly supported before the last nonzero entry of ℓ. The h≤5 head clocks are distinct, so Vandermonde gives m=ℓ(u I−C). At the last nonzero head entry of ℓ, the row m is zero by chronology, forcing that head clock to equal u. This head is before i, contradicting the unique head clock u forced after i in section 3. The F283 pure quartic branch is excluded in every extension field.

## Short exact arithmetic replay data

The monic Euclidean remainders (including the normalized second input, lists ascending) for gcd(D5,60R_at_root), where 60R_at_root=[25,−413,1860,−3060,1650], are:
  [253,156,32,276,1]; [237,83,106,1]; [190,282,1].
For gcd(P,J(xP)/x²), the monic remainder lists are:
  u=106: [77,72,226,11,1]; [28,174,144,1]; [96,142,1]; [53,1]; [1].
  u=178: [243,17,64,154,1]; [157,72,214,1]; [263,11,1]; [78,1]; [1].
For the two scaled cubics, x^283 mod N is [107,44,30] and [132,63,43]. The monic Euclidean remainder lists for gcd(N,x^283−x) are respectively
  [13,275,1]; [15,1]; [1], and [240,87,1]; [277,1]; [1].
A cubic with no root in F283 is irreducible. These are literal finite-field polynomial calculations, not assertions about solution fields of an unreduced RK system.
