# The signed, eight-stage strict SDIRK7 midpoint

**New necessary restrictions:** a rational eight-stage strict SDIRK method of order at least seven must have **all eight weights nonzero, with exactly two negatives**. In particular, a rational strict method with a zero weight or at most one negative weight needs at least nine physical stages. This excludes the entire zero-weight rational subclass, including repeated nodes and internal spectators. It does **not** improve the unconditional eight-stage floor: the six-positive/two-negative rational class is still open. The sign census is for any ordered field, allows zero weights and repeated nodes, and applies even to arbitrary nonzero (not necessarily equal) diagonals. The causal restrictions below requiring a common diagonal say so explicitly.

## Midpoint rank and ordered signatures

Write E_j for the reviewed stage tree space through grade j, F_j for the zero-profile differences, C for multiplication by the physical clock c=A1, and B for multiplication by b. Let U=ker B, m=dim U, d=dim(F_3 intersect U). At eight stages, the paid Volterra recurrence is tight, with dim E_j=(1,2,4,6,7,8,8) and dim F_3=2. In particular E_3 intersect U=F_3 intersect U: remove the pure part of a vector and test the remaining cubic coefficients against 1,c,c²,c³ by the paid Hilbert matrix. For x in F_3 and y in E_3, the paid pairing of xy is zero. Thus B F_3 lies in the ordinary annihilator of E_3+U. Its rank is 2-d, while that annihilator has rank 2-m+d. Hence **m≤2d** over every field in the native order contract. In the strict common-diagonal case the first two coordinates detect every vector of F_3 (the initial seed and its first strict advance give the triangular pivots). Thus if there is any ghost it cannot start after the first two stages; three or more ghosts force both head stages ghost and every cubic defect hidden. Four is the maximum number of ghosts.

For an ordered field the weighted square form on E_3 is nonnegative, since modulo F_3 it is the uniform cubic Gram whose rational sum-of-squares expansion uses the first four shifted Legendre polynomials with norms 1,1/3,1/5,1/7. On F_3 the square form vanishes. Intersect E_3 with the coordinate space on b≤0, or F_3 with the coordinate space on b≥0. In both cases the intersection has dimension d: a paid zero sum with terms of one sign forces all active entries to vanish. The two dimension inequalities give, writing n for the number of strictly negative weights,

    2 - d ≤ n ≤ 2 + d - m.

In particular no ghosts forces exactly two negatives; three ghosts allow at most one negative; four ghosts force all four active weights positive. Two ghosts and d=1 force exactly one negative. No sign hypothesis enters the abstract ghost bound or the following rational exclusion.

## No zero-weight chart over the rationals

Use the actual quadratic seed g=2Ac-c² and the nonzero common diagonal γ.

1. If m>0 the weighted image of F_3 has rank at most one. If B g is nonzero, the visible weighted defects B g and B Cg are proportional, so all active coordinates with a nonzero g have the same clock. At the other end, exact D(1) and the saturated scalar/Volterra frame force nonzero last two weights and distinct last two clocks, and c_s=1−γ. Both B g and the weighted reflected quadratic defect annihilate E_4, whose codimension is one. The reflected row at the final index is b_s γ², and at the penultimate index it is b_{s-1}(γ²+2γD−D²) with D=c_s−c_{s-1}. This entails g_s≠0 when B g≠0, and γ² g_{s-1}=(γ²+2γD−D²)g_s. Therefore the single visible dirty clock would have to be c_s; the penultimate stage is clean and (D/γ−1)²=2. Over a field without sqrt(2) this is impossible. So B g=0.
2. The front seed/tap relation is γ²(C−γI)g=g_2(A−γI)g, where g_2=γ²+2γa_21−a_21² (one-based stage numbers in the prose). If sqrt(2) is absent g_2≠0. Thus the strict advance of g is also ghost-supported and, with g, spans F_3. This step handles repeated dirty clocks; it does not assume all contributing sites distinct at the raw-stage level.
3. At least five distinct active clocks, and complete hiding of F_3, make C F_3 stay in F_3. Indeed dim F_4=4, and two independent visible vectors come from the degree-three and degree-four shifted Legendre polynomials. Their affine combination cannot vanish on five distinct active clocks. Hence F_4 intersect U has dimension at most two, so equals the hidden F_3 and contains C F_3. The first three chronological clocks are distinct: [A,R]1=0 for R=CA−AC−A² forces an arithmetic progression if the third row's middle tap is nonzero, and equality at a zero tap would duplicate a prior stage in every genuine tree. Evaluate (C−c_1)(C−c_2)f for f in F_3: it stays in F_3 and has both head coordinates zero, so must vanish. Thus every cubic defect vanishes at stage 3. The native proof works over characteristic-zero fields, irrespective of the third weight or other clock collisions.
4. A truly cubic-clean third stage has normalized clock y=c_3/γ satisfying y³−9y²+18y−6=0, by the literal row sum, two monomial primitive defects, and the advance of g. The homogenized cubic has no projective root mod 5; hence no rational root. The grouped native prime-5 support theorem supplies the five active clocks for every rational order-seven rule (multiple stages at one clock are aggregated, and a canceled aggregate is not counted).

## Independent projective mod-19 support check

Any degree-six exact uniform quadrature with at most four rational active clock values is impossible, independent of the weights' signs and whether the weights are rational. Pad the clocks to four by repetition if needed. Its monic annihilator H(X) consists of four linear factors and satisfies the three orthogonality tests with 1,X,X², so 70H=L_4+λL_3 for the shifted Legendre pair, with λ rational.

Write λ=b/a in relatively prime integral coordinates, and every clock x_i=n_i/d_i with relatively prime integers and positive d_i. Compare the two integral polynomials

    P=a L_4 + b L_3,   V=product_i (d_i X - n_i).

They are rationally proportional. Neither reduces to zero mod 19: the first two leading tests (degrees 4 and 3) ensure independent L_4,L_3 in the residue field, and no primitive linear factor reduces to zero. If the proportionality scalar is u/v in lowest terms, then uV=vP integrally. One of u,v cannot vanish mod 19 without the other also vanishing, so both are units mod 19. Thus the residue pencil would have to split. A vanishing d_i modulo 19 gives a nonzero constant in the univariate reduction and exactly one factor Y in the homogeneous reduction: these are projective roots at infinity and may not be silently removed from the degree-four argument. Likewise the a=0 pencil direction has degree three in the univariate reduction and exactly one projective infinity. Every direction (1:t) has degree 4 and at most two finite roots, all simple; (0:1) has degree 3 and only one finite root, simple. Therefore none splits. This is an independent check of the existing grouped five-clock conclusion, not itself a new support floor.

## Read/replay

The native entry points are:

- RKResearch.Certified.Graded.SDIRKSeven.signed_ghost_census
- RKResearch.Certified.Graded.SDIRKSeven.cubic_hidden_of_ghost_no_sqrt_two
- RKResearch.Certified.Graded.SDIRKSeven.third_pure_of_hidden_five_clocks
- RKResearch.Certified.Graded.SDIRKSeven.rational_support_signature
- RKResearch.Certified.Graded.SDIRKSeven.rational_stage_floor_of_ghost and rational_stage_floor_of_at_most_one_negative
- RKResearch.Certified.RationalFourClock.rational_four_factor_pencil_impossible (independent pencil obstruction)

The development uses the reviewed HasOrder predicate directly and no fixed nonlinear tableau chart. Compile the four Research modules in dependency order, signs, terminal, ghost exclusion, and the independent four-clock certificate. Run python3 check-arithmetic.py for a standard-library-only independent replay of the numerical identities and projective field checks.
