# Early Lobatto branch and the two-head defect flag

Mathematical source proof over every characteristic-zero field. The only tableau is the reviewed, strictly lower triangular actual width-19 `HasOrder 13 A b`, in the marked branch firstSeed=0 with the literal terminal coordinate ℓ already in E7. Write L for the last stage, c=A1, C=diag(c), D_n=U+span(w,Cw,…,C^(n−1)w), e(P)=P(c), and μ_k(P)=(primitive(X^k P))(1). F_j and E_j are the reviewed zero and tree flags. Adopt the marked staircase, paid shift-locality and joint multiplier construction in [the paid marked staircase](PAID-STAIRCASE.md); all quotients and stages below stay in its actual row coordinates. No new unconditional stage bound is claimed.

## 1. Extra mode measured at the physical endpoint

The marked staircase has rank E7=15, because adjoining ℓ adds nothing at an early terminal. Every vector in F5 vanishes at L: its product with ℓ lies in F12 by the original graded product and the order probe kills the resulting scalar times b_L. Hence F6=D_(r+1) and every head band vanish at L.

If rank F7=8, the V7 polynomial range has rank 8. For its injectivity, a polynomial of degree≤6 vanishing on all rows is killed by ordinary next-grade separation. A degree-seven nonzero one would pay its true origin and six F7 moments from the zero column, and `HyperplaneTerminal.seven_paid_not_one` would contradict c_L=1. Equivalently use `coeff_separated_two_endpoints` at n=6,j=7. Since E7=V7+F7, their intersection has dimension one. Normalize its actual degree-seven polynomial J by J(1)=1:

    J = 1716 X^7 − 5544 X^6 + 6930 X^5 − 4200 X^4 + 1260 X^3 − 168 X^2 + 7 X.

That normalization is unique by the weight-X consecutive moment detector. The rational coefficients have μ_0,…,μ_5=0 (checked directly below). Thus, in either marked first-escape fork,

    F7 = D_(r+2) ⊕ K e(J),       F7 ∩ ker(ev_L) = D_(r+2).

This is an actual unmarked polynomial line; the previous smaller-degree marked projection is another coordinate for the same extra mode. If rank F7=7, F7=D_(r+2) and the leakage coefficient is identically zero.

## 2. Root restriction and a common highest-mask term for the cubic ports

Take a grade-three v∉U and its nonzero degree≤3 multiplier profile P earned by the genuine joint clock/v masks; the required band shift geometry is the argument in section 4 of the marked staircase proof and does not assume rank-F7=7 before the physical ports. Mask w to the joint locus M={v=P(c)}, absorbing the change into U. In particular the off-M clock slice of v is in U and every head power vanishes there.

For S=X, and then S=X(X−t₀) at the second port, take the first original prefix on which z=S(c)(e(P)−v) cannot be matched by U; let u₀∈U match it strictly before that row. Such a mismatch is guaranteed even for S=X(X−t₀)(X−t₁): if global matching held, e(SP) would belong to F6, contradicting degree-six separation (nonzero SP and deg SP≤6). Its row i is strictly before L: z−u₀ lies in E6, so if the first failure were at L it would buy a nonzero multiple of ℓ in E6, impossible. At its clock t the off-M fibre cannot be matched through i, by patching with the separate clock/v masks, and S(t)P(t)≠0. In particular each successive t is nonzero and distinct from the previous chosen clock or clocks.

**The original marked mesh G must vanish at every such t.** In the actual identity e(G)=a+Q(c)w+γℓ with a∈U, the head vanishes on the off-M slice, and the literal mark vanishes on the entire prefix through i. Were G(t)≠0, the masked a would supply a nonzero constant on that slice through i. After scaling by S(t)P(t) and subtracting the known off-M v slice, this would pay a match to z there, contradicting the chosen pivot. This argument does not require the pivot itself to be outside the support of U, nor does it conflate ℓ with a clock-one fibre.

For a mask T with R=TS of degree≤3, the native transported defect is

    Z_R = e(primitive(RP)) − A[T(c)(z−u₀)]
        = e(primitive(RP)) − A e(RP) + A[R(c)v] + A[T(c)u₀] ∈ F7.

Because U is clock stable and paid in F5, the last summand lies in F6 and vanishes at L. Thus ev_L(Z_R) is a common linear functional of the polynomial R, independent of the prefix matching choice u₀ and of the split R=TS. This functional vanishes if deg R≤2: the primitive defect and A[R(c)v] then lie in F6 as well. In rank eight, let κ be its value on X³. Subtract κ·R.coeff(3)·e(J) from Z_R to get an actual vector in D_(r+2). Strict causality shows that Z_R on the clock-t off-M portion through the original pivot row equals the primitive value; the head-subtracted result there is a U vector. If its scalar value were nonzero, it would pay a rescaled match to z, as above. Consequently the true physical port is

    (primitive(RP))(t) = κ · R.coeff(3) · J(t).

The same statement holds with κ=0 in rank seven. Thus there is one shared scalar, not a fresh leakage for each test, and the lower-degree tests have no leakage. No higher-order operator payment was used.

With I_k(x)=(primitive(X^k P))(x) and the first two clock values t,u, the first/second test pairs give these five equations at a genuine distinct nonzero mesh-root pair:

    I_1(t) = 0,                 I_2(t) = 0,
    I_3(t) − κ J(t) = 0,
    I_2(u) − t I_1(u) = 0,       I_3(u) − t I_2(u) − κ J(u) = 0.

## 3. Exact degree-six Lobatto branch: cubic profile cannot survive

Write F(X)=132 X^5−330 X^4+300 X^3−120 X^2+20 X−1 and G_L=X F. In the a=5 fork the actual degree-six G is a nonzero multiple of G_L. This follows because G(0)=0, the five adjacent moment differences are zero, and X(1−X) times G(X)/X is tested against degrees 0 through 4. The rational weight-X(1−X) moment form of order five is nonsingular over characteristic zero (its rational matrix is positive definite over ℝ, hence its determinant survives scalar extension). The listed polynomial G_L has G_L(1)=1 and μ_k(G_L)=1/42 for all k=0,…,5. Consequently the actual last output weight is b_L=1/42. Every nonzero pivot root of G is a root of F.

The five displayed equations are linear in the four coefficients P_0…P_3 and κ. Row I_k(t) has entries t^(i+k+1)/(i+k+1), i=0,…,3. The two higher rows have respectively −J(t),−J(u) in the last column. All denominators are units in ℤ_(43). Over 𝔽_43, F splits into the five distinct roots [2,9,22,35,42]. At the 20 ordered distinct pairs in lexicographic order, the 5×5 determinant residues are

    2,11,36,17, 33,25,25,14, 2,5,23,18, 26,5,17,31, 3,14,17,37.

They are nonzero universally, not just for specified real root evaluations: over R=ℤ_(43) divide F by its unit leading coefficient, adjoin its first root t, and adjoin u using the monic divided difference (F(u)−F(t))/(u−t) normalized likewise. This is finite free of rank 5·4 over R by the two monic quotient presentations. Modulo 43 it is exactly the product of the 20 fields for ordered distinct roots. Multiplication by the determinant is invertible modulo 43, hence invertible over R by the determinant/unit criterion for finite free modules. It remains invertible over any characteristic-zero field when specialized to a distinct root pair. This contradicts P≠0.

Therefore F3⊆U in **both** F7 ranks in a=5. For r≥3 the construction above and scalar obstruction prove it; for r=2 the original paid C² argument puts F3 in U because four head powers are independent modulo U and v,C²v∈F5=D2. Since rank F3≥2, r≤3. Moreover rank F4=4. If r=3 then F3=U and outgoing clock Hermite costs two, giving rank F4≥4. If r=2 and rank F4=3, strict separation forces rank F3=2; F3 cannot be C-stable as that would cost two in the next flag. Thus F4=F3+C F3⊆U and dimension equality makes F4 invariant, contradicting the incoming two-dimensional clock cost from F3. The upper bound rank F4≤4 is strict growth before F5.

## 4. Another exact scalar gate: one primitive kills every pure Lobatto factor

If G_L=R Q up to nonzero leading scalar, and t≠0 with Q(t)=0 and R(t)≠0, then (primitive(XR))(t)≠0. Normalize R to monic and pass to an extension where its roots split. Modulo 181 the distinct roots of F are [52,81,91,101,130]; G_L adds the root 0. For every t in this five-element nonzero set, the primitive is nonzero for every subset of the other five roots used as the monic factors of R, including the optional root 0. The exact integer modular check covers all 160 subsets/target pairs (no floating approximation). For the lift, build the finite free ordered splitting algebra of the monic normalization of F over ℤ_(181) by adjoining one root and then the next root of each successively divided monic polynomial. Its reduction is the product over all 5! permutations of the five distinct roots. Take the first formal root as t, the chosen degree-specific subset of subsequent roots, and include X or not as required. The same multiplication-unit argument gives the scalar gate over every characteristic-zero extension. The factor R can never contain t because all these roots are simple; both cases R(0)=0 and R(0)≠0 are covered.

For any earned clean F4 head w with a pure factor R(c) on its support and G=RQ, deg R≤4, this one scalar gate is physically available **without using F7**. Choose the live U indicator e and let z=e(XR)−Cw−(XR)(c)e. If z=0, e(XR) would belong to F5, contradicting degree-five separation for the nonzero polynomial XR. Its first nonzero row is before L, since z∈E5 and ℓ∉E6, and it is off the core and head. There t≠0, R(t)≠0, Q(t)=0 by the mesh identity, and causality plus the primitive defect and grade-five input puts the primitive at t in the zero off-band trace of actual F6. This is precisely (primitive(XR))(t)=0, contradicting the scalar gate.

## 5. Consequences for the entire a=5 r=3 family and a=5 r=2 except its top branch

The flat interval F4–F6 identifies its invariant core with U by chain drop through the unpaid F5 power. It gives w∈F4 (and Cw∈F4 if r=3). Use literal one-clock locality at F7 or F8 to assemble U² and U·w into U (F3·F4 when r=3, F4·F4 when r=2), then the reviewed disjoint representative. Every band is preserved and the terminal remains zero on U,w.

**Radius 3 is excluded in a=5.** The three shifts of w² are in F8 since w,Cw∈F4, so marked adjacent-shift purity gives w²∈D6. Its first shift is in D7 and remains in F8; the a=5 refund gives Cw²∈D6. Thus the paid multiplier profile on the clean head has degree at most 4. The mesh head multiplier is at most degree 4 from G∈D5+Kℓ. Marked E9→E10 pays at least nine head clocks, since its lower a=5 head length is eight and C V5 and Cℓ already advance inside that chart. Therefore exact degree≤8 interpolation gives G=RQ. The preceding first-X gate excludes it.

**Radius 2 conditional reduction in a=5.** The true w²∈F8 has actual chart e(P)+R(c)w+u+αℓ, deg P≤5, deg R≤5, P(0)=0. The head D6 is paid in F9, so μ_0(P),…,μ_3(P) are equal; the last-row evaluation gives α=−P(1). The mesh Q has deg≤3. On the disjoint head, multiply the mesh by w and substitute the square to obtain

    e(G−RQ)w − e(PQ) ∈ U+Kℓ .

If deg(G−RQ)≤7, the E10 chart D8+V5+Kℓ and division by G of degree 6 show G|PQ: the quotient has deg≤2 with polynomial evaluation in D6+Kℓ, and a degree≤5 remainder in D8+Kℓ must vanish by directness. Write P=X V. The three paid weight-X(1−X) tests put V in the span of monic H3,H4. With H5=F/132 there is the exact recurrence

    H5 = (X−1/2) H4 − (2/33) H3.

Use H3=X³−3X²/2+9X/14−1/14 and H4=X⁴−2X³+4X²/3−X/3+1/42. Their rational moments and recurrence are checked by the small script below; H4 is nonzero at all F roots via mod43 and the same monic quotient argument. Hence at five distinct H5 roots the values of V, divided by H4, are one affine polynomial. Unless P=0 at most one can vanish. The low-degree Q cannot cover the other four roots in G|PQ. Thus P=0, so α=0; one-slot refund gives w²∈D5, the clean amplitude has deg≤4, and at least eight physical head clocks identify G=RQ by a degree≤7 comparison. The first-X gate rules it out.

Separately, if there are no more than nine physical nonzero-head clocks, the nine F4 probes make each clock sum of b w zero. On Q(t)≠0, w² has the same clock-weight factor G(t)/Q(t) times w (w=0 rows contribute zero); the remaining support of clock sums of b w² lies on at most three Q roots. The five F8 probes kill these sums as well. Q cannot be identically zero here, because that would put every preterminal noncore clock on the six roots of G, contradicting the eight-clock lower count. Core sums vanish by clock masking. The square identity now gives P(t)=0 at every off-one clock whose ordinary aggregate b mass is nonzero. There are at least six such clocks by the nonsingular weight-(1−X) moment matrix (if at most five, test its nodal polynomial against powers 0,…,5 at literal order budget). Thus P=0, and the same refund/factor/first-X gate excludes it.

The **only a=5 r=2 branch left by these arguments** has more than nine head clocks and both deg R=5 and deg Q=3, so deg(G−RQ)=8. The transport pays the next head power, making E10 clock-stable. With its clean square and ℓ it is a unital 18-class original algebra: 3 core atoms, 14 noncore preterminal pairs, and the singleton terminal L. The two equations for the 14 pairs have eliminant (G−RQ)G−PQ² of degree 14, so exact saturation applies; for E9 the observer h(c)+s(c)w has deg h≤5 and deg s≤6, and hQ+sG has deg≤12. The generic no-singleton selector proof therefore gives full E9 hyperplane support on the 14 noncore preterminal classes (zero at core and L). Exact original E10 annihilation has the sole contrast ρ1; its P-row value at the physical penultimate P is −b_P(1−c_P)²≠0. Thus the unique duplicate pair includes P as its later row. The final-three causal theorem closes this seam; see [Final three classes](FINAL-THREE.md). The ordinary reflected-zero selector route does not apply because L is in E7 and its hyperplane coordinate is zero.

In that seam, write β for the sum of actual weights on each of the 18 classes and λ for the E9 annihilator on class functions. The exact E8 annihilator on these functions is span{λ,cλ}: it has dimension two by the measured rank, and cλ is paid by C E8⊂E9; the two rows are independent because λ is nonzero at many distinct head clocks. The true F4×E8 product and the degree-zero probe give βw in this two-plane. The class of the true origin is (c,w)=(0,0), is noncore, and has λ≠0, so the constant coefficient vanishes and βw=κ cλ. If κ=0, every head class mass is zero, and the at most four preterminal clean classes cannot supply the six off-one quadrature-active clocks. Thus κ≠0. The origin class is then the only zero-head noncore class; there are exactly 13 head classes and each with nonzero clock has nonzero β. At most one head class can be at clock zero, by the quadratic. Such a class agrees with origin through E3. Accordingly, before the first nonzero head clock, the optional zero head can be coalesced with origin; the new head row is an exact native order-three receiver (F3 vanishes there), so it requires at least three predecessor classes, including at least two core representatives. This last observation does not force an order-four receiver.

## 6. The exact two-head higher defect flag in either early rank-eight fork

If rank F7=8, the paid second head J actually propagates as an independent clock band:

    F_(7+m) = D_(r+2+m) ⊕ span{e(J), C e(J), …, C^m e(J)},    m=0,1,2,3.

To see the upper bound, project the marked early chart E_(7+m)=V_a⊕D_(r+8+m−a)⊕Kℓ to degree≤a polynomials. For actual F_(7+m) this projection has origin zero. The longer head is paid in F_(13+m−a) and the probe window gives equal μ through k=a−1−m; their a−1−m differences are independent on the a free positive-degree coefficients, by the same weight-X(1−X) detector on the smaller coefficient band. The projection rank is at most m+1. The kernel is exactly D_(r+2+m): the mark is excluded by the mass probe at the paid head grade (≤12 within this range), and a=5 then uses its one-slot refund. In particular the correct bound on defect rank is 7+m+(m+1).

The projected columns e(X^k J), 0≤k≤m, are the ordinary Euclidean remainders modulo G. Indeed X^k J has degree 7+k and the quotient has degree at most 6+k−a; multiply the native mesh identity by that quotient and its entire head/mark evaluation fits D_(r+8+m−a)+Kℓ. Now J/X and F are coprime over every characteristic-zero field: modulo 43, J/X on the five F roots has respective values [2,10,40,10,2], so it is a unit in the same monic finite-free quotient. In a=5, G/X is F up to scale; in a=6, G/X=a(J/X)+bF with the nonzero b just derived. Hence G/X and J/X are coprime in both forks. Any vanishing linear combination of the remainders would make G divide S J for deg S≤m≤3; cancelling X and coprimality would make G/X of degree at least five divide S. This proves independence and the exact flag.

This pays a concrete two-head advance on the *ordinary actual defect columns* in the early branch (rank F7,F8,F9,F10 = 8,10,12,14), not merely an extra dimension in a marked polynomial chart. It does not remove the second head.

## Evidence

[The exact Lobatto certificate](certificates/early_a5_certificate.py) regenerates the displayed rational moments, recurrence, modulo-43 determinants, and modulo-181 factor gates with exact integers and fractions. Run it with standard Python 3, no dependencies. The finite-free specialization argument in this proof is what makes the checks uniform over characteristic-zero fields. This is not a Lean verification. Neither late marked geometry, a legacy ghost packet, nor a real/positive tableau assumption is used.
