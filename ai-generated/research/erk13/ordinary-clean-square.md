# The ordinary order-13 clean-square projection on the original 19 rows

Proof note, 25 November 2026. This is a conditional mathematical result. The three-row obstruction is checked in Lean, but the complete argument below has not yet been formalized.

**Conditional theorem.** Let K be a characteristic-zero field, A a strictly lower triangular 19-row tableau, b its actual weights, and let the reviewed `HasOrder 13 A b` hold. Assume the ordinary branch `firstSeed A b ≠ 0`. Use its native `OrdinaryStaircase A b G r U w₀`. Assume **r=2 and dim(zeroSpace A 4)=4**. A representative w of the same head can be chosen in the *actual* grade-four defect space, zero wherever U is live. Its square is in the five-term head band B₅ (so its polynomial projection in E₈ is zero, in particular its degree-six coefficient is zero). There are literal polynomials R,Q with deg R=4, deg Q=3, G=RQ, and wᵢ=R(cᵢ) at every original row with wᵢ≠0. This does not assume eight head clocks, nonzero R(0), positivity, or all individual/output weights nonzero.

Notation: c=A1, C=diag(c), Fⱼ=zeroSpace A j, Eⱼ=treeSpace A j, Bₙ=U+span{w,Cw,…,Cⁿ⁻¹w}. e(H)=H(c), and μₖ(H)=(primitive(XᵏH))(1). All ranks are over K. The source interfaces used below are the native GradedDefects, GradedProducts, GradedPrimitives, NativeFlatClockHead, NativeClockChainPeel, ClockHeadFibers/Support, NativePrimitiveMoments, ReverseFlag, and the ordinary staircase. See [the native order-13 staircase](../../lean/RKCert/ReviewedNative/ERK13NativeOrdinaryStaircase.lean).

## 1. Earning the clean head and the square chart

1. In the ordinary staircase, dim F₅=5, dim F₆=6, dim U=3. Apply `flat_clock_head` to the interval (j,d)=(4,2), using dim F₄=4 and ordinary polynomial separation at grade 6. Its maximal invariant core U′ is U. Indeed, F₅ is the next chain from F₄ and F₆ strictly extends it by its next clock power. For x in any C-invariant subspace of F₅, both x and Cx are in F₅. `clock_chain_drop_of_next_unpaid` thus puts x in F₄, hence the whole subspace lies in U′. Conversely U′ is an invariant subspace of F₅. By maximality in both grades U′=U. The new head has radius 1 at F₄. Choose it as w. The chain lengths at F₄,F₅,F₆,F₇ are 1,2,3,4. The w chain agrees with the old head at F₅ and then at each subsequent length by `clock_chain_next`.
2. The measured grade charts are E₇,E₈,E₉,E₁₀=e(K[X]≤6) ⊕ B₄,B₅,B₆,B₇ respectively (one sum per grade). Directness follows from measured dimensions 14,15,16,17, dim U=3, the ranks of at most n head powers, and the injectivity of the seven-dimensional polynomial band. B₄=F₇; B₅⊆F₈ because U,w⊆F₄ and the clock has true grade cost one. The first mesh is a polynomial of exact degree 7 with e(G)∈F₇.
3. If x∈F₈ is supported on one clock a, write x=e(H)+h in E₈, deg H≤6, h∈B₅. Then e(H)∈F₈. From (C−a)x=0 obtain e((X−a)H)∈B₆. Subtract the leading multiple tG to leave degree≤6. Directness in E₉ and polynomial injectivity imply (X−a)H=tG as polynomials. The true initial stage gives H(0)=0, and the paid probes give μ₀(H)=0 and μ₀(G),…,μ₅(G)=0. Applying μₖ to the identity successively gives μ₀(H),…,μ₅(H)=0. Write H=XJ, deg J≤5; `NativeMoments.x_moments_detect` at n=5 gives H=0. So x∈B₅. The measured E₈→E₉ jump shows B₅ is not clock-invariant; `HeadFiber.more_escape_sites` and `localized_mem` now put x∈U.
4. For u,v∈U (or v=w), the a-block of uv is (blockMask a u)·v∈F₈ by clock stability of U and native `zeroSpace_mul` at 4+4. Apply 3 to every block and assemble: U is a pointwise subalgebra, and U·w⊆U. By `HeadFiber.disjoint_rep` replace w by its clean representative without changing any Bₙ. In particular w∈F₄, w=0 on live U, and w²∈F₈. These are conclusions of this argument under the two numerical subcase assumptions, not further independent assumptions nor formalized claims about all ordinary subcases.
5. The E₈ chart and `HeadFiber.exists_poly` give actual equalities, coordinatewise:

       w² = e(P)+e(R)w+u,      e(G)=e(Q)w+v

   with u,v∈U, deg P≤6, deg R≤4, deg Q≤3. These degree inequalities allow the zero polynomial. Since B₅⊆F₈, e(P)∈F₈, whence P(0)=0 and μ₀(P)=…=μ₄(P)=0, using exactly 8+k+1≤13. Similarly G(0)=0 and its six moments come from F₇. E₁₀ attains the band rank (dim B₇=10); the seven powers w,…,C⁶w are independent modulo U. In particular w has at least seven distinct nonzero-head clocks, since otherwise their nodal polynomial would give a nontrivial dependence. Nothing here pays an eighth.

## 2. Leading transport identity

Disjointness gives vw=0; U is clock stable and therefore closed under multiplication by any e(H). Multiply the second equation in 5 by w and substitute the first. The resulting identity is

       e(G−RQ)w − e(PQ) ∈ U.

Put γ=coeff₇(G−RQ). If γ≠0, the identity expresses C⁷w in E₁₀: e(PQ)∈E₉ because deg(PQ)≤9; all other head powers have degree≤6. C maps U to U and sends e(K[X]≤6) into E₇, using e(G)∈B₄ at the top. Thus E₁₀ is clock-invariant and equals U+e(K[X])+w e(K[X]). It is a unital pointwise algebra since U is closed, w kills U, and the square equation rewrites every w² term.

## 3. The invariant branch is impossible on the actual quotient

Any finite unital coordinate subalgebra is precisely the functions constant on its classes of indistinguishable rows. For each class, multiply finitely many shifted/scaled separating elements, one against each other class, to obtain its indicator. A nonunital coordinate algebra U has the same description on its live support because it contains the live indicator (native `LiveCore.exists_live_indicator`). U's three atoms are entire E₁₀ classes: U is stable under c, which forces c constant on each atom, and w is zero there. On the complement, the E₁₀ classes are exactly the distinct pairs (cᵢ,wᵢ). Thus the 17 classes consist of 3 U atoms and exactly **14 distinct noncore pairs**.

At a noncore pair (a,z),

       G(a)=Q(a)z,       z²=R(a)z+P(a).

Define F=G²−RQG−P Q². Its degree is exactly 14 if γ≠0, since the top coefficient is G₇γ and deg(PQ²)≤12. Every noncore clock a contributes at most two pairs. At a singleton clock F(a)=0; at a double clock both G(a)=Q(a)=0 so (X−a)² divides F. Counting the 14 pairs saturates the degree: F has exactly the indicated simple and double factors and no others, even over extension fields. Q(a)≠0 at a singleton clock (otherwise G(a)=0 as well, an extra multiplicity). At a double clock F/(X−a)² is nonzero at a. No assumption Q≠0 is needed: Q=0 gives seven double clocks automatically.

E₉ modulo the three U atoms consists of the functions h(c)+s(c)w on the 14 pairs with deg h≤6 and deg s≤5; it has dimension 13. Its unique annihilator line has a nonzero entry on **every** noncore pair. To prove this, suppose such a function is zero except possibly at one target pair. Put T=hQ+sG, deg T≤12. Each other singleton gives a zero. At a double clock where both function values are zero, h,s,G,Q all vanish, so T has a double zero. If the target is a double clock, that clock still gives one zero since G,Q vanish there. We obtain at least 13 zeros counting multiplicity, hence T=0. At a singleton target, Q(a)≠0 shows the target value also zero. At a double target let Gₐ=G/(X−a), Qₐ=Q/(X−a) and z′ be its other amplitude. We have h(a)+s(a)z′=0 and h(a)Qₐ(a)+s(a)Gₐ(a)=0. Their determinant is nonzero: if Gₐ(a)=z′Qₐ(a), then (F/(X−a)²)(a)=Qₐ(a)²(z′²−R(a)z′−P(a))=0, impossible. Again the target function value vanishes. Thus no single noncore selector is in E₉. On all 17 classes the unique annihilator λ therefore has λᵢ≠0 off the three U atoms, and λ=0 on the U atoms.

Order the classes by first original occurrence; B is the strictly lower triangular matrix of first-representative rows with inputs summed by source class, exactly `causalMergeMatrix`. Let β be the **sum** of the original b on each class, y=1−c. All β on U atoms are zero because those atom indicators belong to F₄. At least two distinct y carry nonzero β: quadrature has reflected moments 1, 1/2, 1/3, inconsistent with a single mass clock. No positivity is involved.

For f∈E₉, Af∈E₁₀ is constant on each class, so B on the compressed f gives exactly Af on those classes. Native `reflectedStageRow_annih` at j=9, k=0,1,2 is paid (9+k+2≤13). Summing within classes, and dividing by k+1, shows

       Bᵀ(β yᵏ) − β yᵏ⁺¹/(k+1) = aₖ λ,   k=0,1,2.

No assertion of order for B nor for a reversed tableau was used. At the last β-active class j, λⱼ≠0. Put Y=yⱼ. If Y=0 then a₀=a₁=a₂=0; at the last active class with y≠0, the k=1 row reads 0=β y²/2, impossible. If Y≠0 then a₀≠0, a₁=Y a₀/2 and a₂=Y²a₀/3. Choose the last active class i with t=yᵢ≠Y. All later active clocks are Y. Test the three equations linearly with S=(X−Y)(X−Y/3). At i the Bᵀ term vanishes, the λ coefficient is a₂−(4Y/3)a₁+(Y²/3)a₀=0, and the primitive is t(t−Y)²/3. This rules out t≠0. For t=0, test S=X−Y instead. The transpose term and primitive both vanish at i but (a₁−Y a₀)λᵢ≠0. This final contradiction proves **γ=0** in all cases.

## 4. Killing the square polynomial and recovering the factor

Now G₇=R₄Q₃≠0: R and Q have exact degrees four and three. The transport identity implies e(PQ)∈B₇. Divide PQ=GH+J with deg H≤2 and deg J≤6. As e(G)∈B₄ and C-stability of U gives clock cost one per band step, e(GH)∈B₆. Consequently e(J)∈B₇. The direct E₁₀ chart and polynomial injectivity force J=0. Thus G divides PQ as polynomials.

If P≠0, first its degree is exactly 6: at degree≤5 write P=XV with deg V≤4 and use its five paid primitive moments and `NativeMoments.x_moments_detect`. Write G=XW and P=XV of exact degrees 6 and 5 for W,V. For the bilinear moment L(H)=primitive(XH)(1), V is orthogonal to degrees 0,…,4, W to 0,…,5. W,V are coprime. Indeed pass to an algebraic closure (the primitive moments commute with coefficient embeddings by the coefficient formula). At any common root a write V=(X−a)v, W=(X−a)z, deg v=4, deg z=5. Orthogonality gives L(Xᵏv)=aᵏL(v) for k≤5 and L(Xᵏz)=aᵏL(z) for k≤6. L(v)≠0 by the invertible five-row weight-X Cauchy form. The degree-five polynomial L(v)z−L(z)v then has six vanishing weight-X moments, contradicting the same detector at n=5. But G|P Q now yields W|VQ, hence W|Q, impossible at degrees 6 and 3. Therefore **P=0**; the previously missing degree-six coefficient vanishes.

At every nonzero head row, u=0, so the square identity gives wᵢ=R(cᵢ). The transport says e(G−RQ)w∈U, hence G−RQ vanishes on at least seven distinct true head clocks. Since γ=0 lowered its degree to ≤6, G=RQ. This is the requested actual ordinary quartic×cubic factorization and never borrows E₁₀→E₁₁.

**Boundary of the result.** The ordinary upstream rank/staircase producer does not by itself assert r=2 or dim F₄=4. Neither the other radii/ranks nor the marked first-seed-zero branch has been resolved here. `ERK13LateQuarticNative.late_nonorigin_quartic_impossible` is explicitly a zero-first-seed, late-terminal theorem: it cannot be called on this ordinary result. An ordinary last-port proof is separate, as is the R(0)=0 factor branch. No unconditional order-13 stage bound follows from this subcase alone.
