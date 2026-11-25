# Native ordinary ERK13 width 19: the nonzero-first-seed branch

Scope: K a characteristic-zero field, A a strict 19-stage original tableau, b its literal weights, reviewed HasOrder 13, and firstSeed ≠ 0. The proof uses the [clean-square argument](ordinary-clean-square.md) and [first physical port](ordinary-first-port.md) in the radius-two case. This does not touch firstSeed=0, certify an unconditional 20-stage floor, or claim completeness of Lean staging.

Write c=A1, C=diag(c), F_j=zeroSpace A j, E_j=treeSpace A j, e(H)=H(c), and μ_k(H)=primitive(X^k H)(1). Put B_n=U+span(w,Cw,…,C^(n−1)w), with B_0=U. From the paid ordinary staircase:
- dim U=5−r, 2≤r≤5, U is the maximal C-invariant subspace of F5, and F5=B_r, F6=B_(r+1), F7=B_(r+2).
- There is a degree-seven G with e(G)∈F7, G(0)=0 and μ_0,…,μ_5(G)=0 (the literal budget 7+k+1≤13).
- For j=7,8,9,10, E_j=V+B_(r+j−5), dim E_j=j+7, V=e(K[X]≤6) has dimension 7 by separation. Every sum displayed is direct: B_(r+j−5) has dimension at most (5−r)+(r+j−5)=j, and equality of total rank forces both the exact rank of B and disjointness.
- B_(r+3)⊂F8 and B_(r+4)⊂F9, by repeatedly applying C to the paid F7 chart. Measured tree growth between the displayed successive grades gives B_m non-C-stable for m=r+2,r+3,r+4. Thus there are respectively strictly more than m escape clock blocks modulo U, by HeadFiber.more_escape_sites. This counts actual clocks carrying physical w outside U, not individual nonzero b stages.

## A. Adjacent-shift purity: F8 ∩ C⁻¹(F8) ⊂ B_(r+3)

Write x=e(P)+h and Cx=e(P₁)+h₁ in E8, with deg P,P₁≤6 and h,h₁∈B_(r+3). If x,Cx lie in F8, then so do e(P),e(P₁). The true origin and five paid tests give P(0)=P₁(0)=0 and μ_0,…,μ_4(P)=μ_0,…,μ_4(P₁)=0. The vector space of such degree≤6 polynomials has dimension at most one: a nonzero element has nonzero degree-six coefficient (otherwise divide by X and apply NativeMoments.x_moments_detect at n=4), and any two elements can be linearly combined to cancel that coefficient.

Since C B_(r+3)⊂B_(r+4), e(XP−P₁)∈B_(r+4). Subtract tG to cancel the degree-seven coefficient. Directness of the E9 chart and injectivity of e on degree≤6 imply XP−P₁=tG as polynomials. If P≠0, write P₁=aP and use this identity to propagate μ_(k+1)(P)=a μ_k(P)+t μ_k(G) from μ_0(P)=0 up to μ_5(P)=0. Then dividing by X and using x_moments_detect at n=5 yields P=0, a contradiction. It follows that x∈B_(r+3). In particular, for a one-clock member of F8, Cx=ax∈F8, so it lies in B_(r+3). The escape count strictly greater than r+3 and HeadFiber.localized_mem now put every such x in U.

For v∈F3 and each u∈U, the clock slices of uv lie in F8: slice u using C-invariance, then multiply in F5·F3⊂F8. They are supported on one clock, so each lies in U and their finite sum does. Thus diag(v) preserves U. Also, for 0≤k<r, C^k(vw)=v(C^k w)∈F8. For k<r−1 both this vector and its C-shift lie in F8 and hence the vector is in B_(r+3). The last one is in this band as well: the preceding one lies in it, so the last belongs to B_(r+4); its E8 polynomial component must vanish by E9 directness. The preceding one exists because r≥2.

## B. No grade-three vector escapes the core

Take v∈F3 and suppose v∉U. With n=r+3 and usual head length r, HeadFiber.multiplier_profile_of_chart applies to the products from A. Its hypotheses are U-invariance under C and diag(v), r<n<escape-site-count except that only r>0 is needed, the pure B_n band for all k<r, and v∈F5=B_r with v∉U. It gives a nonzero polynomial P with deg P+r≤r+3 and (v−P(c))w∈U. In particular deg P≤3.

Here no closed core or disjoint head is assumed. Let M={i:v_i=P(c_i)} and J be the indicator projection onto M. Any mask or scalar function of the joint pair (c_i,v_i) preserves U: the separate finite masks follow from diagonal invariance and polynomial interpolation, and products of their projections give the joint masks. Off M, multiply (v−P(c))w by the pointwise reciprocal to see that (1−J)w∈U. Replace w by w'=Jw; every B_n is unchanged since both old and new heads differ by U, which is C-stable. Since v∈B_r, express v=u+L(c)w' for u∈U. It follows that every off-M clock slice of v lies in U, including v_a^-=(1−J)·1_{c=a}·v at every a.

Fix S=X or S=X(X−a₀) for a previously found nonzero knot a₀. Write z=S(c)(P(c)−v). This z is not in U: otherwise e(SP) lies in F5 because S(c)v∈F_(3+deg S)⊂F5 and U⊂F5; separation at degree≤6/grade 6 contradicts the nonzero SP of degree≤5. Take the first original row i at which matching z by U through the inclusive prefix becomes impossible. Before i choose u₀∈U matching z. At i let a=c_i; the clock-a part cannot be matched through i, because a matching vector there would patch u₀ using the C-mask alone. The clock-a part of z is zero on M and equals S(a)P(a) times the clock-a, off-M indicator minus S(a)v_a^- off M. Thus S(a)P(a)≠0, or the whole slice would be in U. This also proves a≠0 and, for the second S, a≠a₀.

For each T=X^k with deg T+deg S≤3, put L=primitive(TSP). The physical vector

    y=e(L)−A[T(c)(z−u₀)]
     = A[(TS)(c)v+T(c)u₀]−[A e(TSP)−e(L)]

belongs to F7. In fact (TS)(c)v∈F6, T(c)u₀∈U⊂F5, and the primitive discrepancy of the degree≤6 input is in F7. By causality y_j=L.eval(c_j) through row i, since z−u₀ was zero strictly before i. Its F7 chart writes y=u_y+D(c)w' with u_y∈U. On the clock-a, off-M part it equals the same mask of u_y and hence belongs to U. If L.eval(a)≠0, scale that piece by S(a)P(a)/L.eval(a) and subtract S(a)v_a^-: this is a vector of U matching the clock-a slice of z through i, including on M where both sides are zero. Contradiction. This pays the exact two native ports: at a₀≠0 the three values primitive(X^(k+1)P)(a₀)=0 for k=0,1,2, and at a₁≠0,a₀ the two values primitive(X^k X(X−a₀)P)(a₁)=0 for k=0,1. The same row within each family is used for every k.

For clarity the local scalar cut is as follows. Divide by the nonzero powers of a₀ and scale the independent variable, writing t=a₁/a₀ and P̃(T)=P(a₀ T). The first three weight-X moments of P̃ are zero at 1. If deg P≤2 they force P̃=0 by the checked weight-X Cauchy detector. If deg P=3, comparing its leading coefficient with the monic polynomial

    H₃(T)=T³−(12/7)T²+(6/7)T−4/35

gives P̃ proportional to H₃: three literal integrations show the same moments for H₃, and the difference has degree≤2. The two second primitives (after nonzero scaling) are

    t²(t−1)²(5t−2)(7t−6)/210,
    t³(t−1)²(30t²−35t+8)/210.

Since t≠0,1, the first gives t=2/5 or t=6/7; in the second the last quadratic evaluates to −6/5 or 2/49, both nonzero. This is native scalar algebra for this order-13 port, not any external low-order method classification or fixed tableau. Therefore F3⊂U.

## C. Exact surviving dimensions

Unconditionally dim F2=1 and dim F3≥2 by early strict growth and separation. The paid ranks dim F5=5 and dim F6=6 give dim F4≤4, dim F3≤3, and dim F4≥3. Since F3⊂U and dim U=5−r, r≤3. If dim F4=3 then dim F3=2, and the checked flat interval (j,d)=(3,1) gives F4=F3+C F3 and F4 non-C-stable. But F3⊂U and stable U imply F4⊂U. Since dim U≤3, this would force F4=U, a contradiction. Hence dim F4=4. Either r=2 (the peer's clean lane), or r=3 with F3=U of rank 2. This uses no unstated claim that a proper subspace F3⊂U is itself C-invariant.

## D. Close r=3 with automatic purity and physical compression

Here U=F3, dim U=2, dim F4=4. Apply the checked flat interval (j,d)=(4,2). Its core U₄ equals U: U≤F4, so its C-invariance puts it in U₄; and U₄≤F5, so maximality in F5 yields U₄≤U. The new radius is 4−2=2. Take the new original head w with F4=B₂, so w,Cw∈F4. Its F5 length-three band equals the old one; the C-step equality propagates this through all later charts. In particular F7=B₅, E8=V⊕B₆, E9=V⊕B₇, E10=V⊕B₈.

U is pointwise closed and U·w⊂U: at each clock slice the products have grades at most 3+3 or 3+4, hence belong to F7=B₅. E7→E8 pays >5 escape sites, so each slice lies in U by localized_mem. Assemble the slices. Choose the disjoint representative using HeadFiber.disjoint_rep, which preserves every band; thus w and Cw are still in F4, and w=0 on live core. Then w² and C(w²)=w·Cw both lie in F8. Part A gives w²∈B₆. Its clock-shift is also in B₆: it belongs to B₇ and lies in F8⊂E8, so the E9 directness eliminates the polynomial component; its E8 expansion then lies in B₆. In fact E9→E10 forces >7 escape clocks, hence at least eight distinct physical nonzero-head clocks.

The native multiplier_polynomial at n=6,d=1 now gives the true, nonzero P of degree≤4 with w_i=P(c_i) on all w-live original rows. Write e(G)=u+Q(c)w from F7=B₅, with u∈U and deg Q≤4.

**Eight-clock count.** Suppose the nonzero-head clock set S has exactly 8 elements. From w∈F4, the nine paid scalar moments of w up to k=8 give separately Σ_{c_i=x}b_i w_i=0 for every x (Vandermonde on S). Since w_i=P(x)≠0 at all head rows of clock x, each nonzero-head class has *unweighted by w* output mass zero. This does not require individual weights to be zero or that clocks on different classes be different.

The live core has exactly two disjoint atom classes, both indicators in U. Use the actual live indicator e∈U and choose u∈U outside its span. Its values on the live core contain at least two distinct scalars and cannot contain three, or e,u,u² would be independent. The two class indicators are the normalized affine functions of u and e. Each is a separate basis vector of U; C applied to it remains in U and vanishes on the other class, so its clock is constant on each class. Each has output mass zero by membership in F3.

Every row not in either the head or the core is clean, and e(G) vanishes at it. Scalar quadrature provides ≥7 distinct nonzero aggregate b clocks: if at most six, their monic nodal polynomial D and tests X^kD for 0≤k≤deg D≤6 would have exact integral zero while the unweighted rational Cauchy form is nonsingular. This argument uses only degree≤12. All these active clocks must be supplied by clean rows, as the core and head classes have zero mass individually. A degree-seven G therefore has exactly seven distinct clean clocks, all its roots; no further clean clocks are possible.

There are now 2 core classes, 8 nonzero-head classes and 7 clean classes, exactly 17 distinct labels. The three label types remain distinct even when two types share a clock. All E10 columns are constant on these classes: V depends only on c, U is constant on its two atoms and vanishes off core, and each head power has the single amplitude c^k P(c) on its own clock and is zero elsewhere. Thus dim E10=17 yields the full class algebra, and the hyperplane lemma can also be called simply with the 17-label count and rank E9=16. At every class with nonzero aggregate weight, original c≠1: it is a clean root of G, and G(1)≠0 follows from the native endpoint detector at n=6 with G=(1−X)L, L(0)=0, deg L≤6 and the six reviewed moments. The singleton visibility predicate is therefore vacuous. Apply physical_label_grade_impossible (or physical_class_grade_impossible with first representatives) at j=9,p=13. Contradiction.

Thus there are **at least nine** distinct physical head clocks. On each, G(x)=P(x)Q(x) because U is disjoint. The difference has degree≤8, so G=P Q exactly. Both factors are nonzero with degrees adding to seven; either P is cubic and Q quartic, or P is quartic and Q cubic.

**Cubic head factor.** Reuse the exact cubic two-knot cut from B, now with v=w, the actual closed live core, and the stronger payment Cw∈F4. The two masks S=X and S=X(X−a₀) give all of the same tests: for deg(TS)≤3 and divisibility by X, (TS)(c)w∈F_(3+deg(TS))⊂F6, since Cw is already in F4; a primitive input of degree≤6 is also paid. One can use the simpler live-indicator residual described in the next paragraph. Thus the cubic profile is impossible with no use of the global factorization after the degree has been identified.

**Quartic head factor and exact port transfer.** Use the peer's ordinary clean quartic cut with the sole interface change F7=B₅ instead of F7=B₄. The proof needs only that every F7 column vanishes on an original row off both U and w, not the chart length. Precisely, for any mask S in the peer's proof, form z=e(SP)−S(c)w−(SP)(c)e where e∈U is its live indicator. At each supported row of U or w the residual is zero. It is nonzero by separation since S(c)w∈F_(4+deg S) and (SP)(c)e∈U. At its first nonzero row i, strict causality makes A(T(c)z)_i=0 for every allowed T, and subtraction of the paid primitive defect puts e(primitive(TSP))−A(T(c)z) in actual F7. Consequently primitive(TSP)(c_i)=0 and G(c_i)=0. For P(0)≠0, use S=X,T=1 and G=X(PN) with deg N=2; this is the existing native quartic/quadratic six-moment cut. For P(0)=0, write P=XR and either use the peer's cubic/cubic six-moment cut with S=T=1, or use the already proved cubic two-port scalar gate on R: masks S=1 and S=X−a₀ and tests k≤2 and k≤1, respectively, satisfy deg(TS)≤2, and a₀≠0 because P(0)=0. Thus r=3 is excluded in both origin placements.

Combining A–D with the separate fully specified mathematical radius-two square/port proofs excludes the entire ordinary firstSeed≠0, strict width-19 branch on paper. The joint-mask and rank/radius reductions and their composition have not yet been checked in Lean. This source proof imports no held lower-order exact arithmetic, legacy endpoint data/packets, or unrelated order family.
