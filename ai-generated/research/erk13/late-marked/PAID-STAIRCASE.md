# The late marked paid staircase and low-radius reduction

Work over a characteristic-zero field with a strict 19-row tableau A, literal output row b, the reviewed rooted-tree `HasOrder 13 A b`, vanishing literal first reflected seed, and the final coordinate ℓ absent from the genuine E₇. This is the paper derivation of the chart needed downstream, not an end-to-end Lean theorem. [Prerequisites](PREREQUISITES.md) lists the exact native entrances and source status.

Write c=A1, C=diag(c), F_j=zeroSpace A j, E_j=treeSpace A j, e(P)=P(c), μ_k(P)=primitive(X^k P)(1), and λ_k(P)=μ_k(P)−μ_(k+1)(P). The paid frame gives b_L≠0, c_L=1, ℓ∉E₆, dim F₅=5, dim F₆=6, 2≤r≤5, and a maximal C-invariant U⊂F₅ of dimension 5−r. Write D_n=U+span(w,Cw,…,C^(n−1)w), so F₅=D_r, F₆=D_(r+1), and D_(r+2)=F₆+C F₆ is an actual 7-dimensional subspace of F₇. The last-output probe excludes ℓ from every F_j used below. The superscript + adjoins Kℓ without changing stage coordinates.

## 1. Exact marked staircase and the first terminal timing

The native first escape pays a∈{5,6}, deg G=a+1, e(G)=d+γℓ with d∈D_(r+2), and the first chart E_(a+1)^+=V_a+D_(r+2)+Kℓ, where V_a=e(K[X]≤a). True origin gives G(0)=0; the six real F₇ probes give μ_0(G)=⋯=μ_5(G)=γ b_L. In particular λ_k(G)=0 for k≤4 in either fork.

Let L_n=primitiveBack A b n. LastActive.primitiveBack_tail and primitiveBack_annih give L_(11−j)⊂annih(E_j^+) at the exact bound j+(11−j)+2=13. Native back_finrank and first_dim_zero give dim L_n≥n. At j=6, rank E₆^+=14 by PaidFrame, so L₅=annih(E₆^+) and rank L₅=5. We have dim E₅^+=12: E₅=V₅⊕F₅ by reviewed tree decomposition plus degree-five separation, and ℓ∉E₆ prevents ℓ from E₅.

For j=6,7,8,9 inductively suppose dim E_j^+=j+8. Then L_(11−j)=annih(E_j^+) with exact rank n=11−j. If E_j^+ were C-invariant, the annihilator would be invariant under diag(1−c), and the checked reverse_clock_invariant_gain gives dim L_(n+1)≥n+floor((n+2)/2). At j=6 this is 8, whereas E₅^+ gives an upper bound 7. At j=7,8,9 the preceding saturated chart gives upper bound n+1 and the gain is at least two. Thus E_j^++C E_j^+ strictly extends E_j^+; its containment in E_(j+1)^+ is the actual clock grade step and Cℓ=ℓ. Reverse room gives the matching upper rank, so
E_(j+1)^+=E_j^++C E_j^+,   dim E_j^+=j+8 for j=6,…,10.

For a+1≤j≤10 it follows that
E_j^+=V_a ⊕ D_(r+j−a+1) ⊕ Kℓ.
The equality propagates because C V_a⊂V_a+D_(r+2)+Kℓ, using the top degree of G. Directness and each component's full rank follow by saturating the upper estimates (a+1)+(5−r)+(r+j−a+1)+1=j+8. The indicated head band is actually contained in F_(j+6−a).

If a=5 then γ≠0: otherwise e(G)∈F₇ with degree six contradicts ordinary next-band separation q=6, paid by 2·6+1≤13. Thus ℓ enters exactly E₇, because e(G) and d are in E₇. If a=6 the terminal may or may not be present in E₇. A late terminal (ℓ∉E₇) gives dim E₇=14, hence dim F₇=7 by the same next-band separation and D_(r+2)⊂F₇. For either shape dim F₇≤8 by the paid midpoint's next-defect room with zero first-seed rank.


## 2. Adjacent shifts force marked purity, including single-clock vectors

For j=7 or 8 let m=j−6. Suppose x,Cx,…,C^m x∈F_j^+. Expand x_s=C^s x=e(P_s)+d_s+α_sℓ in the corresponding direct E_j^+ chart. Since the head band is paid in F_(j+6−a), true origin and probes give P_s(0)=0 and μ_k(P_s) constant through k=a+6−j. Thus λ_k(P_s)=0 for k≤a+5−j. Comparing x_(s+1) and Cx_s, the column e(XP_s−P_(s+1)) lies in D_(r+j−a+2)+Kℓ. Subtract the leading multiple t_s G and use directness of the next chart and injectivity on the degree≤a polynomial band. This is the literal polynomial equality XP_s−P_(s+1)=t_s G. Because λ_k(G)=0 through k=4, recursion along the m adjacent equalities upgrades P₀ to λ_k(P₀)=0 through k=a−1 (the latest λ index used on G is a−2≤4). Then P₀/X vanishes by the rational weight-X(1−X) detector. Thus x has no polynomial component.

If x is in actual F_j rather than only F_j^+, its mark coefficient also vanishes: the paid band lies in F_(j+6−a), and ℓ is excluded even there by the b_L probe. Here a=6, so x∈D_(r+j−5).

In particular every actual F₇ or F₈ vector supported on a single numerical clock lies in U. All adjacent shifts are scalar multiples of it; after purity it lies in D_(r+j−a+1)+Kℓ. This band is the clock chain over U+Kℓ, still C-stable as core, and is not C-invariant by the measured next chart and C V_a payment. Thus HeadFiber.more_escape_sites and localized_mem put x in U+Kℓ. Since x∈F_j and ℓ∉F_j, x∈U. This is a genuine one-clock result on original rows, including clock 1.

## 3. The paid low grades lie in the core

For d₀=2,3 put j=5+d₀, and take v∈F_(d₀). Multiplying v by a clock slice of u∈U gives a one-clock member of F_j, so it is in U and assembly gives diag(v)U⊂U. For x_k=v C^k w, 0≤k<r, we have x_k∈F_j. Provided r≥d₀, the adjacent-shift lemma applies whenever k+(j−6)<r; for d₀=2 this needs one next shift, and for d₀=3 it needs two. All the remaining tail x_k are also in D_(r+d₀): shift the preceding pure x_(k−1) so the new vector lies one power longer. Since the late branch has a=6, the next E-chart's directness forces its E_j^+ polynomial and mark components to vanish. Repeat for each tail shift. If r=2 and d₀=3, one needs no product argument: v,C²v∈F₅=D₂ and the first four head powers are independent modulo U. This forces v∈U.

For the other cases, if v∉U, the paid multiplier_profile_of_chart with n=r+d₀ gives a nonzero P of degree≤d₀ such that (v−P(c))w∈U. There are enough escape clocks: the next marked tree jump proves more than r+j−a+1 head clocks modulo U+Kℓ, hence at least that many modulo U. Joint (c,v)-masks preserve U by separate diagonal invariance. As in the ordinary proof, mask w to the locus M={v=P(c)} by absorbing the difference into U; all the bands stay fixed, and each off-M clock slice of v then lies in U. These steps involve the real U, not U+Kℓ.

For S=X or S=X(X−t₀), choose the first original prefix on which z=S(c)(P(c)−v) cannot be matched by U; it exists since global membership in U would put e(SP) in F₅, contrary to degree≤5 separation. Choose u₀∈U matching z before that row. At its clock t, the off-M clock slice cannot be matched through the row (otherwise patch the earlier match by clock projections); moreover S(t)P(t)≠0 because the off-M v slice lies in U. For T=X^k with deg(TS)≤3, the exact physical transport is
e(primitive(TSP))−A[T(c)(z−u₀)] ∈ F_(d₀+4).
This follows by subtracting the native primitive defect from A[(TS)(c)v+T(c)u₀]. Strict causality identifies its evaluations through the pivot prefix with the displayed primitive polynomial. If the transport space is genuinely covered by a head band, its clock-t off-M part belongs to real U. A nonzero primitive value then supplies a matching vector after scaling by S(t)P(t) and subtracting the known off-M v slice. Therefore the primitive value must be zero. No terminal vector is allowed in this last step, and none is used.

- For d₀=2 the transport space is actual F₆=D_(r+1) in the late chart. Use just S=X, k=0,1,2 at the first t≠0. Rescaling t to 1 gives three weight-X moments of deg P≤2, forcing zero. Hence F₂⊂U always. In particular r=5 is impossible since dim F₂=1.
- For d₀=3 the transport is valid under F₇=D_(r+2), i.e. measured dim F₇=7, which was earned above. Use S=X, k=0,1,2, and then S=X(X−t₀), k=0,1 at t₁≠0,t₀. The local scalar problem is exactly the cubic two-port problem from the ordinary source (not a theorem about an ordinary staircase): at the first knot scale to 1 and get a cubic proportional to T³−12T²/7+6T/7−4/35; at the second the two primitive equations factor as in that source and have no common root away from 0,1. Lower-degree profiles die at the first knot. Thus F₃⊂U in the late branch. As dim F₃≥2, r≤3. Also dim F₄=4, for if it were 3 the flat grade-three-to-four step would give F₄=F₃+C F₃⊂U, hence F₄=U by dim U≤3, contrary to the next required non-C-stability. At r=3, F₃=U of rank two. At r=2, F₃⊂U and dim F₄=4 actually hold regardless of dim F₇.
