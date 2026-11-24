# Elementary stage bounds for real explicit Runge–Kutta methods: a logarithmic gain

**Theorem.** Let p≥10 be an integer and let h be the largest nonnegative integer with 5·2^h≤floor(p/2). A real explicit Runge–Kutta method of classical order at least p has s≥⌈3p/2⌉−1+h stages. No assumptions on weight signs, zero weights, repeated abscissae, or exterior abscissae are used.

Sections 1–5 establish the audited unconditional bound (the h=0 case) with a shortened degree-five argument. Sections 6–9 supply the new stronger bound by a flat-band obstruction and dyadic induction. The order-twenty gain is the first nontrivial instance, not a separate premise. Neither the order-eight nor order-nine finite refinement is used.

## 1. Algebra of stage defects

Let A be the strictly lower triangular s×s stage matrix, b the output row, 1 the all-ones column, c=A1, and C=diag(c). Stage-vector products and powers below are componentwise unless matrices are explicitly written. Set Jf(x)=∫₀ˣ f(t)dt.

Generate stage–polynomial pairs from (1,1) by extension (v,f)↦(Av,Jf), which raises degree by one, and multiplication (v,f)(w,g)=(vw,fg), which adds degrees. Take all linear combinations respecting the degree cap. This is exactly the ordinary rooted-tree stage algebra (degree = tree order−1). Classical order p implies b v=∫₀¹ f for each pair of degree ≤p−1. One direct verification, not requiring the tree factorial convention, is to realize an extension as an extra coordinate with derivative the previous observable, zero initial value, and realize multiplication as a product of observables. If a pair has degree k, evaluated in an h-step its numerical stage observable is h^k v and its exact observable at time hx is h^k f(x). Finish by integrating the observable in a new coordinate. Order p forces equality of its numerical and exact h^(k+1) coefficients for k≤p−1. This construction uses only triangular polynomial autonomous systems.

The pairs (f(c),f) exist for every polynomial f of degree not exceeding the cap, since c is the stage vector paired with x. Let F_q denote stage vectors of pairs (v,0) of degree ≤q, P_q={f(c):deg f≤q}, and E_q=F_q+P_q. Thus every pair (v,f) has v−f(c) in F_q. We use
```
F₁=0;  d:=Ac−c²/2 ∈ F₂;
A F_j + C F_j ⊆ F_(j+1);  F_i·F_j ⊆ F_(i+j);
τ_k:=A c^(k−1)−c^k/k ∈ F_k.
```
The assertions are direct from the pair rules; for F₁, the generators are just (1,1) and (c,x). Every vector in F_q has first coordinate zero: at stage one, extension is zero and every polynomial of positive homogeneous degree evaluates to zero at x=0. Chain pairs (A^j1,x^j/j!) first give s≥p.

If p≥2q and a pair (0,f) of degree ≤q exists, then f(0)=0 and f=xg, deg g≤q−1. Multiplication by (g(c),g) and the order moments give ∫₀¹ xg²=0, so f=0. Equivalently, the stage matrix is **separated** through q: polynomial evaluation is injective on degree ≤q, and P_q∩F_q=0. Conversely, separation through q gives a linear functional on E_q by mapping f(c)+d to ∫₀¹ f, d∈F_q. Extend it to an output row. This row obeys the pair moment conditions through q, which is all we will need from it.

## 2. Forward–backward rank and the baseline

We first use a simple triangular obstruction. Let N be strictly triangular, Y diagonal, and U invariant under both. If NYv−Y²v/2∈U, then Yv∈U. Indeed let D=Y† be the diagonal partial inverse (entries 1/y at y≠0 and 0 otherwise); it is a polynomial in Y. For z=Yv and r=Nz−Yz/2, we have (I−2DN)z=−2Dr, because DYz=z. The inverse is a finite geometric sum in the strictly triangular matrix 2DN and preserves U.

For any 2≤j≤p−1, if F_j=F_(j−1), this common space is invariant under A,C and contains d. The obstruction would put c in F_j, impossible because b kills F_j and bc=1/2. Thus F_j grows strictly and dim F_j≥j−1. The same reasoning works through q under separation through q, using the just-constructed output row.

For the backward spaces use X=I−C and the row residuals
```
ℓ_k = b X^(k−1) A − b X^k/k;
L₀=0,  L_r = L_(r−1) + L_(r−1)A + L_(r−1)X + span(ℓ_r).
```
If (v,f) has degree ≤q and q+r≤p−1, then
```
b X^(r−1) A v = ∫₀¹ (1−x)^(r−1) Jf(x)dx
               = (1/r)∫₀¹ (1−x)^r f(x)dx = b X^r v/r .
```
Induction using AE_q,XE_q⊆E_(q+1) shows L_r E_q=0 at that budget. Every L_r with r≤p−1 therefore annihilates 1, whereas b X1=1/2. Under a plateau L_r=L_(r−1), r≥2, the common space would be invariant under right A and X, and contain ℓ₂. The transposed triangular obstruction would put bX there. Hence dim L_r≥r−1, or ≥r if ℓ₁≠0.

Delete any unused trailing stages (zero trailing output weights), leaving b_s≠0. For p≥5, put q=⌊p/2⌋ and r=p−1−q. Separation and orthogonality give
```
s ≥ q+1 + dim F_q + (r−1).
```
At odd p this count gains one more dimension. If ℓ₁≠0, use dim L_r≥r. Otherwise ℓ₁=0 forces c_s=1 by the last coordinate, and L_r vanishes there by its recursion. The column e_s is outside E_q: otherwise e_s=f(c)+d with f=xg by the first coordinate. Testing against any polynomial h of degree ≤q yields ∫₀¹ h f=b_s h(1). Choosing h=(1−x)g first gives ∫₀¹ x(1−x)g²=0; choosing h=1 then gives b_s=0, a contradiction. Thus in either parity
```
s ≥ ⌈3p/2⌉−2 + [dim F_q−(q−1)].
```
In particular the baseline holds, and the algebraic pair moments through degree four already force at least six stages (p=5).

## 3. Two short causality tools

**Chronological compression.** For a subspace H, greedily retain each coordinate evaluation on H independent of earlier ones. The restriction R to retained coordinates is an isomorphism from H onto the retained coordinate space. In each retained row of a strictly lower triangular matrix N, substitute for any earlier omitted input its linear expression from retained inputs before that input. The resulting lower triangular N' obeys N'Rv=RNv for v∈H. Diagonal operators commute with restriction. If H=E_q, row sums of the substitution weights are one (apply to 1), so the reduced RK matrix has the original retained c. Induction on extension and product shows that all stage vectors and defects through degree q+1 are exactly restricted; at each extension its input has degree ≤q and lies in H. Therefore rank through q is preserved and separation through q survives.

**Invariant-space amplification.** A separated stage matrix cannot have CF_j⊆F_j and dim F_(j+1)≤dim F_j+1 for 3≤j within the separation cap. Compress H=E_j as above and write K=F_j, which remains C-invariant. Then K^⊥ decomposes by diagonal node blocks (the spectral projections are polynomials in C). Each block has dimension at most one, since a row orthogonal to 1 at its block node is orthogonal to every polynomial column and hence to all H. As dim K^⊥=j+1, we have exactly j+1 represented nodes, with respective rows λ_u normalized by λ_u1=1. Thus λ_u f(c)=f(u). At zero the row is e₁ᵀ, since all defects vanish at stage one and index one survives compression. Put a_u=λ_u A and k_u=max support index of λ_u. These k_u are distinct because the node supports are disjoint, and a_u is supported before k_u.

Let u,v be the first two nonzero represented nodes ordered by k. Any row in K^⊥ supported before k_u is a multiple of λ₀; one supported before k_v is a combination of λ₀,λ_u. To see this, each represented node's last nonzero coordinate would otherwise occur beyond the support limit and cannot be canceled by a different node row. For m<j the primitive residuals imply a_u c^m=u^(m+1)/(m+1). Thus F_(j+1)=K is impossible: then a_u annihilates K, hence evaluates c to zero, contrary to a_uc=u²/2.

Otherwise F_(j+1)=K+span(w). With σ_x=λ_xw, for z∈K the value a_x z is a fixed linear function of z times σ_x, and a_x c^j=x^(j+1)/(j+1)+γ σ_x for one common γ. The row a=σ_u a_v−σ_v a_u therefore annihilates K and is supported before k_v. Test it on g(c), g(x)=[x²(x−u)²]'. Since g(0)=g(u)=0 its value is zero. The moment expression is σ_u v²(v−u)²; at j=3 the two possible degree-three errors cancel by construction. Thus σ_u=0. Now a_u annihilates K, so evaluates c to zero, the same contradiction. No lower bound on dim F_j and no consecutive completion indices were needed.

Finally, if an actual stage at a nonzero node u evaluates every pair through grade five exactly at u, its prior rows number at least six. Indeed the row of A entering this stage is supported on prior stages and, by extension, pairs each observable of degree k≤4 with ∫₀ᵘ f. Divide both the prior matrix block and the incoming row by u. Homogeneity by degree makes the resulting algebraic moment conditions exactly those through grade four for integration on [0,1], also when u<0. Apply the baseline at p=5. This use needs no general represented-node completion theorem.

## 4. The degree-five barrier

Suppose some stage matrix separated through degree five has dim F₅≤4. Strict forward growth gives equality and dim F₂,F₃,F₄,F₅=1,2,3,4. Compress E₅ to its ten distinct independent rows. No two stage evaluations on E₅ agree. In particular there are no identical incoming rows (when newer coefficients are zero and the row agrees with an earlier one), and c₂≠0: if c₂=0 then the second row is identically zero as is the first. By amplification only F₃ and F₄ need be noninvariant under C; **no condition on invariance of F₅ is used.**

### Case I: d and Cd are independent

They span F₃. Its noninvariance forces C²d outside it, so F₄=d·span(1,c,c²); noninvariance of F₄ likewise gives F₅=d·span(1,c,c²,c³). Since d²∈F₄, we have d²=g(c)d for some nonzero polynomial g of degree ≤2. On a defective stage (d_i≠0), d_i=g(c_i); on a regular stage all grade-five defects vanish.

The column z=c g(c)−Cd pairs with xg through degree three. It vanishes at every defective node and at c_i=0, and is not identically zero by separation. Let i be the first regular stage with c_i=u≠0. Its predecessors all have z=0, and there are at least six by the previous causality tool. Of these, only stage one can be a regular zero node (otherwise its evaluations on P₅+F₅ duplicate stage one). Also any two defective predecessors with the same node have identical evaluations on P₅+F₅. Thus at least five *distinct* defective nodes precede i; this is deduced here rather than assumed from the minimal profile.

Extend the pair for z: Az−(J(xg))(c)=d h(c) for some h of degree ≤2. At each of the five distinct defective predecessor nodes ξ, (Az)=0 by strict causality, so J(xg)(ξ)=−g(ξ)h(ξ). This is a polynomial identity by the degree-four cap. Comparing lowest powers at zero forces h to be a multiple of x²; comparing the other coefficients then forces g to be a single monomial (the coefficient factor 1/(k+2) of J(x·x^k) depends injectively on k). But (Az)_i=0 and d_i=0, whereas J(xg)(u)≠0 for a monomial and u≠0. Contradiction.

### Case II: Cd=λd

Here λ=c₂≠0 since d₂=−c₂²/2. Let w=Ad. It is independent of d: otherwise F₂=span(d) is invariant under A,C, and the triangular obstruction puts c in F₂. Thus F₃=span(d,w); noninvariance of F₃ and F₄ gives F₄=span(d,w,Cw) and F₅=span(d,w,Cw,C²w). The support of w contains at least two node values other than λ: otherwise the C-invariant span generated by d,w has dimension at most three (at most two directions at λ and one at the other node). It contains the three-dimensional F₄, so F₄ itself would be invariant. From d²∈F₄ write d²=δ d+(α+β C)w. The two other nodes force α=β=0, and row two gives δ=−λ²/2.

By homogeneity scale λ to one. Every defective stage then has node 1 and d=−1/2 there. Write t=c₃, z=c₄, y=c₅. Stage three cannot be defective: if it were, c₃=1 and a₃₂=(Ac)₃=0, so it duplicates stage two. Hence a₃₂=t²/2, w₃=−t²/4, and t≠0 (otherwise it duplicates stage one). Evaluating A c²−c³/3 in F₃ on rows two and three gives (2/3)d+(4t/3−2)w. Consequently at stage four, with defective indicator ε₄,
```
a₄₂+t a₄₃=(z²−ε₄)/2,
(2t/3)a₄₂+t²a₄₃=(z³−ε₄)/3 .
```
If ε₄=1, then z=1 and the nonsingular system gives a₄₂=a₄₃=0, a duplicate of stage two. Otherwise a₄₂=z²(3t−2z)/(2t), a₄₃=z²(z−t)/t². Nodes z=0,t duplicate stages one or three, so z(z−t)≠0. Since Aw∈F₄, rows two and three force Aw=k(C−tI)w; its nonzero fourth component guarantees w₄=−z²(3t−2z)/(4t)≠0 and k=t/(3t−2z).

The entire fourth-degree test is one quartic:
```
Q(x)=x²(x−y)(x−3t/2)/4 .
```
Then A Q'(c)−Q(c) lies in F₄ and has a unique expansion on d,w,Cw. Its row-two value fixes the d coefficient, leaving 2Q(1)d+χ(C)w for affine χ. At rows three and four use Q'(t)=t w₃/2, Q(t)/w₃=t(t−y)/2, Q(z)/w₄=t(z−y)/2 and Aw=k(C−tI)w to interpolate
```
χ(x)=−2Q'(1)+(t/2)k(x−t)+(t/2)(y−x).
```
For example row four is a₄₂Q'(1)+a₄₃Q'(t)−Q(z); here a₄₂=−2w₄ and a₄₃w₃=k(z−t)w₄. At row five, Q(y)=0 and Q(1)d₅=0 even for a defective row; w₅=−a₅₂/2. Thus (A Q'(c)−(t/2)Aw)₅=a₅₂Q'(1). Cancel the latter term and the vanished column-three term; only column four remains:
```
0=a₅₄[Q'(z)−(t/2)w₄]=−(3/4)a₅₄ z(z−t)(y−z).
```
If a₅₄=0, the two moments as at row four, with RHS β y²/2, β y³/3, β=1−ε₅, give a₅₂=β y²(3t−2y)/(2t) and a₅₃=β y²(y−t)/t². The Aw equation then gives β y²(y−t)(z−y)=0 (multiply its residual by 2(3t−2z)). If β=0 then row five duplicates stage two; if β=1 then y∈{0,t,z}, and the preceding coefficients and row sum give one of stages one, three or four. Consequently a₅₄≠0 and y=z.

Take L=e₅ᵀ−ε₅e₂ᵀ−(w₅/w₄)e₄ᵀ. Because y=z it kills d and all powers C^j w, so LF₅=0. But (ACw)₄=t(Aw)₄ and (ACw)₅=t(Aw)₅+(z−t)a₅₄w₄, since w first appears at stage three. The Aw terms cancel in L by its equal-node relation, giving LACw=(z−t)a₅₄w₄≠0. This contradicts ACw∈F₅. No calculation of z=2t or normalized separating functional is required.

Both cases being impossible, every separated matrix through grade five has dim F₅≥5.

## 5. First unconditional extra stage (the h=0 case)

For p≥10, q=⌊p/2⌋≥5. Separation holds through q. The degree-five barrier and strict growth yield dim F_q≥q. The surplus formula therefore yields s≥⌈3p/2⌉−1.


## 6. Invariance costs surplus at the end of a flat band

The next argument proves an unconditional logarithmically growing excess beyond the p≥10 bound just established. It subsumes the order-twenty extra stage and does not need any separate order-eight or order-nine proof.

For j≥5 within the separation cap, if CF_j⊆F_j then
```
dim F_j ≥ ceil(3j/2)−3.
```
Indeed compress E_j and form its normalized node rows λ_u exactly as in §3. There are j distinct nonzero represented nodes. For such a node, the polynomial correspondence says λ_u v=f(u) for every admissible pair (v,f) through degree j. If its last nonzero coordinate is k_u, then λ_u A is supported on the k_u−1 prior coordinates and evaluates every pair through degree j−1 as ∫₀ᵘ f. Scaling by u produces the moment identities for order j on these prior coordinates (same argument as for an exactly evaluated stage in §3). Therefore k_u≥ceil(3j/2)−1 by the baseline. These j indices are distinct, so the compressed size dim F_j+j+1 is at least ceil(3j/2)−2+j, giving the claim.

A band [j,2j] will be called flat if dim F_(a+1)=dim F_a+1 for every j≤a<2j. We next prove that every such band, for j≥5 and with separation through 2j, has an invariant endpoint F_(2j). The proof does not assume any particular value of dim F_j.

## 7. An unsaturated band is one growing polynomial chain

In a flat band the intermediate spaces F_j,…,F_(2j−1) are not C-invariant by §3. Suppose for contradiction that F_(2j) is also noninvariant. Write W=F_j, and let Π be the Euclidean orthogonal projector onto W. Then (I−Π)C restricted to W is rank one since W+CW touches just one new direction. Express it as u vᵀ with u∈W^⊥ and 0≠v∈W. The compression T=ΠC restricted to W is symmetric. Let V=span(T^i v:i≥0), of dimension r≥1, and W₀=W∩V^⊥. Then W₀ is C-invariant: it is T-invariant and orthogonal to v. Choose nonzero w∈V orthogonal to v,Tv,…,T^(r−2)v; for r=1 this orthogonality list is empty. The first r cyclic vectors are independent, by Cayley–Hamilton or successive powers, so vᵀT^(r−1)w≠0. For 0≤i<r, C^i w=T^i w, by the rank-one formula; pairing these with v,Tv,…,T^(r−1)v gives an antitriangular matrix with nonzero antidiagonal. Thus
```
W = W₀ ⊕ span(w,Cw,…,C^(r−1)w).
```
The sum is orthogonal. Because C is symmetric and preserves W₀, the entire chain stays orthogonal to W₀.

Let S be the coordinate support of w and N the number of distinct abscissa values on S. The first l chain vectors span min(N,l) dimensions by Vandermonde rank (one nonzero spectral projection of w at each of those N values). If the chain saturated for some F_(j+a), a≤j, take its first saturated grade by growing it via C. Up to and at that grade it uses every one of the a available increments, so that grade equals W₀ plus the full C-invariant chain space. This contradicts the stipulated noninvariance of every grade in the band. Hence N≥r+j+1 and
```
F_(j+a) = W₀ ⊕ span(w,Cw,…,C^(r+a−1)w),   0≤a≤j.
```

**A diagonal multiplier is a low-degree polynomial on the chain.** Suppose a real diagonal Δ sends W to F_(j+d) for 1≤d≤j. The C-invariant W₀ decomposes into local spaces on single abscissa blocks (spectral projection). If h∈W₀ is local to one block, Δh still lies in that block. In the displayed orthogonal decomposition, its chain polynomial must therefore vanish at all but possibly one of the N supported abscissae. This uses blockwise orthogonality: the block projection of each chain vector is orthogonal to the local part of W₀. Since the polynomial's degree is ≤r+d−1 and N−1≥r+d, it is zero identically. Thus Δ preserves W₀. By symmetry it also sends w to W₀^⊥, hence Δw=P(C)w with deg P≤r+d−1. For 1≤k≤r−1, commutation of diagonal operators gives C^kΔw=ΔC^kw∈F_(j+d), again perpendicular to W₀; it has a polynomial representative of degree at most r+d−1. Inductively compare that polynomial with x^k P on the N abscissae: at step k the previous bound on deg P is r+d−k, so deg(x^kP)≤r+d<N and equality at those abscissae is an identity. The new bound is deg P≤r+d−1−k. This ends with deg P≤d, including r=1 directly.

In particular take Δ=diag(f) for any f∈F_j and d=j. The product rule in §1 supplies the necessary inclusion. Since (Δw)_i=f_iw_i, each f agrees with a single polynomial of degree ≤j on S. A block-local f∈W₀ has polynomial zero at all the other N−1≥j+1 supported abscissae, so it vanishes throughout S. Thus W₀ vanishes on all of S. Taking f=w yields a nonzero polynomial P of degree ≤j such that w_i=P(c_i) on S. (One may strengthen this to degree ≤j−r+1 using the same claim for C^(r−1)w, but the weaker statement suffices.)

## 8. Two causal contrasts contradict an unsaturated band

Use a polynomial Q of degree at most two, nonzero, with Q(0)=0. The vector
```
z_Q = (QP)(c) − Q(C)w
```
makes an admissible pair with nonzero polynomial QP through grade j+deg Q, since w∈F_j. Separation through 2j implies z_Q∉F_j, hence z_Q∉W₀. The vector z_Q vanishes on S. It also vanishes at every node where Q=0. Let i be the smallest index for which the first i coordinates of z_Q are not the prefix of an element of W₀; choose h∈W₀ agreeing up to i−1. The mismatch is at a coordinate outside S. As W₀ decomposes into abscissa blocks, the restriction of z_Q to the prefix in the block ξ=c_i cannot be the corresponding restriction of W₀: otherwise substitute just that block component into h. On the block, S coordinates are zero for both z_Q and W₀. Finite-dimensional separation therefore gives a row λ supported on prefix coordinates of this block **outside S**, annihilating W₀ but with λ z_Q≠0. This remains valid if the same node also has coordinates inside S. On this row support z_Q=(QP)(ξ), so λ1≠0 and Q(ξ)≠0. The row kills every chain vector as well, and hence annihilates all of F_(2j).

For any polynomial R of degree ≤j−deg Q−1, the vectors R(C)z_Q and R(C)h agree up to i−1. All outputs inspected by λ use only those earlier inputs by strict causality. Since R(C)h∈W₀ and A W₀⊆F_(j+1), we get λ A R(C)z_Q=0. On the other hand the stage-pair rule gives
```
A R(C)z_Q − (J(RQP))(c) ∈ F_(2j),
```
by the degree budget 1+deg R+deg Q+j≤2j. Thus
```
∫₀^ξ R(x)Q(x)P(x) dx = 0  for all deg R≤j−deg Q−1.
```
The same λ works for every R; no condition on R(ξ) was used.

First choose Q=x, yielding ξ=u≠0 and moments through deg R≤j−2. On the interval between 0 and u the factor x has fixed nonzero interior sign, so P has at least j−1 distinct interior sign-changing roots. In general, with fewer than m+1 such roots when all test degrees ≤m vanish, choose the product of the linear factors at the sign-changing roots as R: then the integrand has one nonzero sign away from isolated zeros and cannot have zero integral.

Now choose Q=x(x−u), yielding a distinct ξ=u'∉{0,u} and moments through deg R≤j−3. The previous moments at u also apply to these tests by multiplying R by (x−u). If u' lies between 0 and u, the new moments and their differences give two nonoverlapping intervals (0,u') and (u',u), in either orientation. On each x(x−u) has fixed nonzero interior sign, so each contributes at least j−2 roots of P. If u' is further in the same direction than u, instead get j−2 new roots between u and u'; if u' is in the opposite direction, get them between 0 and u'. Those add to the original j−1 roots. In every case P has at least 2j−4>j distinct roots, contrary to its nonzero degree-≤j representation. Therefore the flat band's endpoint is invariant, completing the obstruction.

## 9. Logarithmic surplus

Let p≥10, q=floor(p/2), and h be the largest nonnegative integer satisfying 5·2^h≤q. Put σ(a)=dim F_a−a for 5≤a≤q. Strict growth makes σ nondecreasing, and §4 gives σ(5)≥0. Induct on a_i=5·2^i that σ(a_i)≥i whenever a_i≤q. If the band from j=a_i to 2j=a_(i+1) is not flat, the integer surplus increases by at least one. If it is flat, §§7–8 make F_(2j) invariant; by §6,
```
σ(2j) ≥ ceil(3(2j)/2)−3−2j = j−3 ≥ i+1 .
```
Thus σ(q)≥h. Substitution into the surplus inequality in §2 proves
```
s ≥ ceil(3p/2)−1+h.
```
Equivalently, the bound gains one further stage at p≥20, a second at p≥40, a third at p≥80, and so forth. The choice of hypotheses, proofs of sign and rank claims, and use of coordinate support permit arbitrary real abscissae and weights, including repeated nodes, exterior nodes, and vanishing weights. This does not claim attainment, literature priority, or a new leading coefficient. □
