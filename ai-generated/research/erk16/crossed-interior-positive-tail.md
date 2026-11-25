# Strictly interior crossed positive-tail weak-five: complete Gaussian signed-moment exclusion

## Statement and precise scope

Let w=X(1−X) and let B be a monic quadratic nonnegative at every base-field point of [0,1]. Its coefficients may lie in a real closure used for root selection. Suppose β=wB has a strictly positive six-node quadrature rule exact through degree eleven, with ordered nodes z<r<h<a<s<u in (0,1). Then
  I_{0,1}(wB(X−r)(X−s))<0.
This is a sign theorem for the second and fifth Gaussian nodes. It does not use any physical port, endpoint budget, or extreme-mark cutoff. It is enough that all the rational base samples used below have B≥0. The proof uses no held arithmetic, physical fixed fibre, numerical search, compiler, or resultant.

In the actual strictly interior crossed positive-tail two-change class the established Gaussian representation has exactly these hypotheses and q=B(X−r)(X−s). The paid left pair I_{0,u}(Xq)=I_{0,u}(X²q)=0 implies I_{0,u}(wq)=0. On the remaining tail (u,1), H=(X−r)(X−s)>0, B is nonnegative at all base samples, and its two possible zeros cannot exhaust a positive exact mesh. Thus I_{0,1}(wq)=I_{u,1}(wq)>0, a contradiction. On reflection the other actual endpoint pair supplies the same argument. Consequently the entire strictly interior crossed positive-tail two-change class is excluded. No conclusion about unrelated quartic phases or exterior labels is implicit.

## 1. Normalization, rank argument, and parity filter

Reflect if necessary. In y=2X−1, τ=y², write b=4B=A+τ−ky with A≥0, k=2(B(0)−B(1))≥0. Let E be normalized integration against w and ρ(f)=E(bf). Then
  m_j=E(τ^j)=3/[(2j+1)(2j+3)],    h_j(t)=t m_j+m_{j+1},
  v=ρ(y²)/ρ(1)=h_1(A)/h_0(A)=(7A+3)/[7(5A+1)],
  c=√v,    m=ρ(y)/ρ(1)=−k/(5A+1),    R=2r−1,    S=2s−1.
The positive six-node rule implies m²<v. Base positivity at y=1/2 gives k≤2A+1/2, hence −1/2≤m≤0. Assume toward contradiction that T=ρ[(y−R)(y−S)]/ρ(1)≥0. We have
  T=v−m²−(m−R)(S−m).
In particular if m>−d and m<e, with R<−d and S>e, then
  0≤T<v+(d−e)m−de.                                      (1)

On a two-dimensional subspace of polynomials P of degree ≤5, strict positivity of ρ[(y−e)P²] forces at least two of the six nodes strictly above e: otherwise a nonzero member vanishes at the at most one above-cut node, a contradiction by positive exact quadrature. Likewise ρ[(−y−d)P²] gives at least two nodes below −d. Thus these conclusions give bounds on S and R respectively.

For any t>0 and L of degree ≤2 in τ, the test polynomials P=(y±t)L(τ) have degree ≤5. Reflection symmetry of E gives
  ρ[(±y−t)(y±t)²L²] = E[(τ−t²){t A+(t∓k)τ}L²].         (2)
For the lower sign use (−y−t)(y−t)². Given any affine f,g with f(t²),g(t²)>0, put ℓ=f(t²)/g(t²). The threshold comparison
  E[(τ−t²)fL²]=ℓ E[(τ−t²)gL²]+(f'−ℓg')E[(τ−t²)²L²]       (3)
preserves any positive subspace whenever f'−ℓg'≥0. This needs no extension of a sign census and no integration of rational functions.

## 2. Two lower-node bounds and a mandatory lower skew

First take t=c and g=8A+τ. The reference quadratic form E[(τ−v)gL²] has two positive directions. Here is an exact certificate throughout A≥0. Let D=15015, so D(m_0,…,m_6)=(15015,3003,1287,715,455,315,231). For 0≤i,j≤2 set
  C_{ij}=D²[h_1(A)h_{i+j}(8A)−h_0(A)h_{i+j+1}(8A)].
This matrix is −D²h_0(A) times the reference form. Its determinant equals
  33632965656576·(13+239A−46061A²+673681A³+26882856A⁴+187002816A⁵+276243968A⁶).
It is strictly positive: 13+26882856A⁴≥32000A² and 239A+673681A³≥20000A² cover the only negative term when A>0. The value at zero is positive. For reproduction the anti-diagonal coefficient triples in ascending powers of A are (0,72144072,0), (−490776,−6870864,−82450368), (−446160,−8610888,−54966912), (−360360,−6932640,−37477440), (−288288,−5405400,−26906880). The reference form therefore has negative determinant and has a positive vector L=τ² since m_5/m_4=9/13 and m_6/m_5=11/15 exceed v≤3/7. Its inertia is two positive, one negative.

In (2) with t=c, the comparison coefficient in (3) is A(7c∓8k)/(8A+v). The lower sign yields R<−c for every k≥0. If k≤7c/8 the upper sign also yields S>c. But m²<v and R<−c, S>c imply T<0 strictly. Hence the hypothesis T≥0 forces
  k>7c/8.                                                   (4)

Also take d₀=13/22. The three-node τ rule for the even w-reference has nodal polynomial proportional to J(τ)=429τ³−495τ²+135τ−5. This follows from m_j or from the six-node symmetric w rule. J(d₀²)=518891/10307264>0, J(1/2)=−61/8, J(1)=64, so two nodes exceed d₀². Their cardinal span makes E[(τ−d₀²)L²] strictly positive. In the lower filter (2) the factor d₀A+(d₀+k)τ has positive value at d₀² and nonnegative slope, so (3) preserves both directions:
  R<−13/22.                                                 (5)

## 3. A coarse upper-node bound, without assuming positivity at algebraic extension sites

The even reference E also has its positive seven-node Gaussian rule, exact through degree thirteen. Let its monic nodal polynomial be P₇, proportional to yΦ(τ), Φ=715τ³−1001τ²+385τ−35. Orthogonality through degree six follows by parity and the displayed table for m_j. For e₀=9/25 the values of Φ at e₀²,1/5,1/2,1 are respectively −17605312/48828125, 192/25, −27/8, 64. Thus all three positive Gaussian sites p₁<p₂<p₃ exceed e₀. The other four sites are −p₃,−p₂,−p₁,0. Let U(y) be the monic product of their four linear factors.

For affine L and P=UL, the form ρ[(y−e₀)P²] is exactly Σ λ_i b(p_i)L(p_i)², where λ_i=ω_i(p_i−e₀)U(p_i)²>0 and ω_i are the w-reference weights. Here b(y)(y−e₀)P² has degree at most thirteen, so the seven-site rule is exactly paid even at its top degree. If b is nonnegative throughout the extension interval, the form is positive definite: a nonconstant monic quadratic nonnegative in the interval can vanish at no more than one interior site, and no nonzero affine vanishes at two sites.

The following finite argument works even if b is only known nonnegative at base-field samples. If k≥2, monotonicity and b(1)≥0 give b(p_i)>0. Otherwise the vertex t₀=k/2∈[0,1]. Put g=min_{i<j}|p_i−p_j|>0, λ_*=min λ_i, λ^*=max λ_i. Fix N with η=1/N²<min{g²/8, λ_*g⁴/(16λ^*)}. Such N exists since all these reference constants are fixed positive real-algebraic numbers. The rational j/N grid includes a site within 1/N of t₀, giving b(t₀)≥−η. Two sites p_j,p_l are each ≥g/2 from the vertex; hence b(p_j),b(p_l)≥g²/4−η. At the third site b(p_i)≥−η. Affine interpolation gives L(p_i)²≤(2/g²)(L(p_j)²+L(p_l)²). The two positive terms strictly dominate any negative third term by the choice of η, for every nonzero affine L. This proves strict positivity without declaring b nonnegative at any extension site.

Therefore S>9/25. By (1) with d₀=13/22,e₀=9/25 and m≥−1/2, straightforward rearrangement gives
  k<(831−245A)/889≤831/889<1.                               (6)
This first bootstrap does not use the older endpoint budget or any primitive test.

## 4. Exact upper reference improvement to S>8/15

Let e=8/15. From the previous sign brackets and Φ(4/9)=841/729>0, Φ(49/64)=−1602629/262144<0,
  9/25<p₁<√(1/5)<e<2/3<p₂,    7/8<p₃.
Write σ_i=ω_i U(p_i)². We first prove that Σσ_i(p_i−e)L(p_i)²>0 for every nonzero affine L. The weights are
  σ_i=constant / [(1−p_i²)∏_{j≠i}(p_i−p_j)²],
with the same positive constant. To see this directly, let P₆ be the monic w-orthogonal polynomial of degree six. Integration by parts shows (1−y²)P₇'+7yP₇ is proportional to P₆: it is even of degree at most six and its inner product against every polynomial of degree ≤5 vanishes by P₇ orthogonality. It is not identically zero, as is seen at a simple P₇ root. Integrating P₆ times the Gaussian cardinal P₇/[(y−p_i)P₇'(p_i)] gives ω_i P₆(p_i)=E(P₆²)/P₇'(p_i). Combining gives ω_i proportional to 1/[(1−p_i²)P₇'(p_i)²]. Finally P₇=U∏(y−p_j) proves the stated σ formula.

Since the first coefficient σ₁(p₁−e) is negative, express L(p₁) by affine interpolation from p₂,p₃. The rank-one subtraction from the two positive squares is strictly positive definite if and only if
  (1−p₁²)/(e−p₁) > (1−p₂²)/(p₂−e) + (1−p₃²)/(p₃−e).
This follows by the two-coordinate weighted Cauchy–Schwarz inequality (with its equality condition); inserting the σ formula cancels the squared node differences. The left ratio is increasing below e and each right ratio is decreasing above e. Our rational root bounds give a left side greater than 1632/325>5 and a right side less than 25/6+225/328<5. The reference assertion is thus strict.

By k<1 and p₁+p₂>1 the factors b(p₁)<b(p₂)<b(p₃) are strictly increasing on these three sites. In addition b(p₂)>b(1/2)≥0 because p₂>1/2 and p₂+1/2>1. Comparing each summand with b(p₂) times the reference form is directionally correct: the p₁ coefficient is negative, and the p₃ coefficient positive. Hence ρ[(y−e)(UL)²]>0 for all nonzero affine L. By the six-node rank argument,
  S>8/15.                                                   (7)

## 5. Final lower-node improvement and strict contradiction

Combining (5) and (7) in (1), since d₀>e and m≤0, yields v>d₀e=52/165. Consequently A<131/665<1/5, and (4) gives k>7/16. We must also have A>1/16: otherwise b(1/4)≥0 gives k≤4A+1/4≤1/2, but v≥v(1/16)=55/147 makes 7√v/8>1/2. In summary
  1/16<A<1/5,     k>7/16.                                  (8)

Put d=16/25. In (2) with the lower sign the factor is a positive multiple of τ+a*, a*=dA/(d+k)<1/8 by (8). For the fixed reference form E[(τ−d²)(τ+1/8)L²], the five consecutive anti-diagonals after multiplication by the positive integer 8·625·15015 are
  (−1682109, 974831, 928083, 744495, 590275).
They follow by h_i=15015(m_i+8m_{i+1})=(39039,13299,7007,4355,2975,2163), using 625h_{i+1}−256h_i. The determinant of the displayed Hankel matrix is −2356494634004992, and its last diagonal entry is positive, so it has two positive directions. Because a*<1/8, comparison (3) transfers both directions from τ+1/8 to τ+a*: the ratio at d² is positive and below one, so the square term is nonnegative. Hence R<−16/25.

Now d=16/25 and e=8/15 in (1) require the following strict positive number after multiplication by 5A+1:
  0<A+3/7−(5A+1)de−k(d−e)
   =229/2625−53A/75−8k/75
   <229/2625−109/1200=−151/42000.
This contradiction proves the strict Gaussian signed-moment sign and the physical positive-tail exclusion claimed at the start. All physical quadrature tests are of degree ≤11 against β. The two fixed reference rules and the normalized τ moments are algebraic identities common to the entire cone, not computations on a specialized physical profile.
