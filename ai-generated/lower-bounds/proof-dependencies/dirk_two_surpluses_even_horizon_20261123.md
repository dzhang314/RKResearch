# Two compulsory surplus dimensions across a forward DIRK doubling window

**Theorem, for independent review.** With arbitrary real lower triangular A, including zero diagonals, arbitrary repeated/exterior abscissae, and arbitrary signed or zero weights, suppose the method has classical order p. If d≥5 and p≥2d+2, the ordinary forward zero-profile ranks satisfy
    f_(2d) ≥ f_(d−1)+d+3.
There are at least TWO surplus dimensions beyond the 2d−(d−1)=d+1 ordinary unit steps. The ubiquitous first-surplus statement is f_(2k)≥f_k+k+1 for k≥4 and p≥2k+2, in dirk_incoming_hermite_unconditional_dyadic_gain_20261123.md. The new proof allows one intervening surplus to occur *anywhere*. It uses the ERK one-head interpolation idea of erk_universal_grade_eleven_second_surplus_20261123.md, but it needs two genuine implicit pivot refunds and has a different early/late grade allocation. It is a theorem about the forward, multiplicatively closed stage calculus, not unqualified use of multiplication on arbitrary reflected marked rows.

Conventions: E_j,F_j are the ordinary numerical stage and pure (zero formal polynomial) spaces through grade j, tree order minus one; f_j=dim F_j. C=diag(c), c=A1. A induces JH(x)=∫₀ˣH, C induces xH and coordinate products multiply profiles/add grades. The residual R=CA−AC−A² is lower triangular, maps E_j into F_(j+2), and has diagonal −a_ii²; this uses xJ−Jx=J². Every F_j with j≤p−1 is killed by the output. No single-valued polynomial profile at high grade is assumed.

**Inputs.** Strict forward growth costs at least one in the range used here. If F_j is C-invariant, its incoming gain from F_(j−1) is at least floor((j−1)/2). For ANY C-invariant U⊂F_j, f_(j+1)≥dim U+floor(j/2). Both apply within p−1. Here is the shared direct verification of the second version. Choose r=floor(j/2) nonzero chronological detections of 1 modulo U, with earliest supporting prefix row λ_i killing U and normalized at its node on 1. There are enough: every aggregate nonzero-weight node detects 1, and a squared nodal polynomial times x forces at least floor(p/2) nonzero such nodes. At the selected node values a_i use H=x∏_(i=1)^r(x−a_i), including the final factor. For every T of degree ≤r−1, nodal localization assembles u∈U coinciding with H(c)T(c) up through the final detecting row inclusive, since it vanishes on every already-detected node and on 0, and before failure a nodewise prefix match exists on each other node. Thus the r functionals λ_i on F_(j+1) attain the vector of primitive values (∫₀^{a_i} HT) modulo the contributions λ_i A u, themselves from F_(j+1); all λ_i kill U. These vectors have rank r by sign changes across the r sorted gaps of {0,a_1,…,a_r}. The primitive residual fits since deg(HT)+1≤2r+1≤j+1. For the incoming version use U=F_j, 2r+1≤j, and λ_iA kills F_(j−1), as proved in the cited note. In particular a unit outgoing gain at j≥4 forbids invariance of F_j, and a unit incoming gain at j≥5 forbids it too.

**A unit band.** If the dimension gain after F_j is one and F_j is not C-invariant, the self-adjoint compression of the diagonal C gives its maximal C-invariant summand U and a single head w:
    F_j=U⊕w P_(f_j−dim U−1)(c).
Each physical nodal restriction of w is orthogonal to U there. To verify, project C to F_j; its one-dimensional escape has a covector v. The orthogonal complement of v,Tv,… for the symmetric compression T is exactly the maximal invariant space. In the remaining cyclic space of dimension r take w perpendicular to v,…,T^(r−2)v. Its first r true C powers equal those of T (through exponent r−1); their antidiagonal pairing with the powers of v proves independence. In a subsequent string of unit growth and noninvariance these head powers successively span each entire space. If the last F_H is still noninvariant, the number n of distinct physical nodes having a nonzero head projection is at least f_H−dim U+1. In any of the band spaces, a vector supported on a single node must belong to U: its head coefficient polynomial cannot vanish at the other n−1 nodes unless it is zero (including the last space). If a real diagonal multiplier sends the first space into a later space in that band, it preserves U by applying the last observation nodewise. It therefore also preserves U-perpendicularity. Comparing the successive polynomial coefficients of the products with w,Cw,…,C^(r−1)w then represents that multiplier on the nonzero head coordinates by a polynomial of degree at most the number of additional unit steps. Consecutive comparisons are polynomial identities because their degrees are below n.

**Putative one-surplus chart.** Write b₀=d−1 for an early grade (not an output weight), H=2d. Applying the previously verified first-surplus theorem at k=b₀ shows there is already one surplus by grade 2b₀=2d−2. If the claimed conclusion fails, strict growth makes all steps from b₀ to H single, except exactly one double gain ending at some t with d≤t≤2d−2. Every late F_j, t≤j≤H, is noninvariant, by unit outgoing growth except at H, where the incoming test applies. Write u=dim U for the late invariant summand; throughout the late band
    F_j=U⊕w P_(f_j−u−1)(c),    n≥f_H−u+1.
We will construct a nonzero polynomial P of degree at most d and f∈F_d agreeing on every late head coordinate, with diag(f) preserving U. In addition, if Q(C)(P(c)−f) belongs to U for either of the masks below it has a pure representative at grade ≤d.

*If t=d*, choose any f∈F_d outside U. Multiplying F_t by f lands in F_(2d). The multiplier rule just proved gives the desired P of degree at most H−t=d, and diag(f) preserves U. P is nonzero: some nodewise head projection of f is nonzero because f∉U, so f is nonzero at some nonzero coordinate of w. Here U⊂F_d directly. This case does not assume that F_(d−1) is noninvariant or that its head has two powers.

*If t≥d+1*, F_(b₀) and F_(t−1) are both noninvariant: the former has a single outgoing step and b₀≥4; for the latter the incoming step is single, and t−1≥5. The intervening band is noninvariant as well. Write F_(b₀)=U₀⊕gP_(r−1)(c), where u₀=dim U₀ and r=f_(b₀)−u₀≥1. Its power extension
    V_t=U₀+gP_(r−1+t−b₀)(c)
has dimension f_t−1 and lies in F_t, by expanding the single gains through t−1 and taking the nontrivial C escape from F_(t−1). Maximality gives U₀⊂U. Also V_t⊄U: otherwise the incoming-to-next estimate for U would give f_(t+1)≥f_t−1+floor(t/2)>f_t+1 since t≥6, but that step is single.

Write g=wL(c)+e, e∈U; L≠0 follows since V_t⊄U. All C powers of e lie in U. Comparing polynomial coefficients of g,Cg,…,C^(r−1+t−b₀)g on the late nodes gives
    deg L ≤ (f_t−u−1)−(r−1+t−b₀) = 1−δ,    δ=u−u₀∈{0,1}.
If δ=0, e=0 by nodewise orthogonality. If δ=1, L is a nonzero constant; U⊖U₀ is one C-invariant line at a single node α, and e lies in that line. Away from this exceptional node U and U₀ coincide locally.

For 0≤j≤2r−2, C^j g²∈F_(2b₀) by ordinary products. Since 2b₀≥t this is a late band space. Comparing the consecutive coefficients as before shows the head coefficient q of g² has
    deg q ≤ (f_(2b₀)−u−1)−(2r−2) = b₀+2−r−δ.
At an unaffected node, multiplying g into any local vector in U=U₀ lands in F_(2b₀) and is local, hence remains in U. Orthogonality of g to U there consequently implies g² is also orthogonal to U there. On the late head at any unaffected node this proves q(c)=L(c)g coordinatewise, since g=wL there and g²=wq there. The polynomial q cannot vanish identically: L does not vanish at all unaffected effective nodes, having degree ≤1, at most one exceptional node being removed, while n≥f_H−u+1≥4. Set B=1 for δ=0 and B=x−α for δ=1. Then
    P=Bq,    f=B(C)L(C)g.
These are equal on all late head coordinates, including the entire exceptional node where both are zero. We have deg P≤b₀+2−r≤d and deg(BL)≤1. Even if r=1, f∈F_(b₀+1)=F_d; no early second head power is needed. The preceding local argument proves diag(f) preserves U away from α and it is zero on α, so it preserves U everywhere. If Q(C)(P(c)−f) belongs to U, it lies in U₀⊂F_(b₀), because the possible extra orthogonal line at α is killed coordinatewise.

**Both DIRK diagonal refunds.** Let Q=x or Q=x(x−a), and set z=Q(C)(P(c)−f), with formal profile QP and grade at most d+deg Q. If z∉U, take the first prefix at which z cannot be matched by U, ending with index i. The commuting diagonals C and diag(f) both preserve U, so U is localized at their joint coordinate blocks. There is a row λ supported on the failing joint block within this prefix, killing U and not killing z. The value of z on this block is a single nonzero constant, so normalize λ1=1. No head coordinate occurs in this block since z vanishes there; thus λ kills the whole F_H. Take u'∈U matching z on the strict earlier prefix. The vector z−u' is zero strictly before i and nonzero at i. Both Rz and Ru' belong to F_H: their grade bounds are respectively d+deg Q+2≤d+4≤2d and t+2≤2d (the last two spare grades matter). Therefore
    0=λ R(z−u')=−a_ii² λ_i(z−u')_i.
The pivot product is λz≠0, so a_ii=0. For every polynomial T with deg T+deg Q≤d−1 we have A T(C)u'∈F_(t+1) since U is C-invariant; λ kills it. The zero pivot and the matching strict prefix show λ A T(C)(z−u')=0. As the primitive of T(C)z is the scalar J(TQP) modulo F_H, we get at the failing node v=c_i
    ∫₀ᵛ T(x)Q(x)P(x) dx=0,       Q(v)≠0.
This argument refunds each mask separately at its own index, with the true diagonal; it never treats all DIRK rows as explicit.

If z∈U, the earlier construction gives it a pure representative through d. Subtraction from its QP representative gives a zero numerical pair of grade ≤d+deg Q with profile QP. For the first mask Q=x this would yield ∫₀¹xP²=0, since p−1≥2d+1. It follows that the first mask has a failing node a≠0 at which the xP moments through degree d−2 vanish. Use the second mask Q=x(x−a). If it fails at a node v, then v differs from 0,a and the x(x−a)P moments through degree d−3 vanish there. If its vector instead lies in U, the zero numerical pair supplies the same vanishing with v=1, in fact through d−1 since (d+2)+(d−1)≤p−1.

When v≠a, x(x−a)P has these first d−2 zero moments at both a and v, including the ones at a from the first mask. Subtract primitives on the two sorted gaps of {0,a,v}. The factor x(x−a) has fixed strict sign within each open gap. Thus P must have ≥d−2 distinct sign-changing roots on each, giving at least 2(d−2)>d roots since d≥5. This is impossible. In the remaining case a=v=1 the second vector lay in U, so the last two affordable output tests give the missing xP moments of degrees d−1 and d (use the relation m_(j+1)=m_j through j=d−1). Therefore ∫xP²=0 again. This contradiction proves the theorem.

**Rank replay, not a new numerical minimum.** Initial ranks f₂=ε, f₃≥1+ε, ε=1 if g=Ac−c²/2 is nonzero, zero otherwise. For p≥12, f₁₀≥10+ε and it grows strictly thereafter. At higher d the relative estimate is usually stronger than propagating this absolute floor. At actual orders 12–20 the following standard ledger counting procedure, without other special branch exclusions, gives:
~~~python
for p in range(10,21):
    ans=[]
    for e in (0,1):
        f=[0,0,e,1+e]
        for j in range(4,p):
            z=f[j-1]+1
            if j%2==0 and j>=8 and j+2<=p:
                z=max(z,f[j//2]+j//2+1)
            if j%2==0 and j>=10 and j+2<=p:
                z=max(z,f[j//2-1]+j//2+3)
            f.append(z)
        v=[]
        for j in range(2,p):
            h=min(j,p-1-j,(p-1)//2) if e else min(j,p-j,p//2)
            equality_bonus=int(j<=p-3 and 2*j+e<=p-1)
            v.append(f[j]+h+1+max(0,p-3-j)+equality_bonus)
        ans.append(max(v))
    print(p,ans)
~~~
These (anchored C(2), g≠0) floors are (11,12),(13,13),(14,15),(16,16),(17,18),(19,19),(21,21),(23,23),(24,25),(26,26),(28,28) at p10…20. Relative to the prior dyadic replay the generic C(2) floor at p20 improves 27→28, meeting but not exceeding the existing unrestricted bound 28. The separate specialized arguments at p14,15,18,19 remain stronger. There is no new current unrestricted integer ledger endpoint.
