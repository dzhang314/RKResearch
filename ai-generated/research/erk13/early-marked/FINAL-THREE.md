# The final three supported classes: closure of the early marked seams

This is a proof in ordinary characteristic-zero field algebra on the reviewed physical 19-row strict `HasOrder 13 A b` tableau. It does not call a Lean compiler. It uses the exact marked staircase and the finite class conclusions in [the Lobatto argument](A5-LOBATTO.md) and [the pencil argument](A6-PENCIL.md). No positivity or ordering of tableau clocks or weights is assumed. Chronology always means the original row order.

## 1. A finite causal last-three theorem

Let B be a strictly lower triangular matrix on an ordered finite set of classes. Let β, y, λ be class covectors or functions over a characteristic-zero field. Use pointwise multiplication and define

    R_k = (k+1) Bᵀ(β y^k) − β y^(k+1)   for k=1,…,5.

Assume:

1. βy is nonzero, λ is nonzero on at least three classes, and R₁ is a nonzero scalar times λ.
2. Each R_k is λ times a polynomial in y of degree at most max(0,k−2). In particular the first two are constant multiples of λ, the third is affine, and every row vanishes where λ vanishes.
3. Bᵀλ is λ times an affine polynomial in y. For every Y in the field, Bᵀ[(y−Y)λ] is λ times a polynomial of degree at most two.
4. For two different classes i,j with λ_i λ_j≠0 and the same nonzero reflected clock y_i=y_j, the ratios β_i y_i/λ_i and β_j y_j/λ_j cannot be equal and nonzero.

These hypotheses are inconsistent.

**The support must be the union, not merely λ-support.** Let S be the union of the numerical supports of λ and βy (including signed nonzero entries). There are at least three classes in S. Suppose one of the final three classes i of S has λ_i=0. Then β_i y_i≠0, and only at most two subsequent classes can contribute to any R_k(i) with k≥1. Since all five rows vanish at i, the scaled nodes x_j=y_j/y_i and signed weights β_j B_(j,i)/(β_i y_i) on the later contributing sites satisfy

    Σ_j [β_j B_(j,i)/(β_i y_i)] x_j^k = 1/(k+1),    k=1,…,5.

Let H be the monic polynomial of their distinct nodes, of degree d≤2 (the empty set gives H=1). The shadow measure annihilates X^(m+1)H for 0≤m≤d, and those tests have degree at most five and zero constant. Hence the rational moment functional with ∫₀¹X^n=1/(n+1) annihilates X·X^m H for 0≤m≤d. Its weight-X moment matrix is nonsingular: it is positive definite over the reals and has rational entries, so its nonzero rational determinant stays nonzero over every characteristic-zero field. It would force H=0. Therefore the final three classes of S all lie in λ-support. This uses k=1,…,5, not k=0, and allows active reflected-zero classes anywhere.

Write those three classes in reverse order i₀,i₁,i₂. At i₀ there are no later weighted contributors, so R₁(i₀)=−β_(i₀)y_(i₀)² is nonzero. Put Y=y_(i₀)≠0 and f_*=β_(i₀)Y/λ_(i₀)≠0. On λ-support set x=y/Y and f=(βy/λ)/f_*. Define the strictly upper triangular operator there by entries

    T_(i,j) = B_(j,i) λ_j/(Y λ_i).

For the final three classes there are no later contributors from outside λ-support. Dividing R_k(i) by λ_i Y^k f_* therefore gives there (k+1)T(x^(k−1)f)−x^k f. The first two normalized right sides are both −1 by evaluating at i₀. The third right side is −1+g(x−1), for an unknown g. The adjoint hypotheses give T1=a(x−1) for a scalar a, since T1 is affine and zero at i₀, and T(x−1) is a polynomial of degree at most two on all λ-support.

Let x_(i₁)=s and f_(i₁)=h. Its only later contributor is i₀, and T_(i₁,i₀)=a(s−1). Thus

    2a(s−1)−s h = −1,      3a(s−1)−s² h = −1.

If sh=0, these equations are inconsistent. If s=1, then h=1, which repeats the same nonzero ratio as i₀ at the same nonzero y and violates hypothesis 4. Otherwise subtract the equations and cancel s−1 to get sh=a; substitution gives a=1/(3−2s), with denominator nonzero. The third row at i₁ now gives g=−a(s−1).

Let x_(i₂)=v and f_(i₂)=ξ, and let p=T_(i₂,i₀), q=T_(i₂,i₁). They obey

    p+q = a(v−1),
    2(p+qa/s)−vξ = −1,
    3(p+qa)−v²ξ = −1,
    4(p+qas)−v³ξ = −1−a(s−1)(v−1).

No assumption v≠0 is needed. Set Δ=3−2s, P=Δp, Q=q/s, Z=Δξ. The fraction-free system is

    P+ΔsQ = v−1,
    2(P+Q)−vZ = −Δ,
    3(P+sQ)−v²Z = −Δ,
    4(P+s²Q)−v³Z = −Δ−(s−1)(v−1).

The augmented 4×4 determinant is exactly 6v(s−1)(s−v)²(v−1). A stronger division-free compatibility follows directly: eliminate P and vZ by subtracting v or v² times the second equation from the third or fourth, then eliminating P with the first. With A₀=2sv−3s−v and B₀=2sv²−6s−v², the two resulting equalities are

    2(s−1)A₀ Q = 2(s−v)(v−1),
    2(s−1)B₀ Q = (s−v)(v−1)(2v+3).

Cross multiplication and 2B₀−(2v+3)A₀=3(v−s) give 3(s−v)²(v−1)=0. Therefore v∈{1,s}. This includes and excludes the entire v=0 degeneracy, since 1 and s are nonzero.

Finally T(x−1) vanishes at x=1 and x=s: at i₀ it has no later terms, and i₁'s sole later term is multiplied by x_(i₀)−1=0. It therefore vanishes at i₂, which has one of these same clocks. At i₂ its value is q(s−1), so q=0. Then p=a(v−1), and the first shifted residual shows ξ=1 if v=1, or ξ=a/s if v=s. Each is exactly the nonzero f of the later class with that same nonzero clock. This violates hypothesis 4. Thus the causal theorem is proved without divisions by v, v−1, v−s, s+1 or s−2.

## 2. Original-row proof of the compression and all paid degrees

In each **early** residual configuration, E10 is exactly the pullback of all functions on 18 classes. Its single duplicate among 19 physical rows is (I,P), where P is literal penultimate and I<P is its class's first representative. Final L is a singleton and ℓ∈E7. The clocks c and y=1−c are functions of the classes, and β is the sum of the original weights in each class. The first representatives are ordered by their actual indices. Define B by restricting A on class functions to those first representatives. It is strictly lower triangular, since a destination's earlier physical column belongs to a class whose first representative precedes the destination. No forward-invariance of all E10 under A is used.

Let λ span the class annihilator of the actual E9 (dimension 17). The only discrepancy of A on class functions from lifting B back is at P. Its row functional is D=(A_(P,·)−A_(I,·)) on those functions and kills E9 because A E9⊂E10. Thus D=dλ. In particular for every k≥1, the push forward to classes of the original paid row ρ_k satisfies the exact formula

    push(ρ_k) = R_k + (k+1)b_P y_P^k d λ.

This is an equality on all class functions: in the sum of the original weights times A on them, all representative values agree with B except at physical P. The weights with which a correction is paid are therefore the original b_P y_P^k, never the aggregated class weight.

The precise native budgets are ρ_k∈ann(E_(11−k)), for 1≤k≤5. Also ρ_k(L)=0 for all these k: A has zero last column and y_L=0, so the displayed definition of ρ_k has zero there. Therefore each row also annihilates the chosen marked grade E_(11−k)^+=E_(11−k)+Kℓ. For k=1, the push forward vanishes on every class function since E10 is the whole class space. Thus R₁ is a multiple of λ, and it is nonzero: original bushy quadrature gives Σβ y=1/2, so at the latest class with βy≠0 strict B gives R₁(i)=−β_i y_i²≠0. (This also earns d≠0 instead of assuming it.) For k=2 the push forward lies on the λ line. For k=3,4,5 the pushed row lies in the annihilator of E8, E7, and E6^+, respectively.

Measured marked ranks give codimensions 1,2,3,4 for E9,E8,E7,E6^+ in the class space. The corresponding annihilators are exactly

    K·λ,  span(λ,yλ),  span(λ,yλ,y²λ),  span(λ,yλ,y²λ,y³λ).

Indeed each displayed row is paid by the ordinary tree clock step and yℓ=0 (hence the same step on the marked flag), and they are independent since λ is supported at ≥4 distinct clocks as proved below. Adding the exact correction dλ does not change these degree bounds. Finally A E8⊂E9 and A E7⊂E8 on genuine tree grades imply the same for B on class functions. Thus Bᵀλ∈ann(E8), and Bᵀ[(y−Y)λ]∈ann(E7), giving both adjoint polynomial bounds of the causal theorem. These statements require no terminal visibility hypothesis and no k=0 folded equation.

## 3. Every identified early packet earns the ratio condition

**Radius-two high square (a=5 and a=6, including a=6 P=0).** The 18 classes are the three live-core atoms, the singleton L, and 14 different original preterminal noncore pairs (c,w), where w is the genuine disjoint F4 head. Core and L selectors are already in E9, so λ vanishes there. On the 14 pairs the quadratic square bounds every clock fibre by two, and the saturated degree-fourteen eliminant and generic selector lemma show λ nonzero on all 14. For a=5 the polynomial observer has degrees (5,6) and G degree 6; for a=6 the observer has degrees (6,5) and G degree 7. In both cases H·Q+S·G has degree≤12 and the generic no-singleton argument applies, including Q identically zero. Thus λ's support contains at least seven distinct clocks.

The class covector βw annihilates E8 by the genuine F4×E8 product and paid order-13 probe (stage grade 4+8=12). Hence it is in span(λ,cλ). The true origin pair (0,0) is noncore, w=0 there, and its λ-coordinate is nonzero; consequently βw=κ cλ for a scalar κ. For distinct classes with same nonzero y and same nonzero β y/λ, this identity gives the same w since (βy/λ) w=κ c y. They would be the same pair, impossible. This argument does not need κ≠0, a lower bound on physical head clocks beyond the established case classification, or exclusion of a zero ordinary clock.

**Optional radius-three a=6 cut using only one pure square shift.** If one stops one pure square shift earlier, the residual radius-three chart has exactly eight distinct head clocks with one nonzero amplitude each, seven distinct preterminal clean-root clocks with w=0, two core atoms and the true singleton L. All core and head class masses vanish (core indicators and the nine F4 clock probes). A singleton selector at any head class is impossible in E9: restricting a proposed observer H(c)+S(c)w to the seven distinct clean roots kills H, since deg H≤6; its other seven head values then kill S, since deg S≤6. Hence λ is nonzero on all eight distinct head clocks. Any nonzero βy comes only from a clean class, because y_L=0, and distinct clean classes have different clocks. Thus the same nonzero-y ratio cannot repeat. No assumption is made about λ on the clean classes; the union argument explicitly handles its zeros there.

All hypotheses of §1 are now earned in every listed early residual. Together with the exact a=5 Lobatto exits and the a=6 pencil exits, this excludes the entire **early marked branch** (literal final coordinate in E7). It is not an independent proof of any smaller unrelated class branch or of the late/ordinary cases.

## Evidence

[The exact scalar certificate](certificates/early_class_tail_certificate.py) verifies both the exact augmented determinant and the stronger division-free residual by integer polynomial expansion. The standalone [Lean draft](RKCert/ReviewedNative/NativeFinalThreeScalar.lean) is a standalone, uncompiled source draft for the fraction-free four-equation lemma. There is no arithmetic specialization to particular tableau clocks and no use of held inputs, cluster, or publication.
