# Early marked a=6: uniform pencil gates and exact residual classes

Work over a characteristic-zero field, on the reviewed strict physical 19-row `HasOrder 13` tableau. Use the paid marked staircase, original first-escape mesh and the early mark ℓ already in E7 but not E6. Original seed is zero. Use [the paid staircase](PAID-STAIRCASE.md) and the [early two-head flag](A5-LOBATTO.md). Notation: c=A1, C=diag(c), F_j and E_j are the actual zero and tree flags, e(P)=P(c), D_n=U+span(w,Cw,…,C^(n−1)w), L the actual final row. Every pure head/core band vanishes at L. Here a=6, so E_j=V6 ⊕ D_(r+j−5) ⊕ Kℓ for j=7,…,10. Normalize the family as

    G = a J + b X F,    J = X j,
    F = 132X⁵−330X⁴+300X³−120X²+20X−1,
    j = 1716X⁶−5544X⁵+6930X⁴−4200X³+1260X²−168X+7,

with a,b,a+b nonzero, G(1)=a+b, b_L=b/[42(a+b)]. This uses the literal endpoint and the first six actual moment equations; coefficient b is not the stage weight vector. F and j are coprime by the established mod-43 unit check. Thus at **every nonzero root t of G**, F(t), j(t) and J(t) are nonzero. No separability or real-clock assumption is used.

## 1. Genuine lower-grade geometry without assuming a clean representative

In rank F7=8 the known exact two-head flag is F_(7+m)=D_(r+2+m) ⊕ e(K[X]≤m · J) for 0≤m≤3. In rank F7=7 its leakage at F7 is zero. Below use only its actual grade-seven leakage and the existing one-clock F7/F8 cut. Do not assume a corresponding slice cut in F10 or a direct chart at E11.

Take v∈F3 outside U. From the native marked construction, diag(v) preserves U, and the joint clock/v masks give a nonzero profile P deg≤3 and a head representative supported on M={v=P(c)}, with every off-M clock slice of v in U. That argument is earned for r≥3 by actual F8 adjacent-shift purity and the next E9 direct chart; r=2 already forces v∈U through two shifts in F5. The mechanism needs no pointwise closure of U. Since v,Cv,C²v lie in F5=D_r, comparison in the direct band extended through D_(r+2) shows v=u+T(c)w with deg T≤r−3.

To compare G T with Q P on enough actual clocks, use **escape clocks modulo U**, not arbitrary support rows. On a clock t where the slice w_t does not lie in U, the nonzero class of w_t has v=P(t) on its support by the mask just earned. In the same clock quotient, the literal mesh says G(t)[1_t]=Q(t)[w_t] on preterminal rows; the same identity can be projected modulo U+Kℓ on all rows. Similarly, the v identity gives [v_t]=T(t)[w_t], but to identify [v_t] with P(t)[1_t] one must restrict to the joint mask M. Such a restriction preserves U by the paid diagonal-invariance, yet it need not preserve ℓ information; all head slices vanish at L, and the mark is included in the quotient. On M, v is literally P(t)·1. Thus on the slice of an escape clock in M,

    G(t)[1_(clock t ∩ M)] = Q(t)[w_t],
    P(t)[1_(clock t ∩ M)] = T(t)[w_t]

modulo U+Kℓ. Head escape modulo U and modulo U+Kℓ agree here, since both w and U vanish at L. Multiply the first equality by P(t) and the second by G(t); then (G T−Q P)(t)[w_t]=0. The class [w_t] is nonzero, so the polynomial difference vanishes at each such clock. E9→E10 pays at least r+5 escape clocks: otherwise D_(r+4)+Kℓ is clock invariant and so is the full E9. The two degree bounds are 7+(r−3) and (r+1)+3, both r+4. Thus the actual scalar identity is

    G T = Q P,     deg Q≤r+1≤5.

This comparison does **not** borrow a clean physical support or the unneeded grade-ten slice lemma. In particular P and G/X cannot be coprime: if they were, gcd(P,G) would have degree at most 1, so G/gcd(P,G) of degree ≥6 would divide Q.

## 2. Cubic gate uniform over the full pencil

Use original preterminal two ports t,u at masks X and X(X−t), with t,u distinct and nonzero mesh roots. With I_k(v)=(primitive(X^k P))(v), the actual conditions from F6 and F7 are

    I1(t)=I2(t)=0,   I2(u)−t I1(u)=0,
    I3(t)=κ J(t),   I3(u)−t I2(u)=κ J(u).

Here F7 rank seven means κ=0; in rank eight it is the same highest-mask leakage by the original linear terminal evaluation (F6 vanishes at L). Both pivots are strictly preterminal: the residuals fit E6 and ℓ is not there. The original mesh forbids non-root pivots after the off-profile clock masks, as proved in [the earlier port argument](A5-LOBATTO.md#2-root-restriction-and-a-common-highest-mask-term-for-the-cubic-ports).

Set z=u/t. The first two small equations put P(tX) in the plane

    A0=X²−6X/5+3/10,   B0=X³−6X/5+2/5.

The mixed smaller equation at u reduces, after z²(z−1)² is removed, to a single nonzero relation; 4z−3 and 5z²+4z−6 have no common root. The nonzero P(tX) is therefore proportional to

    P_z=15(4z−3) B0−10(5z²+4z−6) A0.

Write D=(5z−2)(7z−6), N=100z⁴−460z³+819z²−672z+210. The two larger integrals, for this normalized polynomial at scales 1 and z, are −D/420 and z⁴N/420. Eliminate the shared κ without dividing by either integral. Since J(tz)/J(t)=z j(tz)/j(t) and the roots share the pencil parameter, the result is

    D·j(tz)+z³N·j(t)=0,
    D·F(tz)+z³N·F(t)=0.

Divide both by z−1, calling the F equation A and the j equation B. C=(B+7A)/t is a polynomial and vanishes as well. The primitive part of Res_t(A,C)/z^15 is a polynomial R0 of degree 50, with nonzero constant. The next subresultant, after cancelling z^15 and integer content, is S(z)t+T(z) with S,T degree 37. Thus any admitted pair has R0(z)=0 and S(z)t+T(z)=0. The exact certificate (mod 43) shows S a unit in the quotient by R0 with unchanged degree 50. Substitute t=−T/S there. Then

    H(X)=F(t) j(tX)−j(t) F(tX)

and P_z have Euclidean divisor degrees 3,2,1,0, with units as every leading coefficient. Therefore they are coprime after every characteristic-zero specialization. But H is proportional to (G/X)(tX) because t is a nonzero root of G and F(t)≠0. This contradicts the exact scalar G T=Q P conclusion of §1. Consequently **F3⊆U for every early a=6 tableau in either F7 rank**. It follows r≤3 and dim F4=4 by the reviewed rank growth and incoming/outgoing clock Hermite, exactly as in the a=5 argument.

## 3. Genuine F4 head and all clean pure-factor exits

The flat F4–F6 interval now gives the same invariant core U by chain drop and yields an actual w∈F4. For r=3 one also has Cw∈F4. Clock-slice locality in F7/F8 earns U²,U·w⊂U (F3×F4 when r=3 since then U=F3, F4×F4 when r=2). Use the reviewed disjoint representative without changing any bands; terminal remains zero. Consider any exact clean factorization G=RQ with w=R(c) on its nonzero support, deg R≤4, Q from the genuine mesh (deg≤3 for r=2, deg≤4 for r=3). Degree seven forces R quartic or cubic. Match any polynomial mask against the core by its indicator and on the head using the exact amplitude. The first mismatch for each masked profile fits E6 and is strictly preterminal by ℓ∉E6. It lies off core/head, the masked amplitude is nonzero, and its clock is a root of G by the actual mesh. The causality transport in F6 has zero off-band value. In F7 the same calculation gives shared leakage κ times the leading mask coefficient, from the terminal evaluation after all lower masks land in F6.

- **Cubic R** is possible only in radius three. Use masks X and X(X−t); their degree-two transport really stays in F6, since Cw∈F4 implies C²w∈F5 and degree-two times cubic has degree≤5. Degree-three transport is in F7. The cubic test in §2 applies literally with P=R, which has degree-three overlap with G (and at least two with G/X).
- **Quartic R with R(0)=0:** use first 1 and then X−t, and put P=R/X. Their pivots are nonzero because the mismatching masked R value is nonzero. Masks through degree one transport in F6 and quadratic masks in F7. The same five equations of §2 hold with the indicated I_k of P, and G/X shares all of P.
- **Quartic R with R(0)≠0:** first X and second X(X−t) have distinct nonzero pivots t,u, with Q(t)=Q(u)=0 and Q(0)=0. Since deg Q=3, these are exactly its three roots. For z=u/t, H(X)=F(t)j(tX)−j(t)F(tX) has roots 1,z, and

      W(X) = (polynomial quotient of H by the monic divisor (X−1)(X−z))/t²

  is a nonzero scalar multiple of R(tX). Its coefficients are polynomials in t,z, since the quotient only uses coefficients of H from X² upward. F6 on the first X mask, F7 on X² at t and X(X−t) at u, after eliminating their shared leakage, give

      A = primitive(XW)(1) = 0,
      M = H(z)/[(z−1)t] = 0,
      B = F(tz)·primitive(X²W)(1)
            − (F(t)/z)·primitive((X²−X)W)(z) = 0.

  All expressions here are polynomials; use primitive integer parts of A,M,B. The resultant Res_t(A,M) has primitive degree 40 in z, and the penultimate subresultant is linear in t. Modulo 101 its leading coefficient is a unit in the monic degree-40 quotient, and the third polynomial B at the recovered t is another unit. This contradicts B=0 uniformly.

Both certificates use the same specialization argument. The raw Sylvester subresultants vanish at every pair with a common t-root. Cancelling only integer contents and the nonzero z power preserves that fact. Localize the integers at the certificate prime; the primitive resultant's leading coefficient is a unit, hence its monic quotient is finite free of rank 50 or 40 over that local ring. A residue unit lifts to a unit by the determinant of multiplication on this free algebra. This applies to the recovered-t denominator, then the Euclidean leading coefficients or the third polynomial. All admitted characteristic-zero pairs define a specialization of that quotient. In particular the proof neither assumes a parameter is generic nor only verifies nonspecial real roots.

## 4. Resulting exact residual classification

**Radius two.** Actual E8 and F8 give w²=e(P)+R(c)w+u+αℓ, deg P≤6, deg R≤4, P(0)=0, α=−P(1), and μ0,…,μ4(P) equal. The genuine head is in F8 here, so all five probes are paid. Also e(G)=Q(c)w+v+γℓ with deg Q≤3. On the disjoint head and after absorbing core/mark terms the exact transport is

    e(G−RQ)w−e(PQ) ∈ U+Kℓ.

If the degree-seven coefficient of G−RQ cancels, the direct E10 chart and Euclidean division of PQ by G give G|PQ: the quotient's degree is at most two, so its mesh evaluation sits in the paid D7+Kℓ; the remaining polynomial of degree≤6 has zero component there. Let H_n be the monic degree n orthogonal polynomial for the rational weight X(1−X). Then P/X lies in span(H4,H5), and monic G/X is H6+δ H5. Gram nonsingularity over Q gives the monic three-term recurrence H6=(X−a₀)H5−b₀H4 with nonzero b₀, and neighboring polynomials are coprime (iterate the recurrence). This extends to every characteristic-zero field. Thus unless P=0, gcd(P/X,G/X) has degree at most one: modulo G/X, eliminate H4 to get an affine polynomial times H5, which is a unit. After cancelling X from G|P Q, Q of degree at most three cannot cover the degree-six G/X. Hence P=0. The next measured tree jump pays seven distinct head clocks, enough to turn the now-degree≤6 interpolation G=RQ on head into exact factorization. The pure-factor gate excludes it.

If the top does not cancel, transport solves for the new head power C⁷w in E10; the e(PQ) term fits by the same Euclidean division. Hence E10 is C-stable and a unital pointwise algebra using the square relation, with 3 core atoms and singleton L. It contains and distinguishes precisely the original 14 different preterminal noncore (c,w) pairs, by rank 18 and the general finite coordinate class lemma. The eliminant (G−RQ)G−PQ² has degree 14; the generic checked selector obstruction applies to E9's H(c)+S(c)w (deg H≤6, deg S≤5). Its annihilator λ on the 18 classes is nonzero at all 14 pairs and zero on core and L. On classes E8 has annihilator span(λ,cλ), and βw=κ cλ by the grade 4+8 probe and the true origin pair (0,0) where λ is nonzero. If P≠0, κ cannot vanish: then all head masses vanish, the clean noncore clocks are common roots of G and P (at most two distinct by the gcd bound), core masses are zero, and the quadrature needs at least six distinct off-one mass clocks. Thus all nonzero-clock preterminal noncore labels are head and carry nonzero β. If P=0 and top does not cancel, there are at most seven distinct head clocks (roots of G−RQ), with exactly one nonzero amplitude R(c) per clock. The 14 noncore labels therefore force exactly seven head clocks and all seven distinct clean roots of G; at nonzero clean clocks βw=κ cλ forces κ=0. This is a different fixed-amplitude residual.

**Radius three.** w,Cw∈F4 gives w²,Cw²,C²w²∈F8. Marked adjacent-shift purity gives w²∈D6. The direct E9 chart implies D7∩F8⊂D6, because the pure D7 band in E9 has no V6 or mark component. Applying it twice, Cw² and C²w² are also in D6. In disjoint coordinates w²=R(c)w, and the independence of the eight paid head powers in E10 bounds deg R≤3 by the second shift. The genuine mesh has deg Q≤4. The measured E9→E10 jump pays at least eight head clocks, so the degree≤7 comparison gives exact G=RQ. The uniform cubic pencil gate excludes it. This is valid whether F7 has rank seven or eight.

It remains only the radius-two top chart. E10 has 18 classes among 19 actual rows, and its original annihilator is exactly the line generated by the original reflected quadratic row ρ1. Its penultimate physical component is −b_P(1−c_P)²≠0, so the sole duplicate pair has the penultimate row as its later representative (never L). The final-three causal theorem closes it; see [Final three classes](FINAL-THREE.md). No ordinary terminal visibility assumption is used.

## Evidence

[The exact pencil certificate](certificates/early_a6_pencil_certificate.py) checks all rational normalizations and both Sylvester/subresultant finite-free certificates in exact SymPy arithmetic. Output:

    cubic pencil: degree-50 chart mod 43; Euclidean units 3, 2, 1, 0
    quartic pencil: degree-40 chart mod 101; third equation is a unit

No Lean compiler, held or legacy inputs, or numerical RK search was used.
