# Order twelve: replace the exceptional ghost determinants by paid chronology

## Scope and interfaces

This is a source-only replacement for the arithmetic gates in the known seventeen-row equality chart for explicit order twelve. It does not run Lean, a solver, the older held charts, or any repository operation. It uses the chart structure and proves every remaining arithmetic gate once that structure has been transported to a field in which 12! is a unit. The original characteristic-zero proof is documented in `../proof-dependencies/pass0045_q6_even.md` and `erk_characteristic_zero_order12_eighteen_stage_finite_audit_20261123.md`. Its current native verification and smaller backward proof are described in `../../lean/ORDER_TWELVE.md` and `../../lean/ORDER_TWELVE.md`. The separately audited pure nonzero-at-origin branch in characteristic 283 is `ORDER-TWELVE-CHAR283.md` with the direct-numerator erratum.

Let K be a field of characteristic zero or characteristic greater than twelve, and suppose an explicit seventeen-row order-twelve tableau. Write c=A1, C=diag(c), F_j for pure rooted numerical defects of grade through j, E_j for numerical rooted pairs through j, and J for the formal antiderivative with zero constant term. The standard chart has
  E_j=P_j(c)⊕F_j for j≤6,
  F5=U+w P_(r−1)(c), F6=U+w P_r(c),
  E7=P6(c)⊕(U+w P_(r+1)(c)),
  E10=P6(c)⊕(U+w P_(r+4)(c))=K^17,
where U is C-invariant, dim U=5−r, with at least r+5 distinct effective head clocks. A numerical pair (z,p) of grade j≤5 satisfies (Az,Jp) at grade j+1. The terminal coordinate e_s is in E6 and has profile
  f(x)=xD(x),  D(x)=132x^5−330x^4+300x³−120x²+20x−1.
The terminal clock is 1, F6 vanishes at the terminal row, and Ae_s=0 by strict causality. F5 and all its clock shifts vanish there.

The cheap F2 multiplier test is universal once the chart is available: for a degree-at-most-two fitted head the x,x²,x³ causal tests are three linear moments at the same nonzero clock, a paid size-three x-weighted Hankel. This forces F2⊂U and r≤4; r≥2 by the established strong Hermite rank gain. The necessary grade-eight leakage controls are also paid: F8 last-zero polynomial components lie on x(1−x)D4 for the corresponding monic Jacobi polynomial. Comparing two consecutive shifts modulo the monic scalar mesh (x−1)f, the D3 coefficient of xD4 is the ratio of the nonzero Jacobi square norms of D4 and D3. This is an algebraic identity, not positivity for unknown K coefficients; the two fixed Gram determinants need cutoff at most eleven. Consequently the same shift comparison kills the grade-eight leakage in the multiplier steps below. For completeness D is squarefree and D4 and D have no common root in the allowed characteristics: with t=2x−1 and z=t², D=t(33z²−30z+5)/8 and D4 is proportional to 21z²−14z+1. The quadratic has discriminant 240 and nonzero constant 5, is nonzero at z=1, and elimination of the two quadratics gives 24(7z−3), followed by −8/7 at z=3/7 for the latter. The normalization leading coefficients, endpoint values, and all fixed denominators here are paid.

## 1. Exact joint-block detection and a forced terminal factor

This section applies whenever the old mixed-ghost proof fits a v∈F3 outside U by a polynomial P of degree at most three, using diag(v) F5 ⊂ U+w P_(r+2)(c). The old shift argument gives this inclusion after grade-eight leakage removal. It also applies to the clean mask/head case with v=w, Cv∈F4, and literal w=P(c) on its support, where P is at most cubic. In both situations U is preserved by C and diag(v).

Choose the head in a direct complement to U on each joint block B of (c_i,v_i), by subtracting its component in U_B. C and diag(v) preserve this complement. The standard multiplier result then gives diag(v)w=P(C)w literally. In the mixed case write
  v=u_v+w R(C),  u_v∈U,  0≠R∈K[x],  deg R≤r−3.
Indeed C²v∈F5, and the r+5 independent head shifts in E10 force the last two coefficients of any R of degree at most r−1 to vanish. For the clean head case take R=1. Write e_s=f(c)+u_f+w Q(C), deg Q≤r, u_f∈U.

On a matching block B of clock k with v_B=P(k) and nonzero w_B modulo U_B, the terminal is not in the block whenever it contains effective w. More precisely, if it does contain the terminal, then P(1)=v_s=0; v_B=0, whence R(1)=0 since w_B is effective. On any effective block where P(k)≠0 the terminal therefore does not occur, and the two quotient identities are
  P(k)[1_B]=R(k)[w_B],       0=f(k)[1_B]+Q(k)[w_B].
Thus f(k)R(k)+P(k)Q(k)=0. If P(k)=0, the first equality gives R(k)=0 and the same scalar identity. Mismatching blocks where v_B≠P(k) have w_B=0 literally, so do not contribute effective head clocks. The degree of fR+PQ is at most r+3, and it vanishes at the r+5 distinct effective head clocks. Therefore
  f R+P Q=0,  hence P divides fR.                                  (1)
In the clean r=3 case the same argument with R=1 gives a cubic divisor of f. In the mixed r=3 case R is constant and (1) likewise forces P to be cubic.

Here is a fully chronological form of the ghost tests. In a mismatching block B with v_B≠P(k), w_B=0 and v_B 1_B∈U_B, so if v_B≠0 then 1_B∈U_B. The only genuine mismatches have v_B=0, P(k)≠0, and [1_B]≠0 in the block quotient. E10 being the whole coordinate space implies that this quotient is one-dimensional, spanned by [1_B]. At a nonterminal such block k is a zero of f by the terminal representation. In a block containing the terminal, its clock is 1 and [1_B]=[e_s]; the first prefix that distinguishes it from U_B is the last row. This proof works over finite fields and with repeated stages.

For any scalar polynomial M with affordable input define z_M=M(C)(P(c)−v). Modulo U it is confined to the genuine mismatch blocks, with coefficient M(k)P(k) at each. At its first nonzero prefix modulo U, choose a row functional λ supported at that joint block and through the first distinguishing row, annihilating U_B and normalized by λ1_B=1. Such a row exists by ordinary finite-dimensional separation on that restriction. All earlier numerical entries of z_M can be matched simultaneously by one vector in U, because U splits across the joint blocks. Strictness says λA of the corrected vector vanishes. Since A U⊂F6 and λ annihilates F6, λAz_M=0. If M is subsequently multiplied by any polynomial of adequate degree, the same correction works after multiplication and λ still annihilates its A-image. Thus at any such block of clock k the low-grade tests are the literal equations J(MP)(k)=0 whenever the input pair has grade at most five.

For deg P≤3 the multipliers x, x(x−u), x(x−u)(x−a) all make grade-at-most-six input pairs and their profiles are nonzero. E6 separation gives a genuine first mismatch after each mask. The first two clocks u,a are distinct nonzero zeros of D, not the terminal clock: if an earlier contrast only first failed at the terminal, a subsequent mask would have all its numerical values in U, while retaining a nonzero separated profile. In particular
  J(xP)(u)=J(x²P)(u)=J(x(x−u)P)(a)=0.                              (2)
All three displayed equations cost input grade at most five: v∈F3 in the mixed case, or v,Cv∈F4 and C²v∈F5 in the clean cubic case.

If P(0)=0, use the multiplier 1 first. There is no genuine mismatch at zero because any mismatching block with P(0)=0 has v_B≠0 and [1_B]=0. At its first nonzero clock k, the tests 1,x,x² have grade-at-most-five input. They give the fixed size-three x-weighted Hankel on P/x, after rescaling by k, and force P=0. This excludes the zero-at-origin cubic fit in any of the mixed or clean ghost cases.

## 2. The two-omission scalar gate and its only exceptional prime

For a root u of D let I(u)=J(xD/(x−u))(u). Direct synthetic division gives
  60 I(u)/u²=600−6000u+19500u²−25410u³+11484u⁴.
Putting t=2u−1 gives
  80 I(u)/u²=957t⁴−407t³−463t²+123t+22,
  D(u)=t(33t⁴−30t²+5)/8.
At t=0 the left numerator is 22. Otherwise, put z=t². The first numerator reduces to (407z−123)(1−t) by the quadratic relation. Since t≠1, the two equations force
  33·123²−30·123·407+5·407²=−2³·7·11·283=0.
Thus the only unpaid characteristic is 283. In that characteristic 407z=123 gives z=90=72², so u is 106 or 178 in the prime field. This excludes other derivatives even after arbitrary extension of the coefficient field.

Suppose S is a monic cubic divisor of D and the distinct omitted roots u,a occur as in (2) with P proportional to S. Combining the first two tests gives I(u)=0; the third gives I(a)=0. Thus we must work in characteristic 283 with {u,a}={106,178}. The quotient D/[(x−106)(x−178)] has increasing coefficients [70,209,85,132]. For this scaled S, the residues of J(xS)(k)/k² at k=106,178 are respectively 233 and 259. Neither is zero. This closes every nonzero-at-origin cubic divisor from (1).

Exactly the same check closes the rank-two pure quartic with P=xS, where S is a cubic divisor of D: use masks 1,x−u,(x−u)(x−a) so separated profiles again force the two distinct nonterminal omitted roots. The low equations are J(P)(u)=J(xP)(u)=J((x−u)P)(a)=0, which are the same as (2) for S. The rank-two pure quartic with P(0)≠0 instead has only one possible nonterminal omitted root. It must occur: otherwise the grade-five mask x has numerical support modulo U only on the terminal, but its profile of degree five cannot be proportional to f of degree six. The paid omitting-root test forces one of the F283 roots above, and the independently audited physical closure in the separate note excludes both. No terminal-only quartic gate remains.

## 3. The mixed quadratic in r=4

If r=4 and P in (1) has degree two, R must be constant, since deg Q≤4 and deg fR=6+deg R. Degree smaller than two is impossible by the same degree comparison. The zero-at-origin branch was already excluded, so P is a quadratic divisor of D. Normalize it to be monic. The first two low moments in (2) at u then give
  P(x)=x²−6ux/5+3u²/10
by a paid two-by-two moment matrix. For y=a/u, the third low moment factors, up to a nonzero power of u, as y²(y−1)²(4y−3)/20. Consequently a=3u/4. The five roots of D are u,a, the two roots of P, and w=5/2−59u/20. They are distinct: D is squarefree, and P(u)/u²=1/10, P(a)/u²=−3/80.

The roots are invariant under reflection x→1−x and include 1/2. These observations rule out this configuration over every paid field:

* If u=1/2, a=3/8 would force characteristic 17 from 33(1/16)²−30(1/16)+5=833/256. The reflected root 5/8 is neither u nor a nor w=41/40. It must annul P, but P(5/8)=29/320 forces characteristic 29.
* If a=1/2, u=2/3, and the centered quadratic at t=1/3 is 168/81, a paid unit.
* If one root of P is 1/2, then 6u²−12u+5=0 and the other root is 6u/5−1/2. The reflected root 1−u must be a, the other P root, or w. These give respectively u=4/7,15/22,10/13 (characteristic 13 is directly impossible in the third equation 39u=30). The values of 6u²−12u+5 are respectively 5/49,−95/242,−115/169. The first is a paid unit. In the second case characteristic 19 would give u=5 and centered quadratic residue 15; in the third case characteristic 23 would give u=−1 and centered quadratic residue 16. These are not roots of D.
* If w=1/2 then u=40/59 (characteristic 59 is directly impossible). The reflected root 1−u is either a or a root of P. The first choice also gives u=4/7 and forces 44=0, impossible. In the second, P(1−u)=−71/59²; characteristic 71 would give u=44 and centered quadratic residue 21, not zero.

## 4. The one remaining algebraic type: an affine multiplier and cubic fit

For the surviving putative mixed r=4 fit, P is cubic with P(0)≠0; a constant R or P dividing D was excluded by the two-omission gate. Hence after scaling v,P together take
  R=k(x−ρ),  P=(x−ρ)S,  0≠k∈K,
where S is a monic quadratic divisor of D. To see the factor S, if P were coprime to R then P would divide D by (1); otherwise cancel x−ρ. The first two detected clocks u,a are roots of D off P. Name the third root off S as b, so
  D=132(x−u)(x−a)(x−b)S.
Here ρ differs from u,a because they are off P, and from b because P does not divide D. It may equal a root already in S; none of the following assumes P squarefree. Put F=x(x−u)(x−a)S.

The third mask numerical vector z3=z_[x(x−u)(x−a)] has profile F(x−ρ); it has support modulo U only in the genuine block at b and at the terminal. If the b block were absent, it would be a multiple of the terminal modulo U, so E6 separation would force F(x−ρ) proportional to f=132 F(x−b), impossible. It follows that b is the third, preterminal mismatch.

Moreover z3−e_s/132 is genuinely a grade-five pair, not just a degree-five polynomial considered in E6. Its profile is (b−ρ)F. The head coefficient of the defect of z3 is −k x(x−u)(x−a)(x−ρ). The terminal defect has head coefficient Q=−132 k x(x−u)(x−a)(x−b) by (1). On subtracting e_s/132 the degree-four terms cancel, leaving head degree at most three, and F5=U+w P3. The corrected vector has no mismatch before b, even after subtracting the terminal. Apply A to this grade-five pair and evaluate with the causal functional at b from Section 1. This yields J(xD/(x−b))(b)=0. Thus characteristic 283 is mandatory, and b is 106 or 178.

At u put M_j=J(x^j S)(u) for j=1,2,3. The first two equations of (2) give M2=ρ M1 and M3=ρ² M1. If M1 were zero, all three paid moments would vanish and force S=0. On the other hand,
  I(u)=132[M3−(a+b)M2+ab M1]=132(ρ−a)(ρ−b)M1≠0.
Hence u is not 106 or 178. The other roots in characteristic 283 are 69,142,215: the centered equation splits at t=0,±72,±137, because the squared roots are 90 and 91. Thus all clocks needed below actually lie in the prime field.

Finally put s=(r1+r2)/u and d=r1r2/u² for the two roots of S, and m_j=∫₀¹ t^j(t²−s t+d)dt for j=1,2,3. From M1M3−M2²=0 it follows that m1m3−m2²=0. Its exact numerator is
  3600(m1m3−m2²)=6−20s+45d+15s²−60sd+50d².
For each u, label A=106, B=178 and C,D' the other two candidate roots aside from u, in increasing order. Pair AB cannot constitute S because b lies in AB and is not a root of S. The scaled values (A/u,B/u,C/u,D'/u) and exact numerator residues for the five remaining pairs are:

 u   | scaled values, mod 283 | AC | AD' | BC | BD' | CD'
 69  | −101,60,121,−42         |219 |44   |176 |276  |168
 142 | −71,73,138,−136         |27  |170  |185 |125  |11
 215 | 90,39,128,−77           |192 |38   |234 |216  |128

These are only 15 simple substitutions in the displayed quadratic in s,d; every value is nonzero. They exclude the final affine mixed ghost, independently of the old five-by-five ghost determinant. No split-prime search for tableaux is used.

## 5. Remaining structural dispatch and payment checklist

* r=4 with dim F4=4 may take the cleaned mask head in F4 with its first two shifts also in F4. Its square and all shifts through the fourth fit in last-zero F8, so the same leakage-free comparisons yield a head polynomial of degree at most two. The first three x-weighted moments at one mismatch are affordable through pure F6 and contradict the paid size-three Hankel. If dim F4=3, F3 escapes U since dim U=1; use Sections 1–4. No assumptions on signs, weights, or distinct physical rows beyond the proved chart.
* r=3 with F3 escaping U uses the mixed multiplier and (1), giving a cubic divisor of f. If F3 is contained in U, then F3=U and Hermite forces dim F4=4; the clean mask head and its first shift lie in F4, so the square-shift comparison gives a cubic-or-lower fit. Take v=w, R=1 in Section 1. This is again a cubic divisor of f. Sections 1 and 2 exclude both possibilities.
* r=2 with dim F4=3 uses the existing three-mask off-row scalar bootstrap. Its only numeric divisions are paid, and its rank contradiction concerns the actual distinct off-mask clocks. With dim F4=4 and genuinely nonzero square leakage H8, the existing degree/multiplicity count bounds the E10 row features by sixteen. It uses only D squarefree, D4,D coprime and polynomial degree or multiplicity, all valid here. With zero leakage, Section 2 and the separately audited F283 physical proof handle the two pure branches.
* The original 30-pair ghost determinant and the old 40-endpoint pure scalar norm therefore need not be paid as integers. The old 30-pair chart relied on only five equations even though a third genuine prefix is guaranteed; at the actual affine fit, the terminal coordinate pays a full grade at that prefix. No unknown large prime from these two arithmetic norms survives.
* Before promoting an arbitrary-ring theorem retain the upstream checklist: cleared chain pays 12! in the coefficient ring; reduce via a maximal ideal to a nonzero field; the generic paid grade-five surplus supplies the preliminary 17-row floor; use paid Hankel separation and endpoint pairs, the reverse physical two-node confinement (or the three original causality cases with small nonzero clock factors and the paid quadrature Hankel), and the exact chart ranks to reach E10. No large characteristic-specific division is used in this note's sections. The original field chart's use of a generic vector must be replaced by per-vector interpolation and finite joint projections, as done above. No Lean certificate over positive characteristic is asserted here.
