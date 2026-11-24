# A genuine grade-five single head cannot pass five distinct nonzero clocks: the order-17 23-stage barrier

**New lower-bound result, pending independent review:** no real lower triangular 23-stage method of ordinary order 17 exists, hence the unrestricted minimum is at least 24. The same theorem eliminates the anchored f7=6 order-16/21-stage alternative. It is a finite ordinary stage-algebra obstruction independent of output weights, signs, diagonal, node locations, numerical multiplicities or any reverse order assumption. No ledger was edited in this pass.

## General chronological theorem

Use the ordinary feature calculus: an actual numerical stage column and a polynomial profile of grade at most m; A advances the grade by one and integrates the profile from 0, while multiplication by the stage abscissa multiplies the profile by x. F_m consists of numerical vectors with an actual zero-profile realization at that grade. Let distinct disjoint physical classes T_a each have one (not necessarily mutually distinct) abscissa a, with their indicator in F5. Assume w is the numerical vector of a genuine grade-five zero-profile feature, vanishes on those classes, and, on their physical complement, each vector of F6, F7, F8 has respectively the single-polynomial form w times an affine, quadratic, cubic in c. The zero vector or a smaller flag is allowed. All coordinates of one vector must use the SAME polynomial. A real lower triangular original tableau under these conditions has at most FOUR distinct NONZERO abscissae outside T. Numerical matches to a physically masked T site still count; all original stages at 0, including those with nonzero w, are allowed.

Suppose to the contrary that five distinct nonzero outside sites debut chronologically, labeled z1,...,z5. The prefix t ends at the first such appearance of z_t. At each debut select its actual value w_i; keep the same witnesses in every subsequent prefix. Actual prior rows at the same knot may freely have other values of w. The first three w_i are nonzero: otherwise take P=x(x-z_i) times the product of (x-z_j)^2 over prior distinct nonzero clocks. Degree is at most six; P vanishes on the whole prefix after physically correcting the T columns by subtracting the genuine pure sum P(a)1_(T_a). Its primitive must then vanish at a zero-w debut by the F6/F7 containment (use nesting when cheap), whereas P has strictly one sign on the open segment from 0 to z_i except at finitely many roots. No orientation assumption on z_i is used.

## The simultaneous input/output saving at *every* split site

For t=3,4,5 set m=t+2, d=t-3. Take all P of degree at most m with P(0)=0 and all q of degree at most d. Use the genuine grade-m input
    P(c) - sum_a P(a)1_(T_a) - w q(c),       formal profile P.
On the actual prefix outside T require P(c_i)=w_i q(c_i), so this entire input is identically zero there AND on T. Let D record once each of these sites: any nonzero clock actually possessing two different w values on the prefix, and 0 if any outside origin on the prefix has nonzero w. Put b=|D|. These repetitions/zero-origin constraints amount to q|D=0 together with at most t specified equations P(z_i)=w_i q(z_i). Therefore the allowed pairs have dimension at least
    m + max(0,d+1-b) - t.
Projection onto P is injective: if P=0, the three already nonzero w witnesses force q to vanish at three different clocks, while d<=2. Thus the same lower bound holds for the polynomial input domain. The primitive JP(x)=integral from 0 to x of P vanishes modulo wR on this entire prefix since A of the actual input is zero there by triangularity and F_(m+1) has R degree at most d+1. In particular R also vanishes at every site of D: two different w values multiplying R must give the same JP; at zero JP(0)=0. Hence the rank of P -> (JP(z_i))_(i<=t) is AT MOST max(0,d+2-b). The difference of the last two bounds is at least m-t-1=1, INCLUDING b above either polynomial dimension. This pays for every repeated state at both ends of the same true A operation, rather than pretending the first representatives form a folded order-p tableau.

Consequently there is a nonzero P in this kernel, and
    JP(x)=x^2 V_t(x) g(x),      V_t=product_(i<=t)(x-z_i),   0!=g in P_1.
The double zero at 0 uses P(0)=0. Differentiate at z_i:
    w_i q(z_i) = z_i^2 V_t'(z_i) g(z_i).
If all selected w_i are nonzero, use the degree of q (<=t-3) and its two divided differences: the two-vector of coefficients of g is in the kernel of
    H_t = sum_(i<=t) (z_i^2/w_i) (1,z_i)^T(1,z_i).
Indeed sum q(z_i) z_i^ell /V_t'(z_i)=0 for ell=0,1. This is a symmetric two-by-two matrix, not a positivity assumption. If two selected w_i vanish, g has two distinct roots, impossible. With precisely one zero at z_j, g is proportional to x-z_j. Interpolating q on the OTHER t-1 sites gives instead
    sum_(i<=t,i!=j) (z_i^2/w_i) (z_i-z_j)^2 = 0.
The extra source factor comes from V_t'=(z_i-z_j)V_(t,omit j)' there.

If w4=0, the last identity at t=4 and 5 differs by a nonzero term unless w5=0, itself impossible by the two-zero case. Thus w4 is nonzero. H3 is nonzero and singular: its three moment entries would otherwise make three nonzero weights vanish by Vandermonde. Since H4=H3+(z4^2/w4)(1,z4)^T(1,z4) is singular, H4 is either zero or rank one along (1,z4). At t=5, a nonzero w5 would then make H5 nonsingular in the latter case; if w5=0, its quadratic test at (-z5,1) likewise excludes that case. Therefore H4=0. The three signed moments at the four distinct knots have the unique barycentric null direction, so after an inessential common rescaling of all w,
    w_i = z_i^2 V_4'(z_i)   for i=1,2,3,4.
The rest of the proof never divides by w5.

## The first four are forced to be a Lobatto skeleton

Write u=z4, V=V4, U=V/(x-u), and Lf(x)=x^(-2) integral_0^x t f(t)dt (a polynomial operator with coefficients x^j -> x^j/(j+2)). The masked scalar inputs xV and xU have cost <=5, so their primitives at their selected witnesses equal w times affine polynomials. With the just-proved four physical amplitudes this says as polynomial identities
    LV=A V'+B V,                    LU=(x-u)D U'+E U,
where A,D,E are affine and B constant. This follows by divisibility by V, respectively U; the remainders have the indicated degrees. A is not zero: otherwise distinct coefficient eigenvalues of L would make V a monomial. Set a=A' and K=a+B.

Apply x*d/dx+2, the inverse of L. At the three distinct nonzero roots of U, use V''=(x-u)U''+2U' and V'=(x-u)U'. Eliminating U'' gives
    A[(x-u)D'-D+E] - K(x-u)D = 0
at all three. This polynomial has degree at most two, hence is identically zero. No division by the value of A or D at a knot is needed in this elimination (a simple U root suffices).

If K!=0, A shares no root with V: evaluating the differential equation x A V''+(2A+xK)V'+(2B-1)V=0 at a shared root contradicts its being nonzero and simple. If A is nonconstant, the last identity makes A divide D; if A is constant, K=B=1/6 by leading coefficients, and the identity by degree forces D constant. In either case D=lambda A. Substitution yields E=lambda[A+B(x-u)], and thus LU=lambda LV, impossible by injectivity of L and unequal polynomial degrees (including lambda=0).

So K=0. The same polynomial identity now gives E=D-(x-u)D'=D(u), constant. The LU identity by degree forces D constant as well. Then LU=D V', and U=D(xV''+2V'), with D!=0. By the quartic leading coefficient 4a+B=1/6 and K=0, a=1/18, B=-1/18. The V differential equation becomes (1-2B)V=A(xV''+2V'), forcing A proportional to x-u, indeed A=(x-u)/18. Equivalently U satisfies x(x-u)U''+(4x-2u)U'-18U=0: up to scale its three knots are exactly the three interior Lobatto nodes of [0,u] in some order. This last identification is not needed for the contradiction.

## The genuine fifth receiver cannot follow that skeleton

Rescale all clocks by their common nonzero factor u, so z4=1; all preceding scalar mask and head interpolation statements are homogeneous (rescale w also to keep its first-four normalization). Now V obeys
    B1(x) = x^2 [P1(x)V'(x)+R0 V(x)],      P1=(x-1)/18, R0=-1/18,
where Bk(x)=integral_0^x t^k V(t)dt. Elementary integration by parts gives
    14 B2=(18x-2)B1 - x^2(x-1)V,
     8 B3=18x^2 B1 - 6 B2 - 2x^3(x-1)V.
In particular Bk=x^2(Pk V'+R_(k-1)V), with deg Pk<=k. Let v=z5 distinct from 0 and 1. The two scalar masks x(x-v)V and x^2(x-v)V vanish on the whole fifth prefix after the T corrections, including all earlier repeated values. Their primitives at any witness therefore equal w times polynomials of degrees at most two and three by F7/F8. At the first four knots those polynomials are exactly P2-vP1 and P3-vP2, respectively: the explicit Bk forms give their values there and the four distinct witnesses determine either polynomial. At v the same two equations therefore require
    (w5-v^2 V'(v))(P_(k+1)(v)-v Pk(v))
        = v^2 V(v) (R_k(v)-v R_(k-1)(v)),      k=1,2.
The right common factor v^2 V(v) is nonzero. But the determinant
    (R1-xR0)(P3-xP2) - (R2-xR1)(P2-xP1)
is exactly -x(x-1)^3/1008, nonzero at v. This excludes the simultaneous equations regardless of w5. The following exact replay verifies the two integrations, the quartic, and this factor.

## Which original rank cases this closes

The pre-existing cross-branch reduction in dirk_chronological_reciprocal_head_masks_close_three_frontiers_20261123.md (last two sections), with dirk_parity_anchored_remainder_dyad_order16_order17_20261123.md including its degree-drop correction and dirk_order17_reverse_product_trace_and_signature_divisor_20261123.md, establishes that every remaining order-17/23-stage ordinary tableau has a genuine local three-class U in F5, w in F5 vanishing on these classes, F_j=U+w P_(j-5) for j=6,7,8, and at least 18 preterminal/outside signatures with at most two (c,w) states per site in the minimal-early-reverse branch, or at least 14 outside abscissae in the early-surplus branch. Both give more than four nonzero actual outside sites (even subtracting the origin). This includes the corrected-cardinal and zero head cases and imposes no nonzero or sign condition on individual b. Saturation of all earlier rank exclusions is as recorded in the cited notes; an independent review of both earlier coverage and this new argument is requested before promotion. Trimming/padding lower counts is unnecessary beyond the already audited lower 23.

For p16/s21 with C(2), f7=6 the same original grade-five flag holds and the earlier dyad/cardinal case gives at least thirteen distinct nonterminal outside abscissae, so that branch also falls. This argument does not by itself eliminate p16 f7=5 or other uncontrolled rank regimes, nor does the grade-four analogue directly yield a 2-by-2 partial moment. No p16 unconditional integer increase is implied.

## Short cross-order scalar corollary and primary branch ledger

No signature/weight count from the later p17 chart papers is actually needed. Each genuine pure 1_(T_a) has b-sum zero in order >=6, and c is constant on that class. Thus all scalar quadrature contributions from these physical classes cancel at their own sites, even when an outside receiver shares that numerical value. If only four or fewer nonzero outside sites S exist, x product_(z in S)(x-z)^2 is a nonnegative polynomial of degree <=9, with strictly positive integral on [0,1], and every outside coordinate evaluates it to zero. This contradicts even order ten. In particular the displayed grade-five single-head flag is impossible at ANY number of stages for any ordinary real order p>=10. This gives the needed fifth outside debut uniformly, irrespective of all output signs or zero b. It also explains how the resulting obstruction can be used without any endpoint cardinal or folded-tableau moment identities.

The primary case dispatch for 23 stages at p17 is:
1. If g=Ac-c^2/2 is nonzero, dirk_parity_cardinal_remainder_order16_order17_20261123.md excludes the case with no coefficient restrictions.
2. Now assume g=0. If the genuine M2,...,M5 reverse ranks take their minimal values, dirk_order17_terminal_zero_kernel_transfer_20261123.md gives the anchored low-grade ordinary head decomposition; dirk_parity_anchored_remainder_dyad_order16_order17_20261123.md proves r=1, k=3 and the local algebra in BOTH scalar cardinal degrees, including the final degree-drop correction at degree eight. Before any degree-shifted presentation of high E_j, the ORIGINAL ordinary F_j are U+w P_(j-5) at j=5,6,7,8. w vanishes on supp U, and U is coordinatewise and C-invariant. Its support indicators span the three genuine disjoint site-classes in F5. These facts, independent of the eventual penultimate clone, are also explicitly cross-checked in the opening of dirk_order17_signature_witt_singleton_and_punctured_reflection_20261123.md.
3. In the complementary early-surplus case, dirk_order17_early_surplus_scalar_divisor_20261123.md proves f4=2, f8=7, f9=8. Strict increases give 3<=f5<=4. Arbitrary-weight f5=3 is excluded by dirk_order17_early_surplus_grade_five_three_fully_excluded_20261123.md. For f5=4, the scalar-divisor proof itself gives k=3, r=1, U an actual algebra with 1_T, w zero on T, and F_j=U+wP_(j-5) for 5<=j<=9. Since U is C-invariant its three coordinatewise joint classes are each at one physical abscissa and have genuine F5 indicators. It is unnecessary here to use later distinctions by square-trace coefficient, reverse-invariant multiplicity, or unsigned constituent pivots.
Both live branches therefore contradict the cross-order scalar corollary. At (p,s)=(16,21), the same parity remainder proof excludes g!=0. Its anchored dyad companion leaves f7=5 or 6. Only f7=6 supplies precisely the F5,...,F8 flag settled here (again r=1, k=3), and is excluded. Therefore the only remaining p16/s21 case has C(2), f7=5 and depends on a DIFFERENT, grade-four flag, not the grade-five result.

The companion exact replay is dirk_grade_five_confluent_head_hankel_p17_24_exact_replay_20261123.md. A separate native integer-polynomial computation checked the three scaled derivative identities and the exact determinant coefficient -1/1008.
