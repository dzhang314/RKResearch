# Order sixteen: every 22-stage real DIRK has a genuine hidden ordinary defect by grade six

**Result for independent review.** For ordinary lower triangular RKOC of order 16 over the reals, write B=diag(b) and F_j for the genuine zero-profile ordinary stage columns through grade j (tree order minus one). If s=22, then
\[
                  F_6\cap\ker B\ne0 .
\]
In particular the unrestricted all-individual-weights-nonzero subclass needs at least **23** stages. A 22-stage solution needs an interior zero individual output weight, not merely a terminal dummy or a zero weight at its explicit initial row. The unrestricted integer floor itself remains 22. All abscissae, repetitions, nonzero-weight signs and internal diagonals are unrestricted. This augments, rather than reproves, the existing real C(2) and minimal-fifth-mark reduction.

The new proof conditional on C(2), a nonzero final b_s, and dim M5=3 works over **every coefficient field of characteristic zero** (in fact it suffices to assume m2=0 and m3,m4,m5=1,2,3). The full unrestricted structural result as stated holds over **every ordered field**, by parameter-free real-closed-field transfer of the rational RKOCs and the finite rank/injectivity assertions. No unconditional assertion of the same rank loss over an arbitrary unordered field is made. The known no-C(2) class exclusion at 22 uses a real-only quartic test; in the special injective-F6 setup its characteristic-zero exclusion is elementary too, as noted below.

Inputs: dirk_order16_twenty_two_requires_c2_and_minimal_fourth_mark_20261123.md (use its stronger last section, currently a separate research result); dirk_orders12_through15_short_native_lower_endpoints_from_grade_six_20261123.md; dirk_field_audit_refunded_cuts_and_order12_over_characteristic_zero_20261123.md; rk_low_grade_reflection_single_mark_extension_and_p17_dense_branch_20261123.md. The standalone finite norm proof is dirk_order16_hidden_six_two_ended_lobatto_pivot_replay_20261123.md. No inverse of a zero individual weight is taken below.

## Dispatch and a singular-weight transfer

E_j denotes all actual ordinary stage features through j, M_j the actual one-mark rows of zero reflected scalar density, in matched original stage coordinates; m_j=dim M_j. In particular BF_j lies in M_j, and M_i annihilates E_j when i+j<=15. Write C=diag(c), y=1-c, and Y=I-C. Trimming the trailing row against the previously proved 22-stage lower gives b_s nonzero. For the real original theorem we enter the anchored reduction C(2), m2=0, m3=1, m4=2, m5=3: the first row is truly zero and D1=D2=0 imply c_s=1, a_ss=0. Every ordinary pure column vanishes in physical position 1.

Argue by contradiction that B is injective on F6. Native f6>=5, f7>=6, f8>=7. Anchored P8 separation at grade eight gives E8 >=16: H(c) pure implies H(0)=0 and testing against all P7 makes H=0 by the fixed rational x dx Gram. Thus m7<=6 and strict genuine marked growth gives m6<=5. It follows that m6=f6=5, M6=BF6, m7=6, E8 has dimension 16, f7=6 and f8=7. The two-detector outgoing lemma makes M6 noninvariant under C since its outgoing gain is only one. Hence BF7 contains M6+C M6 of rank six, proving M7=BF7 and injectivity on F7. The assumed fifth marked minimum and strict ordinary increases now give
\[
     M_j=BF_j,\quad f_j=m_j=(0,1,2,3,5,6)\quad\hbox{at }j=2,3,4,5,6,7 .
\]
Also E8=P8(c) directly plus F8 equals Ann M7. Even without the real reduction, a non-C(2) injective-F6 chart over any characteristic-zero field is impossible: f6>=6, f7>=7,f8>=8, unanchored P7 separates at grade eight, so m7<=6 and m6<=5.

The two unit gains from six to eight give the ordinary single-head form
\[
 F_6=U+w P_{r-1},\quad F_7=U+wP_r,\quad F_8=U+wP_{r+1},\qquad
 r=5-\dim U ,
\]
all sums direct. In particular C-invariant U is already in F6. Indeed F6,F7 are noninvariant by the outgoing and F8 by the incoming Hermite lemmas; each unit step is a C-escape. The split-diagonal chain proof in the field audit works over any field in scope. There are at least r+3 distinct effective w clocks by noninvariance at eight, after choosing local complements to U. A vector in F8 supported at just one numerical clock is in U: its head polynomial of degree <=r+1 vanishes at at least r+2 other effective clocks.

If b_i=0 for i other than 1, then e_i lies in Ann M7=E8. Write e_i=H(c)+f, f in F8. True quadrature tests against P7 make H orthogonal to all P7, and H(0)=0. Thus H=0, and local e_i belongs to U in F6. This contradicts the assumed injectivity. There remains the subtle possibility of exactly one zero weight, at the first physical row.

Let S be the active weights. Under the displayed full equalities through seven the actual restricted reversed matrix
\[
    \widehat A = B_S^{-1}(A^T)_{SS} B_S
\]
with stage order subsequently reversed and weights b_S has order at least EIGHT, even if a zero weight is omitted. By D1,D2 its row sums are y_S, and it satisfies C(2); its genuine first reversed row (the old terminal) is zero. Here is a general limited-grade transfer that avoids all division at missing coordinates: each true reverse ordinary stage feature through d=7 is the restriction to S of a genuine old ordinary feature of the same grade and reflected profile. Use induction on products, marking any converted old child v by B before applying A^T. The marked primitive discrepancy from b(JH)(y) lies in M_j=BF_j, and its active restriction is the requisite genuine reverse primitive times B_S. In the matrix multiplication Bv vanishes at every omitted index; no restriction on virtual row values there is needed. Rewrite the discrepancy as B times a genuine ordinary pure and then restrict. At the output through d the omitted b are zero, hence original quadrature proves reverse order d+1. This does NOT claim double horizon on a singular B.

The reverse ordinary seventh flag has rank >=6 by its native grade-six rank >=5 at order eight and the strict next increase. Its restricted original counterpart R_S F7 also has rank six, so they coincide by this transfer. Consequently every F7 column vanishes at s, as does every F8 column since F8=F7+CF7. If b1=0, e1 lies in E8=Ann M7. Its scalar part in P8 is orthogonal to P7 as before, but now has H(0)=1: it is the normalized degree-eight shifted Legendre polynomial. At s every F8 vanishes, forcing H(1)=0 although this Legendre polynomial has nonzero value there. This contradiction eliminates the sole-omitted-initial case. We have proved that an injective-F6 counterexample must have ALL weights nonzero.

## Bidirectional ordinary flags and the fixed Lobatto grid

In the remaining dense case use the genuine one-mark doubling lemma with d=7: the actual reflected tableau has full order 16. Indeed up to total grade 15 at most one integrated child factor can have grade >7. Mark this factor once by the genuine A^T recursion and use converted ordinary lifts on all others. On all-active coordinates no normalized product of two arbitrary marked rows occurs. The original and genuinely reflected ordinary F_j agree through 7: reflection gives containment, and the native lower rank at each grade equals the displayed dimensions. For reverse grade 8 we also have exactly 7 dimensions: as for the original, its genuinely marked rank at seven is >=6 by dense weights, so its E8 has dimension <=16, while anchored P8 separates. Therefore both F8 are the same C-extension of the common F7. These common flags vanish at both physical endpoints.

In either orientation E9 has dimension at most 17 by genuine marked rank at six >=5. Write Z=F8+CF8, terminal- and initial-zero, of dimension >=8 by noninvariance of F8. P8 separates from Z because H(0)=H(1)=0 for a represented scalar H and the genuine grade-nine pure tests go through P6; the fixed x(1-x) Gram kills H/[x(1-x)]. Hence
\[
    E_9=P_8(c)\oplus Z,\quad Z=U+wP_{r+2},\quad \dim E_9=17 .
\]
In particular the monic degree-nine alias D=x^9-H8 has D(c) in Z. It vanishes at 0,1 and is orthogonal through degree six, so D is the unique monic multiple of x(x-1)L8'(x), with shifted Legendre L8. Every physical position outside supp U and supp w (a clean position) thus has its abscissa on the fixed NINE-node Lobatto grid. A true F9 member may NOT be assumed clean-zero. Its scalar part belongs to the single line phi(x)=x J7(x), J7 the shifted degree-seven Jacobi polynomial for x dx: it vanishes at the actual origin and is perpendicular to P6. If it vanishes at both endpoints the scalar part is zero. The reflected analogue has scalar line phi(1-x). At every nonzero Lobatto node phi is nonzero. For instance (x-1) times the degree-seven x(1-x) polynomial is a linear combination of the consecutive degree-eight and seven x-weighted polynomials with nonzero degree-eight coefficient, and hence has no common zero with J7.

We require one more effective head clock, not E10 saturation. E9=Ann M6 is not invariant because M6 is not. As CP8 is in E9 and U is invariant, the escape in E9+C E9 is the next head power, genuine and independent. There are consequently at least r+4 distinct effective w clocks.

## One low-grade contrast in BOTH orientations

Put k=dim U. The three-detector gain from U at F6 gives k+3<=f7=6, hence k<=3. If k=3 then r=2. Every v in F4 has no head, because v,Cv,C²v belong to F6, whose head degree is only one (compare successive coefficients at the >=r+4 effective clocks). Thus F4 is in U. As f4=2 and f5=3 make F4 noninvariant, its C-extension fills U=F5. The incoming gain at five forbids this invariant rank-three F5 after a unit increment. Thus k<=2, r>=3.

Let h=Ac²-c³/3, the nonzero true cubic defect. For node-local u in U, hu is terminal-zero true F9, hence in Z. It is in U: a localized Z head of degree <=r+2 cannot vanish at the >=r+3 other effective clocks. Thus hU lies in U. Split U by simultaneous (c,h) blocks and choose w in local linear complements. The genuine products h C^i w for 0<=i<r also are terminal-zero F9 and so in Z. The joint complements remove their U parts. On comparing their head polynomials successively, >=r+4 distinct effective clocks enforce T_(i+1)=xT_i, deg T_i<=r+2. Consequently h_i=P(c_i) wherever w_i is nonzero, for one P of degree <=3.

In fact P=0. For completeness, eliminate U in the joint (c,h) blocks using its earliest chronological pivots, let pi be the retained map, L its zero-insertion section, beta=pi 1 and omega=pi w. Then pi h=beta h_ret is in omega times polynomials. The retained vector theta'=pi(P(c)-h) vanishes wherever omega is nonzero and equals beta P elsewhere. The reduced triangular operator pi A L need not itself have RK order. Its true primitive discrepancies differ by pi AU inside pi F7; double-integration/commutator discrepancies by pi(AU+CAU+A²U) inside pi F8 (expand Lpi=I-Q with image Q=U). They vanish at omega-clean positions. All scalar moment tests remain valid since b kills the whole invariant U. If P is nonzero there are actual first retained nonzero pivots for masks x theta' and x(x-a)theta', with distinct nonzero clocks a,d: absence would kill the scalar profile xP or x(x-a)P against all available tests, contrary to the fixed x dx Gram applied to P or (x-a)P. At each first pivot the commutator gives minus the reduced diagonal squared times the nonzero entry, hence the diagonal is zero. The true primitive tests give all three moments of xP through degree two at a and both moments of x(x-a)P through degree one at d, dividing only by the nonzero retained base there. The masks and primitives have true cost at most seven; projection errors fit through eight. These 3+2 moments exclude every nonzero cubic over arbitrary characteristic zero (the m=2 differentiated-factor lemma of dirk_characteristic_zero_nearly_balanced_two_endpoint_moments_and_grade_ten_dyadic_20261123.md). Thus P=0 and pi h=0: it is zero on omega support by the joint split, and elsewhere by its polynomial-times-omega representation. We conclude h in U, so k=1 or 2. Moreover h is node-local: otherwise h,Ch span F4 of rank two inside U, making F4 invariant, impossible by its outgoing unit gain.

Select v in F4 outside U (if F4 were contained in U it would equal invariant U). Write v=u+w L(c) with deg L<=r-3 since v,Cv,C²v are in F6. The genuine square v² belongs already to F8=U+wP_(r+1). Consequently for a single polynomial Q of degree <=r+1,
\[
        L(c_i)v_i=Q(c_i)
\]
at every nonzero-w position outside supp U: there v=wL and v²=wQ. Q is not zero, because L is nonzero and at least r+4-k distinct effective head clocks remain away from the <=k U nodes. This square argument requires no literal order-ten comparison.

For k=1, the node-local h² in F6 belongs to the one-dimensional U, so a scaled h is the true grade-three indicator of supp U, and hv in F7 shows v is constant there. Correct Q(c)-L(C)v on this support by subtracting the appropriate constant times that indicator. For k=2, r=3, L is constant and deg Q<=4. If U uses one node z, instead multiply Q(c)-L v by c-z. If U uses two, choose z to be the other node than h's site; the one-dimensional h component again has its genuine grade-three indicator and v constant there, so subtract the remaining constant on that support. A possible physical overlap at the same numerical node does not spoil the identity, and the multiplier kills the entire other node.

In every case there is a genuine stage pair (theta,P) of grade <=5 such that P is a NONZERO polynomial of degree <=5, theta is zero on supp U union supp w, and equals P(c) at every other position. It is the same numerical contrast in both orientations: theta-P(c) is a genuine F5 column and F5 agrees in the original and reflected tableaux. Its backwards scalar profile is P(1-y). In particular every nonzero coordinate of theta belongs to the fixed Lobatto grid.

## Two ends and one carefully paid primitive

In either orientation, denote the profile temporarily by P(x) and write a,d for the first and second distinct nonzero active clocks in that orientation. They exist by the x dx Gram as in the preceding cubic test (here deg P<=5, grade allowance 15). All F8 vanish at clean rows. Thus the commutator on x theta, of grade <=8 at its first pivot a, refunds that diagonal. The commutator on x(x-a)theta may cost nine, but it vanishes numerically at the previous pivot because the masked input was zero on its whole prefix. Such an F9 has one possible scalar line phi on clean rows, and phi(a) is nonzero. Therefore the scalar coefficient vanishes, and the actual diagonal at the first surviving d is zero too. This is not an assumption that all grade-nine defects are clean-zero.

Write I_u[H]=integral from 0 to u of H. Primitives through grade eight give
\[
 I_a[xP]=I_a[x²P]=I_d[x(x-a)P]=0 .
\]
The primitive of x²(x-a)theta can cost NINE. Its numerical value vanishes at both selected actual stages by triangularity and the two refunds. Its scalar discrepancy at both is the SAME multiple of phi (up to the common sign). Thus
\[
 \phi(d)\, I_a[x²(x-a)P] - \phi(a)\, I_d[x²(x-a)P]=0 .
\]
This fourth equation is essential: the six first-two/second-one raw moment equations need not alone have full rank. Evaluate these four linear forms at both ends, replacing P(x) by P(1-y) at the other end. There are 8*7=56 possible ordered pairs of nonzero, distinct Lobatto nodes in EACH coordinate orientation, including 1; endpoints may recur or lie in either chronological ordering. At split primes 1033 and 1237 every one of the 3136 resulting eight-by-six matrices has column rank six. The standalone source verifies the fixed grid, reflected basis, rank and algebraic lifting. The contradiction forces P=0, excluding dense B, and completes the proof.

The transfer ingredients are reusable: active-only grade-d reversal from M_j=BF_j, without presuming double horizon on a singular B; simultaneous saturated F7/M7 gives a two-ended ninth-grade Lobatto alias and a one-dimensional visible leakage; the fourth clean-pivot equation retains that leakage rather than spending it twice. The finite determinant is a property of the fixed rational Lobatto grid, not a reduction of unknown tableau coefficients.
