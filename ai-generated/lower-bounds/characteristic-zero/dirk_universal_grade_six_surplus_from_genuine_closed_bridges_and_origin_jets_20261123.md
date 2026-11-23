# A universal surplus by grade six for every ordinary DIRK of order at least eight

**Theorem.** Let A be any lower triangular Runge–Kutta array satisfying the classical rooted-tree order equations through p>=8 over a characteristic-zero field. Write F_j for the numerical space of stage lifts with zero scalar profile through grade j (grade = tree order minus one), and f_j=dim F_j. Then
    f_6 >= f_3+4.
In particular f_6>=5, or f_6>=6 when Ac-c^2/2 is nonzero. Arbitrary signed and individually zero weights, repeated or exterior clocks, mixed zero/nonzero diagonals and masks without a true origin are allowed. This moves the first universal surplus into the three steps 3 to 6, rather than the previously established four steps 3 to 7 at p>=10. It is a rank theorem, not by itself an announcement of a higher integer stage minimum.

## Genuine starting reduction and its field scope

Strict native ordinary growth gives f_6>=f_3+3. If equality holds the grade-six equality theorem in dirk_universal_grade_seven_surplus_and_grade_six_terminal_head_20261123.md gives the following after its grade-four invariant-head alternative has been excluded:
    F_j = U + w P_(j-3)(c)    (direct sum),  3<=j<=6.
Here U is spanned by genuine F_3 indicators of disjoint physical classes T_a, each at a single numerical clock a; different classes may share the same a. The genuine F_3 vector w vanishes on their union T. Off T it equals a nonzero P(c) wherever w!=0 (the dirty rows) and is zero otherwise (the clean rows), for a single polynomial P of degree 2 or 3 with P(0)!=0. There are at least FIVE distinct dirty clocks because F_6 is non-C-invariant (unit incoming gain): four or fewer would already make wP_3 invariant and U is invariant. All of this is algebraic in characteristic zero; the grade-four zero-head debut test, all Hermite gains and nodewise complements are explicitly justified in dirk_field_audit_refunded_cuts_and_order12_over_characteristic_zero_20261123.md, items 1-5. In the last low-degree exclusions of the grade-six equality theorem, two or three independently available local primitive tests against all polynomials of the stated degrees give nonsingular fixed moment matrices after x=uz. No variable-coefficient complex square is assumed nonzero.

There is at least one nonzero clean clock that is not a root of P. Use the genuine grade-three theta=P(c)-sum_a P(a)1_(T_a)-w, with scalar profile P and zero numerical values on T and dirty. If every clean coordinate were at zero or a root of P, its weighted pairing with c q(c), for every q in P_3, would vanish numerically. The order-p grade allowance is exactly 3+(1+3)<=7=p-1 at the minimum p=8. Therefore every integral of xPq would vanish, contradicting the nonsingular fixed rational x dx Gram matrix on P_3. This supplies an actual clean scalar witness without considering the number of signed weighted rows. No separate existence of a second clean clock is necessary for the proof.

## Precise finite-grade projection, including the second integration in the commutator

Retain one earliest physical representative of each pair (c_i,w_i) outside T, except delete all clean rows of clock zero. Keep a dirty clock zero if present. Let D restrict to these representatives in original order and L repeat the corresponding value at all retained-signature copies, inserting zero throughout T and at every deleted clean zero. DL=I. Put B=D A L and X=D C L; B is lower triangular: a column transferred from any later duplicate goes to its earliest original representative, never to a later position. X is the diagonal of the retained clocks.

For every genuine ordinary lift (v,f) of grade j in [3,6] with scalar f(0)=0, v-f(c) is in F_j by the definition of the pure space. Hence v is constant on each T_a, is constant on each unmasked (c,w) signature, and is zero at every deleted clean zero. Consequently
    L Dv = v - sum_a v_(T_a) 1_(T_a)
is itself a bona fide lift of the SAME profile f at the SAME grade, because all those subtractions are genuine pure of grade three. No cost is charged to delete clean zero or to repeat the signatures. In particular the retained operations
    B Dv = D A(L Dv),     X Dv = D C(L Dv)
are restrictions of genuine grade-(j+1) lifts of Jf and xf, respectively, when j+1<=6. Both new scalar profiles still vanish at zero. Iteration is licensed: for example B^2 Dv=D A(L D[A(LDv)]), and the intermediate inserted/zeroed vector is again a genuine lift by the same rule, now at grade j+1. The difference
    R_B Dv=(X B - B X - B^2) Dv
therefore lies in D F_(j+2) for j=3,4. This assertion does NOT identify R_B with D(CA-AC-A^2)L, and does not treat B as an order-p method. It uses only the licensed composed lifts and the scalar identity xJ-Jx=J^2. Since U disappears under D, its pure output restricts to w times a polynomial of degree at most j-1 on ALL dirty rows and to zero on ALL clean rows. The reduced matrix diagonal is -B_ii^2.

Any explicit input f(c)+wq(c) with f(0)=0 used below is available at grade max(3,deg f,3+deg q), after clearing the masks by their true indicators. This convention applies even to f=x,x^2, so the low-degree probes have cost three, not one or two. The A-images of grade up to five on clean rows still equal Jf, since D F_(j+1) vanishes there. The nonzero clean coordinates of D theta are P(c). Although theta itself need not have profile zero at the origin, only x theta (grade four) and x^2 theta (grade five), both with zero scalar constant, are passed into the reduced proof operators. The test establishing existence of a clean nonroot was instead performed on the original array. In what follows h denotes Dw, P_m the polynomial space of degree at most m, and all residue evaluations are on actual retained rows.

## First clean clock and the exact four-donor interface

The retained list has at least five distinct dirty clocks and at least one nonzero clean clock. Denote the earliest clean clock by u. At least four dirty rows precede u: at this clean row B(hq)=0 for all q in P_2 (actual cost at most five). On at most three earlier dirty knots the three-tap Vandermonde forces all the corresponding incoming B-coefficients to vanish, as h never vanishes dirty. The only remaining possible contribution on the two inputs x and x^2 would be its own tap. Their exact clean primitives would require B_uu=u/2=u/3, impossible. This uses corrected grade-three lifts of x and x^2, not a claim about the row sums of B.

First suppose at least five dirty rows precede u. Write z_1,...,z_5 for the first five dirty clocks and d_i for the corresponding rows. For m=3,4 any polynomial V in P_m is attainable on every dirty row by a grade-m origin-cleared lift: use physical values f(c)+t h, where t=V(0)/P(0) and f=V-tP. For i=4 and i=5 choose V=product_(j<i)(x-z_j) of degree m=i-1. The input pivots at d_i. Its R_B-image is zero on all preceding dirty rows by lower triangularity. Its guaranteed hP_2 or hP_3 form then makes it zero on every dirty and clean row, by the previous three or four distinct dirty knots. Thus B_(d4,d4)=B_(d5,d5)=0. The d_4-pivot input, globally killed by R_B, gives R_(d5,d4)=0 as well. For these consecutive explicit rows this entry is (z_5-z_4) B_(d5,d4), so B_(d5,d4)=0. Thus d_4 and d_5 use only the same first three retained predecessors. The common-predecessor contradiction below applies.

It remains that exactly four dirty rows precede u. The first clean clock not a root of P, say v, is necessarily explicit: x theta first becomes nonzero there, while R_B(x theta) is pure of grade six and vanishes clean. The exact clean B-primitives of x theta and x^2 theta are consequently zero there, so J[xP](v)=J[x^2P](v)=0. If u preceded v, both numerical inputs vanish through u and the same two local moments vanish at u. Then J^2[xP]=xJ[xP]-J[x^2P] has a triple zero at 0 and double zeros at the two distinct nonzero u,v, exceeding degree at most six. Therefore u=v, P(u) is nonzero and u is explicit. Its four incoming dirty taps times P(z_j) lie on the null line of the three-moment Vandermonde; they cannot all vanish by the primitive of x at u and hence all four are nonzero. Write d=d_4. The grade-three d-pivot previously described still has R_B-image zero everywhere, and d is explicit. At u this equality gives (u-z_4) B_(u,d)=0, so z_4=u exactly. This deals with the possible cross-set coincidence without assuming it in advance.

The fifth dirty row must occur immediately after u in the retained list. If there is no second nonzero clean clock, this is already true. Otherwise suppose a SECOND clean row of clock v appeared first. Pick any f in P_5 with f(0)=f(u)=Jf(u)=0. There is q in P_2 such that f(c)+h q(c) is zero on the first four dirty rows. Indeed the four h-weighted evaluations of q form a rank-three space annihilated by the nonzero incoming tap row at u; those same taps annihilate the four f-values by the true primitive Jf(u)=0. The input also vanishes at u. Hence B applied at the putative next clean row must give Jf(v)=B_vv f(v). The primitives of the admissible f are exactly x^2(x-u)^2 P_2. Their value and derivative at distinct v not in {0,u} are independent, contradiction. If other chronological duplicates or a clean zero originally intervened, the finite-grade projection above had already justified dropping them.

Write e=d_5 and w_*=z_5, necessarily w_*!=u=z_4. The consecutive retained rows are d,u,e. Pick a grade-four lift attaining product_(j<=4)(x-z_j) on dirty rows as above. Adjust its value at u to zero by adding a multiple of x theta, whose numerical value there is uP(u)!=0 and which vanishes dirty. The lift first becomes nonzero at e. Its R_B-image is hP_3 and vanishes at all four earlier dirty knots, hence everywhere, so e is explicit. Independently R_B(x theta) itself is zero by those four dirty knots. At e the only possible contribution is from clean u; this gives (w_*-u)B_(e,u) uP(u)=0, so B_(e,u)=0. Evaluating the d-pivot's zero R_B-image at e now gives R_(e,d)=0. The output tap through the only internal row u is already zero, and d,e are explicit; hence R_(e,d)=(w_*-u)B_(e,d), so B_(e,d)=0. Again d and e use only the same first three retained predecessors. In the original six-distinct-ghost/unmasked order-11 chart these are true physical RK tap zeros. With masks or duplicate rows the proof only needs the proved zeros of B.

## The double-origin-jet contradiction

In either retained prefix let V consist of pairs (f,q) in xP_3 times P_1 such that f(z_j)+P(z_j)q(z_j)=0, j=1,2,3. Its dimension is at least 4+2-3=3. The map to f is injective since h is nonzero at these three distinct knots and deg q<=1. For each pair, input f(c)+h q(c) is a genuine grade-four trace, zero on the common first three rows. By the no-tap result its B-image is zero on all five dirty rows. The genuine F_5 discrepancy there lies in hP_2. Thus the evaluations of Jf on those five rows belong to the evaluations of P P_2. The map f to these evaluations is injective: Jf has a double zero at zero, degree at most five and cannot vanish at five distinct knots (even if one is zero). In particular the image is the ENTIRE three-space of evaluations of P P_2. So each of P and xP can be changed into a polynomial Jf with a double zero at zero by adding a constant multiple of the degree-five nodal polynomial H_5=product_(j=1)^5(x-z_j): both polynomials involved have degree at most five and agree at all five sites. This is impossible: (P(0),P'(0)) and (0,P(0)) are independent, whereas the value-and-derivative jet of all constant multiples of H_5 spans at most one dimension. This contradicts equality f_6=f_3+3 in all cases and proves the theorem.

The general jet codimension bound (for other grades, support counts, higher origin vanishing and common predecessor sets) and a standalone executed symbolic replay appear in dirk_p11_five_dirty_common_predecessor_christoffel_six_ghost_branch_excluded_20261123.md and dirk_p11_five_dirty_common_predecessor_double_jet_replay_20261123.md. All inequalities in this proof are dimension inequalities; none orders unknown coefficients or unknown numerical roots.

## Immediate endpoint consequences and limitations

For any unrestricted, normalized p11/s13 candidate the completely known native rank budget 4<=f_6<=5 now forces f_6=5, discarding BOTH the five- and six-distinct-dirty alternatives of f_6=4, not only a fixed quadrature support. This conclusion needs no reflection lemma, D_3 classification or inverse weights beyond the cited native f_6 cap. At p13/s17 and analogous anchored boundaries any branch stipulating minimum ordinary f_6=4 is likewise empty. Do not infer d_6>=d_3+4 for arbitrary true marked row flags: two marked inputs have no general paid product. Whole-array count for j=6 only: if p>=9, strict native E growth through p-3 yields at least dim E_6 +p-9 stages; the separated scalar dimensions of E_6 are at least 1+min(6,p-6) in the g=0 case using the actual zero origin, or 1+min(6,p-7) without that anchor. This alone does not beat the already reported unrestricted integer intervals through 20. Additional dimension-profile arguments may now fit, but are not included as new endpoints in this note.
## Generic rank floors, without the specialized endpoint charts

Run the existing native-rank recurrence of dirk_two_surpluses_even_horizon_20261123.md with and without the new grade-six constraint. The independent rank inputs used in that recurrence are the ordinary/anchored scalar separation, strict forward E growth through p-3, the established terminal-cardinal equality bonus where 2j+epsilon<=p-1, and the one/two-surplus dyadic lower bounds at their original authorized horizons. This uses no marked multiplicative closure. The two entries in each parenthesis are the C(2) and nonzero-g alternatives; the first pair is before, second after this theorem. Replayed exact integers:

~~~text
10 (11, 12) (11, 12)
11 (13, 13) (13, 13)
12 (14, 15) (15, 15)
13 (16, 16) (17, 17)
14 (17, 18) (18, 19)
15 (19, 19) (20, 20)
16 (21, 21) (21, 22)
17 (23, 23) (23, 23)
18 (24, 25) (24, 25)
19 (26, 26) (26, 26)
20 (28, 28) (28, 28)
~~~

Thus the generic native argument alone now recovers the current lower endpoints at orders 12, 13, 14 and 15. At order 14 an eighteen-stage candidate has to satisfy C(2), even before any more specialized argument. The generic order-16 nonzero-g bound becomes 22. These are strengthened branches and shorter proofs of known bounds, not newly higher unrestricted integers.

~~~python
def endpoints(p,tight):
    ans=[]
    for e in (0,1):
        f=[0,0,e,1+e]
        for j in range(4,p):
            z=f[j-1]+1
            if tight and j==6 and p>=8: z=max(z,f[3]+4)
            if j%2==0 and j>=8 and j+2<=p: z=max(z,f[j//2]+j//2+1)
            if j%2==0 and j>=10 and j+2<=p: z=max(z,f[j//2-1]+j//2+3)
            f.append(z)
        v=[]
        for j in range(2,p):
            h=min(j,p-1-j,(p-1)//2) if e else min(j,p-j,p//2)
            bonus=int(j<=p-3 and 2*j+e<=p-1)
            v.append(f[j]+h+1+max(0,p-3-j)+bonus)
        ans.append(max(v))
    return tuple(ans)
for p in range(10,21):print(p,endpoints(p,False),endpoints(p,True))
~~~
## Sharpness of the uniform constant

The previously verified eight-stage order-eight DIRK with a genuine zero first row (dirk_order8_eight_exact.md; an independent Lobatto-style witness is checked in dirk_lobatto_p8_p9_p10_characteristic_zero_20261123.md) has f_6<=5. Indeed its quadratic scalar evaluations form a three-dimensional space separated from F_6 by the origin: a coincidence H(c) with H of degree at most two forces H(0)=0, and testing under x dx with all polynomials through degree one is allowed at 6+1=7. Since f_3>=1, the present theorem forces f_3=1 and f_6=5 for that witness. Thus +4 is best possible uniformly for p>=8, even for real coefficients; no new claim of a higher-order witness attaining equality is made. A compact characteristic-zero proof of all four familiar endpoints without parameter-dependent spectral or Jacobi tests is dirk_orders12_through15_short_native_lower_endpoints_from_grade_six_20261123.md.
