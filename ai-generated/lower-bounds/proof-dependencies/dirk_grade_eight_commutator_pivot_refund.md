# Commutator pivot refund: the grade-eight DIRK dichotomy and order seventeen

For unrestricted real lower triangular classical Runge–Kutta, write C=diag(c), c=A1, E_j for the evaluated rooted-tree stages through grade j (order minus one), and F_j for the evaluated combinations with zero scalar polynomial profile, f_j=dim F_j. The profile of A v is JH, J integration from 0 to x, when v has profile H; C acts by x, and componentwise products multiply profiles. We use the established strict forward and backward growth and Hermite amplifier in dirk_grade_nine_double_endpoint_growth.md, with the endpoint argument also independently checked in dirk_reverse_quotient_independent_audit.md.

**Dichotomy.** For p≥13, if f_8=f_4+4, then F_8 is C-invariant. Thus either f_8≥f_4+5 or F_8 is invariant and gains at least four extra dimensions at grade nine (f_9≥f_8+4). In the second alternative, degree-four polynomials separate from F_8 by 8+4≤p−1, so there are at least five detected nodes including at least four nonzero, and the four-row DIRK Hermite amplifier has degree bound nine, since 2·4≤8. This statement does not assert f_8≥f_4+5 unconditionally.

Suppose f_8=f_4+4 and F_8 is not invariant. All four growth steps are single. F_j for j=4,…,7 cannot be C-invariant, by the two-row Hermite gain. In the rank-one orthogonal compression argument of the grade-nine note, write F_4=W⊕w P_(r−1)(c), where W is C-invariant, each C-power of w is orthogonal node by node to W, and r≥1. Since each F_j through seven gains just one, those spaces expand by successive head powers:
    F_j=W⊕w P_(r+j−5)(c),  4≤j≤8.
In particular at the end there are r+4 independent powers of w. Since even F_8 is assumed noninvariant, the number N of distinct effective head nodes is at least r+5. Any node-local member of F_8 must then be in W: its head polynomial has degree ≤r+3 and would vanish at ≥N−1 other nodes. For node-local d in W and a∈F_4 the product da∈F_8 is local, hence belongs to W. Thus W is a componentwise algebra and preserves F_4 under multiplication into W. Its support T has indicator 1_T∈W (take powers of a generic member and interpolate to 1 at all its nonzero values and 0 at zero). Because w⊥W and 1_T w∈W, w vanishes on T. Write S for its support. The products C^k w² lie in F_8 for 0≤k≤2r−2. They vanish on T, so after dividing by w on S they give polynomials P_k of degree ≤r+3 representing x^k w there. At N≥r+5 nodes P_(k+1)=xP_k identically; hence w=P(c) on S for a nonzero polynomial P of degree ≤5−r≤4. All of F_8 vanishes away from S∪T.

**Pivot refund.** R=CA−AC−A² sends E_d to F_(d+2), since xJ−Jx−J²=0 on polynomials. At the earliest nonzero coordinate i of v, triangularity gives (Rv)_i=−a_ii² v_i. Hence if F_(d+2) vanishes at i, that pivot is explicitly forced to have a_ii=0. No diagonal sign or zero hypothesis is assumed.

Use Q=x, then Q=x(x−u). In either case the mask
    v=(QP)(c)(1−1_T)−Q(C)w
has profile QP and grade ≤4+deg Q. In fact (QP)(c)1_T belongs to W by C-invariance. The mask cannot vanish identically, since then (QP)(c) is a pure defect of grade ≤6 and the positive-square test fits through grade twelve. It vanishes on S∪T. At its earliest nonzero coordinate i, write η=c_i; Q(η)P(η)≠0, every vector in F_8 vanishes there, and the refund applies as 4+deg Q+2≤8 in both tests. Then even A C^k v evaluates to zero at i for 4+deg Q+k+1≤8. Its exact profile, whose difference from its scalar evaluation is in F_8, gives
    ∫₀ᵘ xP(x)x^k dx=0  (k=0,1,2),
    ∫₀ᵛ x(x−u)P(x)x^k dx=0 (k=0,1),
where u≠0 and v≠0,u. Let t=v/u. The degree-≤4 polynomial P(ux) is orthogonal to degrees ≤2 for weight x on [0,1], so it is in the span of J_k(x)=Jacobi(k,0,1,2x−1), k=3,4. The determinant of the remaining two-by-two moment matrix of ∫₀ᵗ x^(i+1)(x−1) J_k(x) dx (i=0,1; k=3,4) is
    t^6(t−1)^6(15t²−24t+10)/8.
The quadratic has negative discriminant, so no real t≠0,1 can work. This contradiction proves the dichotomy. Exact replay:
~~~python
import sympy as s
x,t=s.symbols('x t')
J=[s.jacobi(k,0,1,2*x-1) for k in (3,4)]
M=s.Matrix([[s.integrate(x**(i+1)*(x-1)*g,(x,0,t)) for g in J] for i in range(2)])
assert s.factor(M.det()-t**6*(t-1)**6*(15*t*t-24*t+10)/8)==0
~~~

**Unrestricted bound: s_DIRK(17)≥23.** Write g=Ac−c²/2. If g≠0, f_4≥3 and strict growth gives f_8≥7. At f_8≥8, the separated scalar space P_8 gives dim E_8≥17 and six more strict gains up to E_14 give s≥23. At f_8=7 the dichotomy gives f_9≥11, so dim E_9≥11+8 by separation of P_7 (grades 9+7=16); five further gains give s≥24. If g=0, the first row is zero, f_4≥2 and f_8≥6. At f_8=6 the dichotomy gives f_9≥10; P_8 separates at grade nine by the H/x anchored test (9+7=16), hence dim E_9≥19 and s≥24. At f_8≥7, dim E_8≥16 and s≥22. If s=22 all the reverse gains through E_14 and the midpoint lower estimate are saturated. A trailing zero weight could be trimmed, contrary to the already established unrestricted lower bound 22. Thus D1=D2=0, c_s=1, Ae_s=0 and e_s∈E_8, as in the audited reverse quotient proof. Write e_s=H(c)+f with f∈F_8; then H(0)=0. Testing against (1−x)H/x, degree at most eight, gives ∫x(1−x)(H/x)²=0 through grade 16, thus H=0 and b_s=0, contradiction. This completes the order-17 result. All node values, weights and diagonal positions were unrestricted.

Further application to order fourteen is being investigated. The grade-eight dichotomy alone gives no order-fifteen increment.

Verified the two selected stages, explicit-diagonal refund, rank cases and terminal test. Root independently reconstructed the Jacobi coefficients and exact rational polynomial convolution, confirming the determinant through every monomial. Lower p17 updated to 23 and David notified at 06:10 UTC.
