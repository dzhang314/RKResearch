# Candidate unrestricted real explicit bound s(18)>=29: closure of the final one-node D2 mergers

This finishes the two surviving charts of erk_order18_28_three_node_weighted_feeder_20261123.md. Together with the predecessor eliminations, no real strictly lower triangular 28-stage order-18 RK tableau exists. No node signs, ordering, distinctness, nonzero-weight or other simplifying restrictions are imposed. The independently established smaller-count lower bound was 28. No upper bound or other order is claimed changed here. Independent review is requested before changing the canonical table.

## Exact premises

The preceding results leave a single-node d=N(Yb)-Y²b/2; D1=0; F8,F9 have dimensions 9,10, F9 terminal-zero, e_s in E9, b_s=1/90, and H(c)-e_s in F9, H=x (d/dx) Legendre(9,2x-1)/90. A row on which F9 vanishes has its abscissa on the ten-point Lobatto grid Z. Use the coupled adjoint flag M_j. We have M2=span(d), dim M3=2, M4=3, M5=5, and M3,M4 both noninvariant (for M4 the two-prefix weighted feeder is essential). From grade five through nine the flat, nonsaturating rank-j flag is
    M_j=U direct-sum tau P_(j-u-1)(Y).
Here U is diagonal invariant of dimension u=1 or 2, tau is nodewise orthogonal to U, all local vectors in M9 belong to U, and tau lives on m>=10-u nodes. Indeed M9 cannot saturate since the next terminal-zero Hermite target has dimension at most 12; see the early-surplus note. Each vector in U has zero coordinate sum at every node. Tau has moments zero through degree 16-u, since its 4-u shifts already in M5 annihilate E12. M9 is the full terminal-zero annihilator of E8. The one-node elementary reverse chronology ensures g=Nd is independent of d (details below), so M3=span(d,g) and M4=span(d,g,Yg). Choosing the grade-three generator modulo d, it projects to tau T with degree T<=2-u (g,Yg,Y²g in M5); the polynomial T is nonzero since M4 is noninvariant. At u=2, after subtracting a d multiple from g and rescaling tau, this gives
    g=tau+e,  g in M3,  e in U supported at a single node beta.
The vector e may be zero; if zero choose beta to support a generator of U orthogonal to d. In all cases U=span(d,e0) with e0 supported at beta, choosing e0 independently if needed. Since U is real diagonal invariant, the orthogonal complement of d in U is a one-dimensional diagonal eigenline. At u=1, whether or not the generator was so normalized, every vector in M5 on the d node belongs to span(d_local,tau_local); at every other node the M5 restrictions have dimension at most one. These local dimensions, not its total rank, suffice for the next exclusion.

## u=1: the earlier chronological proof needs only local ranks at the exceptional repeats

Use the three exhaustive one-node d chronologies in pass2345_q7analytic.md (section on localized L2) and pass0045_q6_odd.md (first sections and Completion). The latter proof at the time assumed dim L5=4. We do NOT reuse that rank here. All its nonexceptional determinant and continuation steps use ONLY D1=0, the one-node d, and the bases of grades three and four just stated. The sole uses of a quadratic-in-g polynomial form at grade five were at the three exceptional repeats listed below; in each we replace it by a direct local test.

Normalize the nonzero d abscissa to 1 by rescaling Y,N for these chronology calculations only, and write v for the reversed b. The first nonzero Y v is at 1, with d=-v/2. At the first subsequent independent local feature r at node 1 before any other active node, Nd=-(d+v/2)/2 is nonzero there. Otherwise at the first active off-node y not in {0,1}, before any such r, (Nd)_y=-y²v_y/4 is nonzero. At the first nonzero d row itself Nd=0. An off-node must occur by scalar quadrature, so the actual unnormalized generator g=Nd is indeed independent of d. Call a local feature independent when v+2d is nonzero at that repeat. The three determinant systems and exceptional minors were independently re-evaluated in the attached exact SymPy replay.

* If r is before y, the ordinary induction excludes every new active node and forces all carried features even on ghosts, except the singular repeat x=y=2. At the first row carrying the active y, g_y=y²(2y-3)v_y/4 is nonzero for y=2. The grade-five vector N(Y-1)g is zero at that first y because all earlier nonzero g were at 1. Since y is not the d node, M5 restricted there has dimension at most one, and g already probes it nontrivially at that row. Hence the vector vanishes at EVERY y repeat. This supplies exactly the old omitted equation, forcing the incoming sum S_y=0 and restoring the induction.
* If y occurs before r, and r before the next distinct active off-node, the only singular repeat is x=1 at y=1/2. The vector N(Y-y)g is zero at the first nonzero d row and at r because before r nonzero g is restricted to y. The earlier relations give g=0 with d nonzero at the first of these two rows, and g_r=(2-3y)(v_r+2d_r)/(4y) nonzero at the second. Thus these two rows separate span(d,g) at the d block; the ENTIRE restriction of M5 there has dimension at most two. The grade-five vector consequently vanishes at every repeated 1, exactly the constraint needed to restore S_1=-2g.
* If the second off-node z occurs before r (or r never occurs), the only singular repeat is x=z with y=z/2. The first active z has g_z=z²(2z-3y)v_z/(4y) nonzero, while N(Y-y)g there is zero since all earlier nonzero g were on y. On z outside the d node, M5 restriction has dimension at most one. Again it vanishes at all z repeats, implying S_z=0 as required.

The cited proofs show by the explicit four linear equations at each subsequent row that outside the exceptional repeats no other freedom is needed; the three normalized determinants and their two critical minors in each case are also printed by the replay. The forbidden-y denominator cases were already eliminated at the first relevant rows by Ng; no grade-five assumption enters. Thus at most four distinct nodes can carry v in all three cases, contradicting exact integration of the square of their vanishing polynomial. Arbitrary ghosts and repeated nodes are included; the rescaling used inside the identities does not affect this positivity statement on the original interval. This excludes u=1.

## u=2: exact quartic hidden algebra; usable traces off the lone extra reverse node

Now tau annihilates P14, m>=8 (the stronger m>=9 from the lagged argument is not necessary below). At F_j for j<=4 the full ordinary representations and hidden-mask algebra of erk_order18_28_localized_early_surplus_20261123.md still work. Indeed U and tau, Ytau, Y²tau are all in M5; products at grade j<=4 and their further shifts fit in M9. Every f in F_j thus preserves U, and
    tau f=tau Q_f,  Bf=u_f+tau P_f,  deg Q_f<=j, deg P_f<=j-3.
In the comparisons the maximal degree after one shift is seven, less than m>=8. Define exactly as in that note the invariant algebra K of endpoint-zero z satisfying tau z=0, Bz in U and z U subset U. Its disjoint node-class masks are pure in F9 (M9 full and the origin P/x test); the reverse 3+2 quartic proof implies F4 subset K. The two forward class-summed primitive feeders and the maximal-forward-invariant cap give 4<=k=dim K<=5. These arguments import only the grade-four feature identities here, not any grade-five version.

Write J for the full beta block, lambda(y)=y-beta. Off J, every f in F5 or F6 preserves the localized pieces of U: only d can remain there and f d lies in M_(j+2), hence is a single-node vector in U. If its abscissa is not beta its local U is precisely the span of d. Consequently f also preserves each K-mask off J (its product with such a mask stays in K) and is constant on that mask.

For h in F5 the grade-three g=tau+e supplies gh in M8=U+tau P5. Off J, tau h is orthogonal to U by the just-proved preservation, so
    tau h=tau Q,   Bh=u_h+tau P off J,   deg Q<=5, deg P<=2.
The second formula follows from Bh in M5; u_h in U. No assertion about tau h on J is needed. A grade-six head w with w,Cw,C²w all in F6 instead satisfies the SAME identities off J with the STRONGER caps deg Q<=4 and deg P<=1: apply g to all three at grade nine (head cap six), B to them at grade six (head cap three), and compare consecutive representatives at the at least m-1>=7 outside tau nodes. For the degree-six chain comparison, a shift could reach degree seven, so one needs m-1>=8. This does hold: if m=8 the full tau orbit plus U, dimension ten, is already in M10 as M9+YM9; tau has zero aggregate at its eight nodes and U is localized with zero sums. The lagged degree-nine Hermite argument into the terminal-zero annihilator of E6 in the early-surplus note gives 15>14. Thus m>=9 and all outside comparisons are valid. The P comparison only needs the weaker count.

If such an h or w has Q=0, it is in K modulo the single beta block: P=0 by projection on the outside tau nodes, and setting its J coordinates to zero gives a vector in K (tau annihilates it coordinatewise; B times it lies in the off-J nodal projection of U; it preserves U, and its endpoints vanish). Its class modulo K is then an eigenvector or zero. In particular Q cannot vanish for any feature outside the maximal forward invariant U_F whose cyclic shifts are used below.

## One common ignored node: the forward and reverse exceptions do not add

We choose a visible h in F5, or a three-shift w in F6, so that outside the K masks and J, wherever this feature vanishes, ALL F9 vanish.

* At k=5, U_F=K, and F5 cannot be contained in it since otherwise f6>=8 by Hermite. Strict quotient growth gives F9=K+hP4 for h in F5 outside K. This proves the assertion.
* At k=4, dim U_F=5, write U_F=K+span(xi), where xi is a single-node eigenvector at alpha. If alpha=beta the same strict quotient argument gives F9=U_F+hP4, which suffices. Suppose alpha is different. For any f=k0+t xi in F5 intersect U_F with t nonzero, (i) xi d is in U using fd in M7 and k0 d in U, (ii) Bxi in U using Bf in M5, Bk0 in U and locality, and (iii) g xi in U using gf in M8 and g k0=e k0 in U, again by locality of xi. Since alpha differs from beta, xi e0=0, so xi preserves U by (i), and (iii) equals tau xi orthogonal to U. Hence tau xi=0 and xi in K, contradiction. Thus F5 intersect U_F is contained in K. As F5 not subset U_F by Hermite, the strict quotient has dimensions exactly one at five and two at six. Since f5>=5 this puts K in F5; Hermite then gives f6=7 and all U_F in F6. But for xi itself in F6, Bxi in M6, d xi in M8, g xi in M9 are all localized, hence in U. The same argument yields xi in K again. Thus distinct alpha,beta are impossible.
* At k=4, U_F=K, the grade-five projection has dimension one or two, by strict growth through the six-dimensional grade-nine quotient and the f5 lower bound. If two, the C-escape is one and the two-space, having no invariant part, is a two-step cyclic chain. Lift its head as h in F5. Its powers generate F9 modulo K by the one-unit increases, so on h=0 off K all of F9 vanish. If one, K subset F5 and Hermite gives f6=7. The three-dimensional projected F6 has only single escapes until grade nine, with no invariant part. Choose its head w, giving F6=K+wP2 and F9=K+wP5. Because K is already contained in F6, all three actual shifts w,Cw,C²w lie in F6, not just their projected classes. This is the direct grade-six g-times-three-shifts case and avoids introducing any second pole from a grade-five representative.

In every case the selected feature f is outside U_F, so its off-J Q is nonzero. All the claimed cyclic decompositions use only the self-adjoint rank-one escape for the actual subspace K+F_j and removal of invariant K, or equivalently its orthogonal complement; strict growth follows because a nonzero invariant part of the quotient would enlarge U_F.

## Finite grid and physical count

With the selected f and its pair (Q,P), use the same U-projection construction as in the early-surplus proof ON THE COMPLEMENT OF J, where f preserves U. There, subtract local U terms from bQ-tau P so that the result lies only on f=0,Q nonzero outside K masks, orthogonal to U in each such block. On nonzero-f blocks with f unequal to Q one has tau=0 and b f in U locally, permitting this subtraction. Set the actual final contrast to zero on J by the node mask. Globally it is
    W=b (lambda Q)(Y) - tau (lambda P)(Y) - u',    u' in U.
This has no requirement that f preserve or be constant on any beta subblock. Off J it is supported on the just-constructed clean blocks, so all its nodes are on Z. The masked density lambda Q is nonzero of degree at most six. Test against polynomials through 11: b quadrature is exact to 17, tau annihilates degree 14 and deg(lambda P)<=3, and U has zero sums. Therefore lambda Q vanishes at every unoccupied Lobatto node. At W blocks its reverse primitive has the usual prefix detection via lambda_i killing U and giving nonzero value on b; y then y(y-a) masks give two moments at one nonzero node and one at a different nonzero node. The residuals of the polynomial primitives are in M9, as are the N images of tau (lambda P)R for deg R<=2 (deg (lambda P)R<=5 and tau P5 subset M8) and the N images of local U matching vectors. Thus this is precisely the genuine sextic, four-hole, 2+1 grid test. The split-prime replay at 8429 proves that all 5,040 assignments have full rank. At least seven distinct W nodes are necessary.

Count the blocks by (Y,f,K) outside J, but ONLY by K classes and their complement inside J. U splits on the resulting partition: off J both f and K preserve it, on J only K is used. Each block costs at least one plus its local U dimension. There are k separate mask blocks, seven distinct W blocks and m disjoint tau macroblocks: outside J a tau macroblock has f=Q, no mask, so is disjoint from W; on J all tau lives outside K, and no W is allowed there. If m>=16 the total is >=2+4+7+16=29. If m<=15, tau annihilates P14 so the separate sums all vanish; tau is orthogonal to local U on its macroblock, which costs at least TWO plus the local U dimension. Then the total is >=2+4+7+2m>=31 by m>=9. This contradiction covers all u=2 possibilities.

The full dependency chain is: nonzero D1 and high-front-rank exclusions; rank-eleven two-ended quintic and endpoint Lobatto; persistent eighth mode; principal and pole exclusions; erk_order18_28_excludes_eigenmode_20261123.md for large n; erk_order18_28_localized_early_surplus_20261123.md and erk_order18_28_three_node_weighted_feeder_20261123.md for small n and the two late mergers; and the present proof. The new order-18 interval would be 29–46 after independent review. An order-16 or order-20 count change is not implied.
~~~python
import sympy as s
x,y,z,v,d,g,A,B,E=s.symbols('x y z v d g A B E')
def cert(eq,Avar,AB,tests):
 e=[s.factor(q.subs(Avar,s.solve(eq[0],Avar)[0]))for q in eq[1:]]
 M,b=s.linear_eq_to_matrix(e,AB)
 D=s.factor(M.row_join(b).det());m=[s.factor(M[[0,i],:].det())for i in [1,2]]
 print('det',D);print('coeff minors',m)
 for sub,t in tests:
  expr=s.factor(D.subs(sub,simultaneous=True)/t)
  assert expr!=0 and not (expr.free_symbols & {x,v,d})
 return D,m
# local rank two at node 1 achieved before first outside node y:
k=1/(3-2*y);gam=y*y*(2*y-3)/4
ee=[A+y*B-x*x*v/2-d,A+y*y*B-x**3*v/3-2*(d-g)/3,A+y**3*B-x**4*v/4-d/2-(-1+k*(y-1)*(x-1))*g,-g/2-A/4+gam*B-k*(x-1)*g]
D,m=cert(ee,A,[g,B],[({},(x-1)*(-2*d*y*y+4*d*y+3*v*x*x*(x-y)**2))])
assert all(s.factor(m[i]/c).free_symbols<={y}for i,c in enumerate([3*x*y-3*x-4*y*y+5*y,3*x-2*y*y+y]))
# first outside y appears before 1 completes, but 1 completes before next outside z:
eta=-y*y/4;ze=(2-3*y)/(4*y);k=y/(3*y-2);kap=4*y/3-2
ee=[A+y*B-x*x*v/2-d,A+y*y*B-x**3*v/3-2*d/3-kap*g,A+y**3*B-x**4*v/4-d/2-(y*y-2-k*(y-1)*(x-y))*g,ze*A+2*ze*g+eta*B-k*(x-y)*g]
D,m=cert(ee,A,[g,B],[({},(x-1)*((12*y*y-14*y+4)*d+3*v*x*x*y*(x-1)*(x-y)))])
assert all(s.factor(m[i]/c).free_symbols<={y} for i,c in enumerate([3*x*y-3*x-5*y+4,3*x*y+y-2]))
# second outside z before 1 completes (possibly never):
k=y/(3*y-2*z);gam=z*z*(2*z-3*y)/(4*y);lap=-k*(y-z)
ee=[-2*g+y*B+z*E-x*x*v/2-d,-2*g+y*y*B+z*z*E-x**3*v/3-2*d/3-kap*g,-2*g+y**3*B+z**3*E-x**4*v/4-d/2-(y*y-2+lap*(x-y))*g,eta*B+gam*E-k*(x-y)*g]
D,m=cert(ee,B,[g,E],[({d:0},v*x*x*(x-y)*(x-z)**2),({x:1},v+2*d)])
assert all(s.factor(m[i]/c).free_symbols<={y,z} for i,c in enumerate([3*x*y-3*x*z-5*y*z+4*z*z,3*x*y+y*z-2*z*z]))
print('all three normalized identities passed')
~~~
