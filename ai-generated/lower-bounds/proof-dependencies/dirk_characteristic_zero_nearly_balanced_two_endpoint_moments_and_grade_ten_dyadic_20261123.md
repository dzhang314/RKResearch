# A field-independent two-pivot multiplicity bound and the grade-ten doubling gain

Formal integrals are over any characteristic-zero field. Let m≥1, a,b≥0 integers, u,v nonzero distinct elements, deg P≤2m−1 and f=x^a(x−u)^b P. If all m+1 moments ∫₀ᵘ x^i f=0 (0≤i≤m) and all m moments ∫₀ᵛ x^i(x−u)f=0 (0≤i<m) hold, then P=0. No sign, root-reality or fixed-node assumption is needed.

Put F=J^(m+1)f. It vanishes at zero to order at least m+1+a. At u, the first moments express F,F′,…,F^(m)=0, and F^(m+1)=f vanishes there to order ≥b. Therefore
    F=x^(m+1+a)(x−u)^(m+1+b)D,    deg D≤deg P−m−1.
But J^m[(x−u)f]=(x−u)F′−mF equals
    x^(m+a)(x−u)^(m+1+b) { [(m+2+a+b)x−(m+1+a)u] D + x(x−u)D′ } .
For D nonzero the bracket has degree deg D+1, since its leading nonzero coefficient gains the positive integer deg D+m+2+a+b. By deg P≤2m−1 this is at most m−1. The second moment family requires a root of multiplicity at least m at v, away from both displayed endpoint factors: impossible. This single rational differential identity proves all assertions, including fields with no embeddings in the reals. For m=3 and a=1,b=0 it excludes every QUINTIC from the 4+3 tests; for m=2 it excludes cubics, not arbitrary complex quartics. The latter distinction is exactly the old 3+2 quartic field obstruction.

**Unconditional field-safe native doubling.** For every d≥5 and p≥2d+2, ordinary lower triangular RK has f_(2d)≥f_d+d+1. Suppose contrary all d increases from F_d through F_(2d) are unit. Incoming/outgoing Hermite and split-diagonal unit-band compression give the actual flag
    F_j=U⊕wP_(r+j−d−1), d≤j≤2d,
where the first r head powers already cost d, and at least r+d+1 effective nodes remain modulo U because F_(2d) is noninvariant. Products of F_d members lie in F_(2d): applying this to node-local u∈U gives U⊙F_d⊂U, by the number of other effective sites versus the head degree r+d−1. Thus U is a site-class algebra and w can be taken zero on supp U=T. The 2r−1 consecutive products c^i w² in F_(2d) now show w=P(c) on supp w for a nonzero polynomial of degree ≤d+1−r≤d, using the identical adjacent-coefficient root count as at grade ten. Construct θ=P(c)(1−1_T)−w, an actual lift of grade ≤d, nonzero only on clean positions where it equals P(c) and every F_(2d) vanishes. The first mask xθ must be nonzero, for otherwise testing the zero lift's profile xP against every q∈P_d through (d+1)+d≤p−1 contradicts the fixed rational x dx Gram. At its first physical nonzero stage u≠0 its commutator at grade d+3≤2d forces zero diagonal, and its primitive tests through F_(2d) give all d−1 moments of xP at u (degrees 0,…,d−2). At the first surviving stage v of x(x−u)θ its commutator at d+4≤2d gives zero diagonal, and all d−2 moments of (x−u)xP at v follow. Here m=d−2 and d≤2m−1 since d≥5. Thus the proposition excludes P. If x(x−u)θ is identically zero, its profile still gives the same second moments with v=1 by the output test. If u=1, the affordable output moments for x(x−1)P through degree d−1 (cost d+2+d−1=2d+1) successively supply the two missing moments of xP, completing the fixed x dx Gram on P_d. This covers all physical and field cases. For d=5 this strict gain is f₁₀≥f₅+6 at p≥12. One does not need the refunded fifth-debut for this length-five window; that theorem remains essential to the shorter F₅–F₇ chart and to p18/p19 where only F₉ is clean.

This is a coefficient-field extension of an already established real rank inequality. It does not assert the d=4 borderline over complex fields at the tight p≥10 horizon. The signed-square-free Gram and chronological unit-band lemmas used here are in dirk_field_audit_refunded_cuts_and_order12_over_characteristic_zero_20261123.md.
## Two-surplus transfer for d≥6, and the absolute grade-ten bound

For d≥6 and p≥2d+2, one also has f_(2d)≥f_(d−1)+d+3 over every characteristic-zero field. This is the field-safe version of dirk_two_surpluses_even_horizon_20261123.md. Put b₀=d−1. If false, the first-gain theorem just proved at b₀≥5 and all strict growth imply that exactly one double step intervenes between F_b₀ and F_(2d), landing at some t≤2d−2. If t=d, the already-proved first-gain theorem at d rules out the remaining unit steps immediately. Otherwise t≥d+1. This proof also applies at d=5 if the one surplus is KNOWN to land by grade 8; it does not simply assume that grade-eight fact in characteristic zero.

F_b₀ up to F_(t−1) and F_t up to F_(2d) are noninvariant through their entire unit bands by the incoming/outgoing Hermite bounds (incoming at t−1≥5 and at 2d). Algebraic unit-band decomposition gives an early head g, early invariant U₀, r=f_b₀−dim U₀≥1; late head w, late invariant U, with U₀⊂U. V_t=U₀+gP_(r−1+t−b₀) has rank f_t−1 inside F_t, by the last early noninvariance. V_t is not contained in U, since then f_(t+1)≥f_t−1+floor(t/2)>f_t+1 as t≥6. Write g=wL+e, e∈U, L≠0. Comparing the true powers of g up to r−1+t−b₀ in F_t, at the at least f_(2d)−dim U+1 effective w sites, proves deg L≤1−δ where δ=dim U−dim U₀ is 0 or 1. If δ=1, the split diagonal on U/U₀ has one clock α; U and U₀ coincide on all other nodes.

Here are the required replacements for real orthogonality in the source argument. At any unaffected site, for u local in U=U₀ and a∈F_b₀, the product au is in F_(2b₀) and node-local; this is a late band with too many other effective sites, so au∈U. Choose complements to this U simultaneously in the joint coordinate-value blocks of C and all diag(a), a∈F_b₀. Such complements exist because these commuting diagonals split and preserve U on the site. Change g by its U₀ projection and w by its U projection there, choosing arbitrary nodewise complements elsewhere. This keeps all true head modes at their respective original grades. Then on each unaffected block e=0, and g² is in the chosen complement since it is diag(g)g. The late head coefficient q of g² has deg q≤b₀+2−r−δ: compare the 2r−1 genuine consecutive products C^i g² in F_(2b₀). These comparisons are polynomial equalities because the ending late band is noninvariant. On unaffected w coordinates we therefore have g=wL and g²=wq, hence q=Lg. The polynomial q is nonzero: on the affected site (if any) one could lose one effective node and deg L≤1 loses at most another, whereas there are at least 2d−t+2≥4 effective sites. At a remaining site some coordinate w≠0, so g and q are nonzero there.

Set B=1 for δ=0, B=x−α otherwise. Take P=Bq, f=B(C)L(C)g; deg P≤b₀+2−r≤d and deg(BL)≤1, so f∈F_d. On every w coordinate P(c)=f, including the exceptional block. The diagonal diag(f) preserves U (away from α by the local multiplier argument; it is zero at α). For either Q=x or Q=x(x−u), z_Q=Q(C)[P(c)−f] has grade at most d+deg Q. If z_Q∈U it has a pure representative at grade b₀, because in the δ=1 case it vanishes at α; otherwise U=U₀.

If z_Q∉U, use its earliest original prefix not matchable by U and a joint-(C,diag f) block row functional λ supported within this prefix, killing U but not z_Q. The joint block contains a single nonzero value of z_Q and no w coordinate, so normalize λ1=1; then λ kills F_(2d). Choose a single u′∈U matching z_Q STRICTLY before that last physical position i. Both Rz_Q and Ru′ lie in F_(2d), since d+4≤2d and t+2≤2d. The physical pivot of R(z_Q−u′) then gives zero diagonal at i. For every T with deg T+deg Q≤d−1, AT(C)u′∈F_(t+1) since U is C-invariant, and λA T(C)(z_Q−u′)=0 by the explicit physical pivot. Hence J(TQP)(c_i)=0. The first mask cannot belong to U by the zero-vector scalar tests ∫xPq for all q∈P_d. Apply the displayed moment result at m=d−2 to the two pivots with Q=x then Q=x(x−u). If the second mask instead belongs to U, its cheap pure representative and the scalar tests give the missing moments at v=1; if u=1 use the two additional output moments exactly as in the ordinary one-surplus proof. This proves the two-surplus result.

In particular one does NOT need a complex grade-eight dichotomy to obtain the **absolute** f₁₀≥10+ε (ε=0 when C(2) holds and 1 otherwise) for p≥12. Indeed f₃≥1+ε, f₆≥f₃+4, and strict growth through ten show f₁₀≥9+ε already. At that exact lesser value f₆=5+ε and all later steps are unit. The single-gain theorem at d=5 forces f₅≤3+ε, hence f₅=3+ε, f₄=2+ε by strict growth. There is exactly ONE double step after grade four and it lands at t=6, not at the unproved borderline t=9. Thus the previous proof with b₀=4, d=5, t=6 applies verbatim, contradicting f₁₀=f₄+7. For p20 this gives a characteristic-zero lower bound s≥28 by grade-ten scalar separation (ten unanchored or eleven anchored polynomial dimensions) and seven strict increments to E₁₇, without asserting any full f₁₀≥f₄+8 at d=5 in fields not ordered.
Independent exact BigInt factor/differentiation replay for 396 homogeneous test monomials (u normalized to 1). This is a sanity check on constants and multiplicities; the written polynomial identity is universal.

```javascript
const add=(a,b)=>{let c=Array(Math.max(a.length,b.length)).fill(0n);for(let i=0;i<c.length;i++)c[i]=(a[i]||0n)+(b[i]||0n);while(c.length>1&&!c[c.length-1])c.pop();return c;};
const mul=(a,b)=>{let c=Array(a.length+b.length-1).fill(0n);for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)c[i+j]+=a[i]*b[j];return c};
const sc=(a,n)=>a.map(c=>c*BigInt(n)),X=[0n,1n],xm=[-1n,1n];
function pw(a,n){let s=[1n];while(n--)s=mul(s,a);return s}
const D=a=>a.length===1?[0n]:a.slice(1).map((c,i)=>c*BigInt(i+1));
const dd=(a,k)=>{while(k--)a=D(a);return a};
const eq=(a,b)=>a.join(",")===b.join(",");let num=0;
for(let m=1;m<=8;m++)for(let a=0;a<3;a++)for(let b=0;b<3;b++)for(let k=0;k<=m;k++){
  const h=pw(X,k);
  const F=mul(mul(pw(X,m+1+a),pw(xm,m+1+b)),h);
  const L=add(mul(xm,D(F)),sc(F,-m));
  const br=add(mul([BigInt(-m-1-a),BigInt(m+2+a+b)],h),mul(mul(X,xm),D(h)));
  const R=mul(mul(pw(X,m+a),pw(xm,m+1+b)),br);
  if(!eq(L,R)||br.length!==k+2||!eq(dd(L,m),mul(xm,dd(F,m+1))))throw Error("bad");
  num++;
}
console.log(num);
```
Output: 396.
