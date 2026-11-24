# Order 19/46 independent audit; obstruction to transferring its twenty-row jet prefix to local-ten ports

**Result.** I independently approve the ERK(19,46) proof and its common root. The constructed 46-stage tableau has order exactly nineteen, and its twenty-stage nonlinear jet prefix cannot attain five distinct positive local-ten sites in 26 stages by ANY extension of its actual rows. The latter is a fixed-donor obstruction, not a changed unrestricted order-twenty bound.

**Audit.** I reconstructed the eleven-row low and central rectangular seed identities; the singleton cancellations, primitive and commutator signs, and terminal pin of the moving-helper reverse bank; the donor and first-/second-jet nonlinear single-bad-child proof; and both the 20-variable directed contraction and the physical assembly in `erk_moving_helper_two_sided_causal_reciprocity_order19_46_20261123.md`. The double-integral interchange gives exactly the factor a/d and correction −W11 I_y11(q) E0 in the two reciprocal scalar dependences. Their last coefficients vanish from the D cardinal and all three B_l; the linear form after eliminating D annihilates Kf by Fubini and therefore also the C cardinal by the rank-one restriction and nonzero pair on Kf. The full coordinatewise 2×2 solve thus has its three upper entries algebraically zero BEFORE the late tree evaluations are used. This proves causal induction, true high observations and the ten literal whole-row pins. With h=|t|−1 a primitive error costs at least 10 vertices. A product at grade ≤18 has at most one, all other factors contribute scalar times a clock power, and the resulting exterior source has h+ell+1≤18. The exceptional joint grade is h=9, ell=8: F_i kill its residual individually, the physical origin is genuinely pinned and the reflected origin has identically zero incoming. The six zero reflected columns transpose to six zero internal suffix rows whose entire cross-rows are the true scaled pinned incoming rows; merging preserves all B-series coefficients. No gap found.

**Exact degree.** Let a_n=binom(2n+2,n) and Q=P10+λP9+βP8+νP7 with the shifted Jacobi normalization in the source. The monic nodal polynomial is N(v)=v(v−1)Q(v)/a10. Dividing (1−v)^19 by N leaves quotient with leading term −v^7. Its remaining terms and all Jacobi components except νP7 disappear by v(1−v) orthogonality. The normalized squared norm of P7 is 8/153. Consequently 1/20−bᵀc^19=8ν/(153 a10 a7), strictly negative on the master. The physical bush error independently returned −9.528850942785488×10^-13 both by direct quadrature and this exact formula. Thus ν=0 is necessary for order 20 on this 12-knot pencil.

## Twenty-row prefix obstruction

On the exact varying-pole prefix of the 19/46 tableau, the seven scalar observations through ordinary size nine are E0,E1,μ,μC,E′0,E′1,E″0. The last follows by subtracting the available first derivative from the confluent jet. They exhaust the true scalar dual: the directed test below yields rank ≥13 for the 20-coordinate columns Φ(t)−f_t(c) over ALL 486 trees through size nine. Every honest coefficient must annihilate these, by using the pure bush at each size to determine its scalar action. The listed observations have rank seven because their common P8 kernel is exactly
    Q={R″ : R(u)=G(u)(A+Bu)},   G(u)=u^5(1−u)^4.
Indeed R=J²q automatically vanishes twice at 0, and q,q′,q″ vanishing there raise this to five. The two moments give R′(1)=R(1)=0; q,q′ vanishing at 1 raise this to four. The converse and rank are immediate.

A nonendpoint local-nine mark v already on the prefix, or arriving on row 21, would require R′(v)=I_v q=0 for every R. Taking G and uG rules this out. A nonendpoint local-ten mark by row 22 would, by unary pullback of its incoming, put I_v J on at most the first twenty through size nine, giving R(v)=0 for all R, impossible. Thus four distinct nonendpoint local-ten marks by row 26 require v,b at rows 23,24.

Suppose these rows exist. The 23rd incoming A_v has nonzero coordinate 22 or the same unary contradiction applies. The 23rd derivative unit e_v is a genuine E_v through size ten. Subtract βe_v from the 24th incoming A_b to eliminate coordinate 23, then αA_v to eliminate 22. The resulting signed row on the first 21 is genuinely
    F=I_b−αI_v−βE_v
through size ten. If s is the clock of row 21, FJ and F((u−s)·) have genuine actual rows on the first TWENTY through size nine, by the strict unary pullback and the leaf-minus-clock pullback respectively. Both annihilate Q. Put Δ=b−v, K=G(b)/G(v), L=G′/G. The first gives R(b)=αR(v)+βR′(v), so β=KΔ and α=K(1−Δ L(v)). The second, integrated by parts and simplified with the first, is
    (b−s)R′(b)−[α(v−s)+β]R′(v)−β(v−s)R″(v)=0.
First set R=(u−v)G: this gives (b−s)L(b)=(v−s)L(v). Setting R=G and substituting the preceding equality gives L(v)+(v−s)L′(v)=0. Hence
    φ_s(u)=(u−s)L(u)=(u−s)(5−9u)/[u(1−u)]
satisfies φ_s(b)=φ_s(v), φ_s′(v)=0. This rational function is nonconstant for every s because its two distinct logarithmic poles cannot both be canceled by u−s. Clearing the denominator gives a nonzero polynomial of degree ≤2 with a double root v and a distinct root b, impossible. This argument extends to general G with just two distinct roots of positive multiplicities whenever its two indicated second derivatives are invisible to the whole earlier dual.

The fixed prefix therefore needs at least 25 stages for its five positive local-nine marks, a price met by the 19/46 chart. It cannot yield five distinct positive local-ten marks on 26. A 50-stage p20 splice based on 26 forward, the fixed 30-row reverse bank and six standard literal merges would need a different core or a different overlap/port strategy.

## Additional independent directed rank replay
Append this block after the 19/46 source's original replay. The original master contraction was independently rerun (derivative norm 2.9052e−101, displacement/radius 4.8917e−248). The rank check returned 486 trees and lower bounds [13,13] for the first nineteen and first twenty.
```javascript
{
const Bs=[[],[]],bank=[];let tot=0;
function addB(B,q){q=q.slice();for(let [j,r] of B){let z=q[j];q=q.map((v,k)=>sub(v,xm(z,r[k])));q[j]=X0}
let a=q.map((v,j)=>[v,j]).filter(([v,j])=>sg(v)&&B.every(([i])=>j!=i));if(!a.length)return;
let [p,j]=a.sort(([x],[y])=>Math.abs(mid(y))-Math.abs(mid(x)))[0];q=q.map(x=>xd(x,p));q[j]=X1;B.push([j,q])}
for(let n=1;n<=9;n++){let layer=[];
function rec(rem,k,v,fac){if(!rem){let p=xi(1,fac),e=v.map((x,i)=>sub(x,xm(p,xpow(fc[i],n-1))));
addB(Bs[0],e.slice(0,19));addB(Bs[1],e);let pv=mv(fwA.slice(0,20).map(r=>r.slice(0,20)),v);layer.push({n,fac:fac*BigInt(n),pv});tot++;return}
for(let j=k;j<bank.length&&bank[j].n<=rem;j++){let z=bank[j];rec(rem-z.n,j,v.map((x,i)=>xm(x,z.pv[i])),fac*z.fac)}}
rec(n-1,0,xrr(20,()=>X1),1n);bank.push(...layer)}
if(tot!=486||Bs.some(B=>B.length<13))throw Error('rank');console.log(tot,Bs.map(B=>B.length));
}
```
