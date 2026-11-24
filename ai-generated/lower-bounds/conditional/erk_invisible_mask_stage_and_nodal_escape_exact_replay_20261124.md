# Exact physical ordinary controls for the invisible-mask and signed nodal-hull argument

24 November 2026 UTC. Companion to erk_invisible_mask_is_a_physical_stage_and_nodal_escape_20261124.md. Three independent checks:

1. In each of the four (p,K,m_K) numerical branches the marked-origin annihilator budget is 14 or 15 exactly as stated. Explicit integer-coefficient shifted Jacobi polynomials R_n (n=K+1) have R_n(1)=1 and all required x dx moments vanish by exact rational arithmetic. The scalar H(c)=cR_n(c) is only asserted to be in that physical annihilator.
2. A fully rational, ordinary nine-stage order-seven ERK has two true coordinate units in F₃, and BOTH of their first nonzero genuine complete exterior coordinates occur only at grade 4. Nevertheless the known nine-stage minimum at order seven prevents deleting even one. The units are found by exact row-space tests against every ordinary F₃ residual, not a coordinate count or a marked linear-only calculation. This is a concrete control against the erroneous idea that an invisible pure unit is necessarily disposable.
3. A genuinely different twelfth-stage construction has a zero-weight grade-4 ordinary duplicate which splits at grade 5. Its two nonzero outgoing taps have zero direct weighted return; bᵀ C A sees it at genuine grade 2 with value −4/105. A proper physical return to the earlier anchor gives an 11-stage method passing every order-seven condition. Uncompensated deletion of the coordinates/column fails 36 of the 85 conditions (already at size three). All 85 coefficients on the original seed, expanded tableau and correctly reduced tableau are recomputed exactly. The example tests the causal ingredient and is not represented as an order-19/20 witness.

The strict R7 seed is the fully explicit nine-stage rational seed also used in the earlier three-ghost-plane physical controls. All arrays below are ordinary, one-based only in the returned lists of seed units. The adjoint module recursion includes same-parent genuine ordinary siblings; no adjoint normalization by b is used. Run this self-contained ECMAScript source with Node or another BigInt-capable JavaScript engine.

~~~javascript
const report=(()=>{
const Q=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);if(!b)throw Error('zero denominator');if(b<0n){a=-a;b=-b}const gcd=(x,y)=>y?gcd(y,x%y):x<0n?-x:x;const g=gcd(a,b);return[a/g,b/g]};
const add=(a,b)=>Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]), neg=a=>[-a[0],a[1]], sub=(a,b)=>add(a,neg(b)),mul=(a,b)=>Q(a[0]*b[0],a[1]*b[1]),div=(a,b)=>Q(a[0]*b[1],a[1]*b[0]), nz=a=>a[0]!==0n, str=a=>a[1]==1n?''+a[0]:a[0]+'/'+a[1],rat=s=>{let [n,d='1']=s.split('/');return Q(n,d)};
const z=n=>Array.from({length:n},()=>Q(0)), one=n=>z(n).map(()=>Q(1)), eye=n=>z(n).map((_,i)=>z(n).map((_,j)=>Q(i===j?1:0))), dot=(a,b)=>a.reduce((v,x,i)=>add(v,mul(x,b[i])),Q(0)), mv=(A,x)=>A.map(r=>dot(r,x)),prod=(x,y)=>x.map((a,i)=>mul(a,y[i])),scale=(c,x)=>x.map(a=>mul(c,a)), plus=(x,y)=>x.map((a,i)=>add(a,y[i])), eq=(x,y)=>x.every((v,i)=>!nz(sub(v,y[i]))),OK=(c,m)=>{if(!c)throw Error(m)};
function rref(M){const a=M.map(r=>r.slice()),p=[];if(!a.length)return[a,p];let i=0;for(let j=0;j<a[0].length&&i<a.length;j++){let k=i;while(k<a.length&&!nz(a[k][j]))k++;if(k===a.length)continue;[a[k],a[i]]=[a[i],a[k]];a[i]=scale(div(Q(1),a[i][j]),a[i]);for(k=0;k<a.length;k++)if(k!==i)a[k]=plus(a[k],scale(neg(a[k][j]),a[i]));p.push(j);i++}return[a,p]}
function core(A,p){let ts=[];for(let n=1;n<=p;n++){let items=[],lim=ts.length;function branch(start,left,ids){if(left===0){let v=one(A.length),g=BigInt(n);for(const t of ids){v=prod(v,ts[t].Av);g*=ts[t].g}items.push({n,g,v,Av:mv(A,v)});return}for(let j=start;j<lim&&ts[j].n<=left;j++)branch(j,left-ts[j].n,ids.concat(j))}branch(0,n-1,[]);ts=ts.concat(items)}return ts}
const seedRows=['','1/4','-1/2 1','1/12 1/3 1/12','394/3993 400/3993 100/3993 -56/1331','-26/27 -1360/243 -340/243 4024/1701 10648/1701','1500/2401 1104/343 276/343 -19176/16807 -51909/16807 1053/2401','163/1536 1/3 1/12 1/8 -6655/106496 -945/8192 2401/79872','-337/264 -260/33 -65/33 190/77 96921/11648 -1701/1408 3087/4576 144/77'];
const A=seedRows.map((r,i)=>(r?r.split(' ').map(rat):[]).concat(z(9-i))),b='77/1440 0 0 16/105 1771561/6289920 243/2560 16807/74880 16/105 11/270'.split(' ').map(rat), T=core(A,7), I=eye(9), c=mv(A,one(9));
function err(T,b){return T.filter(t=>nz(sub(dot(t.v,b),Q(1,t.g))))}
const [RR,PV]=rref(T.filter(t=>t.n<=4).map(t=>t.v));let delta;
for(let j=0;j<9;j++)if(!PV.includes(j)){let d=I[j].slice();PV.forEach((a,k)=>d[a]=neg(RR[k][j]));if(T.some(t=>t.n===5&&nz(dot(t.v,d)))){delta=d;break}}
OK(delta,'E3/E4 separator');OK(T.length===85&&!err(T,b).length,'seed');
const G=Array.from({length:12},()=>z(12));for(let a=0;a<9;a++)G[a]=A[a].concat(z(3));G[9]=delta.concat(z(3));
const S=[3,8],B=b.concat(z(3)),alpha=[Q(1),neg(div(b[S[0]],b[S[1]]))];
for(let q=0;q<2;q++){const a=S[q],k=10+q;B[k]=B[a]=mul(b[a],Q(1,2));G[k]=A[a].concat(z(3));G[k][0]=sub(G[k][0],alpha[q]);G[k][9]=alpha[q]}
const T2=core(G,7), c2=mv(G,one(12)), col=G.map(r=>r[9]), raw=dot(B,col),return2=dot(prod(B,c2),col);
OK(!err(T2,B).length,'expanded');OK(!nz(raw)&&nz(return2)&&nz(col[10])&&nz(col[11]),'true near return');OK(T2.filter(t=>t.n<=5).every(t=>!nz(sub(t.v[0],t.v[9])))&&T2.some(t=>t.n===6&&nz(sub(t.v[0],t.v[9]))),'grade 4 match, 5 split');
const B3=B.filter((_,j)=>j!==9),shrink=(doRedirect)=>G.filter((_,i)=>i!==9).map(r=>r.map((v,j)=>j===0&&doRedirect?add(v,r[9]):v).filter((_,j)=>j!==9)),T3=core(shrink(true),7),Bad=core(shrink(false),7);
OK(!err(T3,B3).length&&err(Bad,B3).length,'actual collapse v. naive');
const choose=(n,k)=>{let x=1n;for(let i=1;i<=k;i++)x=x*BigInt(n-i+1)/BigInt(i);return x};
let endpoints=[];for(const [p,s,K] of [[19,30,7],[20,32,8]]){let n=K+1,R=Array.from({length:n+1},(_,j)=>(-1n)**BigInt(n-j)*choose(n,j)*choose(n+1+j,n));let hp=R.reduce((a,b)=>a+b,0n);OK(hp===1n,'terminal');for(let m=0;m<=K;m++)OK(!nz(R.reduce((q,a,j)=>add(q,Q(a,j+m+2)),Q(0))),'Jacobi'); for(let m=K-1;m<=K;m++){let D=s-m-K-2;OK(D===15-(m-K+1),'cap');endpoints.push({p,K,m,ann:D,H_at_1:''+hp})}}
const F=[];
for(let d=2;d<=6;d++){const pw=n=>{let v=one(9);while(n--)v=prod(v,c);return v}, f=T.filter(t=>t.n<=d+1).map(t=>plus(t.v,scale(Q(-t.n,t.g),pw(t.n-1)))),r=rref(f)[1].length,units=b.map((v,i)=>rref(f.concat([I[i]]))[1].length===r?i+1:0).filter(Boolean);F.push([d,r,units])}

const baza=M=>{let [r,p]=rref(M);return r.slice(0,p.length)};
function ext(A,b,T,H){let V=[[b]],E=Array.from({length:H+1},(_,k)=>baza(T.filter(t=>t.n<=k+1).map(t=>t.v)));
for(let h=1;h<=H;h++){let M=V[h-1].slice();for(const l of V[h-1]) M.push(A[0].map((_,i)=>dot(l,A.map(r=>r[i]))));for(let j=1;j<=h;j++)for(let l of V[h-j])for(let u of E[j])M.push(prod(l,u));V.push(baza(M))}return V}
const vv=ext(A,b,T,6),v2=ext(G,B,T2,3);
const born=(V,i)=>V.findIndex(ll=>ll.some(l=>nz(l[i])));
const borns=[born(vv,1),born(vv,2)];OK(borns.every(h=>h>3)&&born(v2,9)===2,'full marked horizons');

return {first_actual_seed_ghost_returns:borns,expanded_first_return:born(v2,9),Jacobi_endpoints:endpoints,seed_ordinary:T.length,delta:delta.map(str),two_actual_taps:alpha.map(str),direct:str(raw),genuine_return2:str(return2),split_and_reduced:[T2.length,T3.length],naive_failures:err(Bad,B3).length,first_naive_size:err(Bad,B3)[0].n,rank_F_seed:F}

})();
console.log(JSON.stringify(report));
~~~

Exact result, also evaluated directly in the research session:
~~~json
{"first_actual_seed_ghost_returns":[4,4],"expanded_first_return":2,"Jacobi_endpoints":[{"p":19,"K":7,"m":6,"ann":15,"H_at_1":"1"},{"p":19,"K":7,"m":7,"ann":14,"H_at_1":"1"},{"p":20,"K":8,"m":7,"ann":15,"H_at_1":"1"},{"p":20,"K":8,"m":8,"ann":14,"H_at_1":"1"}],"seed_ordinary":85,"delta":["260/343","0","0","9984/2401","-19965/9604","-5265/1372","1","0","0"],"two_actual_taps":["1","-288/77"],"direct":"0","genuine_return2":"-4/105","split_and_reduced":[85,85],"naive_failures":36,"first_naive_size":3,"rank_F_seed":[[2,1,[]],[3,2,[2,3]],[4,4,[2,3]],[5,6,[2,3]],[6,7,[2,3]]]}
~~~
The seed rank table at grade 3 is rank F₃=2, exactly the two listed unit axes. Their unit grades plus their null horizon obey 3+3=6=p−1. The marked grade-2 test in the 12-stage example is deliberately outside the applicable L=1 agreement horizon; it does not invalidate the paid L=1 stage collapse.
## Companion signed-contrast sparse-kernel replay for the last p19-low t=5 exclusion

The proof in the main note finally closes that corner, without assuming positivity or even a nonzero individual weight in a pair. This exact finite control tests the two new linear implications independently over the rationals. Use the helper definitions Q, nz, OK, eye, dot, prod, mul, div, neg and rref appearing at the top of the preceding script. The finite cases supplement, not replace, the general linear proofs.

~~~javascript
const sparseReport=(()=>{
const Q=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);if(!b)throw Error('zero denominator');if(b<0n){a=-a;b=-b}const gcd=(x,y)=>y?gcd(y,x%y):x<0n?-x:x;const g=gcd(a,b);return[a/g,b/g]};
const add=(a,b)=>Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]), neg=a=>[-a[0],a[1]], sub=(a,b)=>add(a,neg(b)),mul=(a,b)=>Q(a[0]*b[0],a[1]*b[1]),div=(a,b)=>Q(a[0]*b[1],a[1]*b[0]), nz=a=>a[0]!==0n, str=a=>a[1]==1n?''+a[0]:a[0]+'/'+a[1],rat=s=>{let [n,d='1']=s.split('/');return Q(n,d)};
const z=n=>Array.from({length:n},()=>Q(0)), one=n=>z(n).map(()=>Q(1)), eye=n=>z(n).map((_,i)=>z(n).map((_,j)=>Q(i===j?1:0))), dot=(a,b)=>a.reduce((v,x,i)=>add(v,mul(x,b[i])),Q(0)), mv=(A,x)=>A.map(r=>dot(r,x)),prod=(x,y)=>x.map((a,i)=>mul(a,y[i])),scale=(c,x)=>x.map(a=>mul(c,a)), plus=(x,y)=>x.map((a,i)=>add(a,y[i])), eq=(x,y)=>x.every((v,i)=>!nz(sub(v,y[i]))),OK=(c,m)=>{if(!c)throw Error(m)};
function rref(M){const a=M.map(r=>r.slice()),p=[];if(!a.length)return[a,p];let i=0;for(let j=0;j<a[0].length&&i<a.length;j++){let k=i;while(k<a.length&&!nz(a[k][j]))k++;if(k===a.length)continue;[a[k],a[i]]=[a[i],a[k]];a[i]=scale(div(Q(1),a[i][j]),a[i]);for(k=0;k<a.length;k++)if(k!==i)a[k]=plus(a[k],scale(neg(a[k][j]),a[i]));p.push(j);i++}return[a,p]}
const ent=(n,r)=>{let a=[];for(let i=0;i<r**n;i++){let m=i;const v=[];for(let j=0;j<n;j++){v.push(m%r);m=Math.floor(m/r)}a.push(v)}return a};
let hyp=0,nodal=0,coap=0;const N=4,Q4=eye(N);
for(const raw of ent(4,3)){let v=raw.map(a=>Q(a-1)),j=v.findIndex(nz);if(j<0)continue;hyp++;
const K=[];for(let i=0;i<4;i++)if(i!==j){let x=Q4[i].slice();x[j]=neg(div(v[i],v[j]));OK(!nz(dot(v,x))&&x.filter(nz).length<=2,'sparse γ');K.push(x)}
OK(rref(K)[1].length===3,'hyperplane');
for(const y of ent(4,3)){let c=y.map(a=>Q(a)),invariant=K.every(x=>!nz(dot(v,prod(x,c)))),supp=y.filter((_,i)=>nz(v[i]));OK(invariant===supp.every(a=>a===supp[0]),'eigenline support');nodal++}
}
for(let u=0;u<=3;u++)for(let n=10-u;n<=40;n++){OK(n-2>6-u,'pair-local');coap++}
let checks=0;for(const c of ent(4,3))for(const g of ent(4,2))for(let a=0;a<3;a++){let J=c.map((x,i)=>x===a&&g[i]===0?i:-1).filter(i=>i>=0);if(!J.length)continue;let h=[Q(0),Q(2),Q(-3),Q(4)],M=[];for(const v of [g.map(a=>Q(a)),h])for(let r=0;r<3;r++)M.push(J.map(i=>mul(v[i],Q(BigInt(c[i])**BigInt(r)))));OK(rref(M)[1].length<=1,'same-clock zero-g mask rank');checks++}
return {nonzero_contrast_equations:hyp,clock_assignments_tested:nodal,paid_short_support_tests:coap,same_clock_zero_g_tests:checks};
})(); console.log(JSON.stringify(sparseReport));
~~~

Exact output:
~~~json
{"nonzero_contrast_equations":80,"clock_assignments_tested":6480,"paid_short_support_tests":130,"same_clock_zero_g_tests":2013}
~~~

## Last uniform F₄ physical census: exact horizon bookkeeping

The first two conditions in this replay check the true quadratic trace has three available roots after four exceptional mask knots, and that all two-clock contrasts fit the invariant core by strict head-degree comparison. The native t+3 condition is checked rather than extended from p20 to p19 by analogy. The two distinct later regimes (no surplus, or t≥6) are supplied separately by the first-return rank, not these numerical loops.

~~~javascript
console.log((()=>{const p=u=>Math.floor(u/2);const ans=[];for(const [order,K,nfu] of [[19,7,10],[20,8,11]])for(const [label,T,ua] of [['nonzero D1 or m2=2',3,2],['t=3',3,2],['t=4',4,3],['t=5',5,3]]){const de=[];for(let u=0;u<=ua;u++){let n=nfu-u;if(n<7||n-2<=K-u-1||T+2>K)throw Error('unpaid');let r;if(T+3<=K)r=u;else{if(order!==19||T!==5)throw Error('lag');r=(u<3)?u+1:3;}de.push(4+r)}ans.push([order,label,Math.max(...de)])}return ans;})());
~~~
Exact output: [[19,"nonzero D1 or m2=2",6],[19,"t=3",6],[19,"t=4",7],[19,"t=5",7],[20,"nonzero D1 or m2=2",6],[20,"t=3",6],[20,"t=4",7],[20,"t=5",7]]. No numerical tableau feasibility result is inferred.
