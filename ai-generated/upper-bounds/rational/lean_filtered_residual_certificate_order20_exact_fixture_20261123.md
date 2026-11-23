# A small exact fixed-tableau certificate for Lean, with an order-20 replay

## Parent Decisions

Dreamer checkpoint: archived certificate background (not included in this snapshot). The full filtered-residual witness format is mathematically sound. Read the checkpoint's two division-free identities and finite obligations. The coordinatewise powers and differences are genuine raw vectors. For completeness at high grades one should say the numerical span of zero-formal-profile rooted combinations; a scalar-profile map from an arbitrary numerical tree span need not already be single-valued at those high grades, even when the RKOC hold. Extend bases of the nested numerical pure spaces to get at most s stored vectors. Basis independence is not needed by soundness. A generator of newly assigned grade can appear on the right-hand side of its own generating membership equation; this is safe because checking an explicit vector equality and its output annihilation is not an inductive claim of span generation.

Root independently implemented exact rational generation and verification on a 55-stage variable-diagonal DIRK order-20 midpoint-extrapolation formula. This is an algebraic proof-checking benchmark, NOT a strict SDIRK construction and NOT a new real upper endpoint. Only 54 residual vectors, 654 explicit vector equality witnesses, 20 quadrature identities, and 54 b-annihilator checks are needed. The second pass verifies these same witnesses without a rank decision. It checks all degrees permitted by the certificate, including the constant moment. This is far smaller than 2,423,307,047 planar trees, but is not a predicted Lean compile time for a large coefficient field. We ran the arithmetic replay, not a Lean build; formal Lean code remains to be written only if user wants that work.

For an initial Lean integration, put the scalar and vector identities in a generic commutative ring with finite indexed stage vectors; certify scaled rational fixtures over integers when useful. A common scalar scale D makes the target monomial moment D^(j+1) and the order RHS D^|t|, as in the Gauss bridge. For exact linear coefficient witnesses in an integral domain, cross-multiply by each nonzero denominator. A plain finite checker can reconstruct all expected obligations from the assigned grades. The following replay keeps the explicit witness matrix as ordinary records; it never enumerates trees and requires no filesystem, packages, or unverified runtime theorem.

```javascript
// Node or any ES2020 implementation: print the statistics of the exact certificate.
console.log(new Function(`

const Z=[0n,1n],O=[1n,1n],abs=x=>x<0n?-x:x,gcd=(a,b)=>{a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a};
function Q(a,b=1n){a=BigInt(a);b=BigInt(b);if(!a)return Z;const g=gcd(a,b)*(b<0n?-1n:1n);return [a/g,b/g];}
const add=([a,b],[c,d])=>{if(!a)return [c,d];if(!c)return [a,b];const g=gcd(b,d);return Q(a*(d/g)+c*(b/g),b*(d/g));},neg=([a,b])=>[-a,b],sub=(a,b)=>add(a,neg(b)),mul=([a,b],[c,d])=>{if(!a||!c)return Z;const x=gcd(a,d),y=gcd(c,b);return [(a/x)*(c/y),(b/y)*(d/x)];},inv=([a,b])=>Q(b,a),div=(a,b)=>mul(a,inv(b)),sum=v=>v.reduce(add,Z);
const times=(v,f)=>v.map(x=>mul(x,f)),had=(v,w)=>v.map((x,i)=>mul(x,w[i])),ip=(v,w)=>sum(had(v,w)),N=10,origin=Array.from({length:N},(_,i)=>Q(1,(i+1)**2));
const w=origin.map((x,k)=>origin.reduce((a,y,j)=>j===k?a:mul(a,div(y,sub(y,x))),O));
const b=[],nodes=[],starts=[0];
for(let k=1;k<=N;k++){for(let i=0;i<k;i++){b.push(div(w[k-1],Q(k)));nodes.push(Q(2*i+1,2*k));}starts.push(b.length);}
const size=b.length;
function A(v){const out=[];for(let k=1;k<=N;k++){const h=Q(1,k);let pref=Z;for(const x of v.slice(starts[k-1],starts[k])){out.push(mul(add(pref,mul(x,Q(1,2))),h));pref=add(pref,x);}}return out;}
const c=A(Array(size).fill(O)); if(c.some((x,i)=>sub(x,nodes[i])[0]))throw Error('clock');
if(sub(sum(b),O)[0])throw Error('constant moment');
let instructions=[],basis=[],series=[Array(size).fill(O)],count=0,adds=0,rank=[];
function take(v,d,op){count++;if(ip(b,v)[0])throw Error('nonzero residual at '+d);v=v.slice();const w=[];for(let j=0;j<basis.length;j++){const x=basis[j],k=v[x.p];if(k[0]){w.push([j,k]);v=v.map((a,i)=>sub(a,mul(k,x.v[i])));}}const k=v.findIndex(a=>a[0]);if(k>=0){const z=v[k];w.push([basis.length,z]);basis.push({d,p:k,v:times(v,inv(z))});adds++;}instructions.push({d,op,w});}
for(let d=1;d<=19;d++){series.push(had(series[d-1],c));if(sub(mul(Q(d+1),ip(b,series[d])),O)[0])throw Error('moments');if(d===1)continue;take(times(A(series[d-1]),Q(d)).map((v,i)=>sub(v,series[d][i])),d,["r",d]);const old=basis.filter(x=>x.d===d-1);for(const x of old){take(A(x.v),d,["A",basis.indexOf(x)]);take(had(c,x.v),d,["C",basis.indexOf(x)]);}const prev=basis.filter(x=>x.d<d);for(let i=0;i<prev.length;i++)for(let j=i;j<prev.length;j++)if(prev[i].d+prev[j].d===d)take(had(prev[i].v,prev[j].v),d,["P",basis.indexOf(prev[i]),basis.indexOf(prev[j])]);rank.push(basis.length);}

// Standalone checking pass: use membership identities only, never ranks or elimination.
function checksum(){
const one=Array(size).fill(O), p=20;
if(basis.length>size)throw Error("certificate bound");
if(c.some((x,i)=>sub(x,A(one)[i])[0]))throw Error("stage nodes");
let count=0,lookup=new Map(instructions.map(z=>[z.op.join(":"),z]));
function check(op,d,lhs){
 const rel=lookup.get(op.join(":"));if(!rel||rel.d!==d)throw Error("missing relation");let rhs=Array(size).fill(Z);
 for(const [j,w] of rel.w){if(basis[j].d>d)throw Error("unavailable grade");rhs=rhs.map((x,i)=>add(x,mul(w,basis[j].v[i])));}
 if(lhs.some((x,i)=>sub(x,rhs[i])[0]))throw Error("wrong vector equality");count++;
}
let x=one;for(let d=0;d<p;d++){if(sub(mul(Q(d+1),ip(b,x)),O)[0])throw Error("wrong quadrature");const nx=had(c,x);if(d+1>=2&&d+1<p)check(["r",d+1],d+1,times(A(x),Q(d+1)).map((a,i)=>sub(a,nx[i])));x=nx;}
for(let i=0;i<basis.length;i++){
 const a=basis[i];if(ip(b,a.v)[0])throw Error("wrong annihilator");
 if(a.d+1<p){check(["A",i],a.d+1,A(a.v));check(["C",i],a.d+1,had(c,a.v));}
 for(let j=i;j<basis.length;j++){const d=a.d+basis[j].d;if(d<p)check(["P",i,j],d,had(a.v,basis[j].v));}
}
return count;
}
return {size,p:20,count:checksum(),rank,adds,quadratureEqualities:20,outputPairings:basis.length};

`)());
```

Independent native replay matched exactly: 54 generators, 18 residual introductions + 53 A actions + 53 node-multiplication actions + 530 products = 654 vector identities. A common denominator for the unscaled matrix is 5,040 and for the unscaled output weights is 60,822,550,204,416,000. This is a second exact arithmetic implementation, not a Lean compilation. User summary accepted in internal review record.
