# Exact replay: p14 midpoint, grade-five double refund and ordinary square-factor test

Standalone JavaScript (ES2022), executed natively. No generic coefficient tests are used as proofs. The degree-seven chronological theorem gives the identities over an arbitrary field; its forced scaled fourth knot is 1. The fixed-grid modular tests concern only the explicitly rational L₇ Lobatto data. All squarefree ordered root choices are covered, not samples.

```javascript
function replay(){
const ck=(t,s)=>{if(!t)throw Error(s)};
const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){[a,b]=[b,a%b]}return a};
const R=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);if(!b)throw Error("zero denominator");if(b<0){b=-b;a=-a}let d=gcd(a,b);return [a/d,b/d]};
const add=(a,b)=>R(a[0]*b[1]+b[0]*a[1],a[1]*b[1]), mul=(a,b)=>R(a[0]*b[0],a[1]*b[1]),neg=a=>R(-a[0],a[1]),Z=R(0);
const xs=(...c)=>c.map(x=>R(x)),trim=a=>{a=a.slice();while(a.length>1&&a.at(-1)[0]===0n)a.pop();return a.length?a:[Z]};
const A=(a,b)=>trim(Array.from({length:Math.max(a.length,b.length)},(_,i)=>add(a[i]||Z,b[i]||Z)));
const S=(a,r)=>trim(a.map(x=>mul(x,r))),sub=(a,b)=>A(a,S(b,R(-1))),M=(a,b)=>{let g=Array(a.length+b.length-1).fill(Z);a.forEach((u,i)=>b.forEach((v,j)=>g[i+j]=add(g[i+j],mul(u,v))));return trim(g)};
const D=a=>trim(a.slice(1).map((e,j)=>mul(e,R(j+1)))),J=a=>trim([Z,...a.map((e,j)=>mul(e,R(1,j+1)))]),same=(a,b)=>sub(a,b).every(z=>!z[0]);
const x=xs(0,1),x2=M(x,x),xm1=xs(-1,1),U=xs(-1,9,-21,14),V=M(U,xm1),P1=S(xm1,R(1,18)),R0=[R(-1,18)],vprime=D(V);
const P2=S(M(xs(-2,18),P1),R(1,14)),R1=S(sub(M(xs(-2,18),R0),xm1),R(1,14));
ck(same(A(M(M(x,xm1),D(D(U))),M(xs(-2,4),D(U))),S(U,R(18))),"Jacobi skeleton");
for(const [a,P,T] of [[x,P1,R0],[x2,P2,R1]])ck(same(J(M(a,V)),M(x2,A(M(P,vprime),M(T,V)))),"exact primitive");
ck(same(sub(M(R0,P2),M(R1,P1)),S(M(xm1,xm1),R(1,252))),"refunded fifth determinant");
for(let b=0;b<=12;b++){for(let t of [3,4])ck(t+2+Math.max(0,t-2-b)-t-Math.max(0,t-1-b)>=1,"inclusive budget");ck(6+Math.max(0,2-b)-4-Math.max(0,3-b)>=1,"refunded budget")}
const F=M(M(x2,x2),M(M(xm1,xm1),xm1));ck(same(sub(M(xm1,D(F)),S(F,R(2))),M(M(M(x2,x),M(M(xm1,xm1),xm1)),xs(-4,5))),"origin 3+2");
const p=1361,m=a=>(a%p+p)%p,inv=a=>{let t=1;for(let k=p-2;k;k>>=1,a=m(a*a))if(k&1)t=m(t*a);return t},mm=(a,b)=>{let c=Array(a.length+b.length-1).fill(0);a.forEach((r,i)=>b.forEach((t,j)=>c[i+j]=m(c[i+j]+r*t)));return c},pe=(xs,x)=>xs.reduceRight((a,b)=>m(a*x+b),0);
let la=[1],lb=[-1,2];for(let n=2;n<=7;n++){let lc=mm(lb,[-1,2]).map(t=>m(t*(2*n-1)));for(let j=0;j<la.length;j++)lc[j]=m(lc[j]-(n-1)*la[j]);lc=lc.map(t=>m(t*inv(n)));la=lb;lb=lc}
const der=lb.slice(1).map((v,j)=>m((j+1)*v)),knots=Array.from({length:p},(_,i)=>i).filter(u=>!pe(der,u));ck(knots.join(",")==="228,425,610,752,937,1134","fixed splitting");
const mom=(T,k,u)=>pe([...Array(k+1).fill(0),...T.map((v,i)=>m(v*inv(i+k+1)))],u);let n=0,prod=1;const grid=[...knots,1];for(let mask=0;mask<128;mask++){const Z=grid.filter((_,i)=>(mask>>i)&1);if(Z.length!==3)continue;let T=[1];for(const r of Z)T=mm(T,[-r,1]);for(const u of grid.filter(r=>!Z.includes(r))){let [i,j,k]=[1,2,3].map(s=>mom(T,s,u));let d=m(i*k-j*j);ck(d!==0,"two moments after three zeros");prod=m(prod*d);n++}}
ck(n===140&&prod===1050,"quartic trace");
const fac=[0,...knots],facResult=[];for(let d=0;d<=4;d++){let n=0,firstZeros=0,prod=1;for(let mask=0;mask<128;mask++){const Z=fac.filter((_,i)=>(mask>>i)&1);if(Z.length!==d)continue;let T=[1];for(const r of Z)T=mm(T,[-r,1]);for(const u of knots.filter(r=>!Z.includes(r))){let i=mom(T,1,u),j=mom(T,2,u);ck(i||j,"ordinary factor first clean");if(!i)firstZeros++;n++;prod=m(prod*(i||j))}}facResult.push([d,n,firstZeros,prod])}
ck(facResult.map(x=>x.join("/")).join(",")==="0/6/0/1153,1/36/0/1161,2/90/1/342,3/120/0/1027,4/90/0/762","factor summaries");
return {rational:"Jacobi skeleton, two normalized primitives, determinant (x-1)^2/252, refunded split budgets, cubic-origin 3+2",prime:p,roots:knots,gridQuartic:[n,prod],ordinaryFactors:facResult};
}
console.log(replay());
```

Executed output:
```json
{"rational":"Jacobi skeleton, two normalized primitives, determinant (x-1)^2/252, refunded split budgets, cubic-origin 3+2","prime":1361,"roots":[228,425,610,752,937,1134],"gridQuartic":[140,1050],"ordinaryFactors":[[0,6,0,1153],[1,36,0,1161],[2,90,1,342],[3,120,0,1027],[4,90,0,762]]}
```

For the factor option with a first-moment zero mod 1361 one must not infer the corresponding rational first moment vanishes. At every possible root choice the separately evaluated second moment still suffices if needed. Equivalently use the symmetric product over all admissible distinct labellings of the linear polynomials J[xP](u)+tJ[x²P](u) over F_1361[t]: each factor is nonzero, hence so is the product. It is the good-prime reduction of the analogous rational-coefficient symmetric product; a characteristic-zero common zero in any labelling would annihilate that product. Thus using the first nonzero residue in the table as diagnostic does not require that the conditional selection itself lift as a symmetric rational number.
