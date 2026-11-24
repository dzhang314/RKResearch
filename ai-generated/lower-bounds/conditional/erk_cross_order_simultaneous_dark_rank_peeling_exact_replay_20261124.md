# Standalone exact nonlinear control for simultaneous cross-order rank peeling

The deterministic R7 seed, exact rational arithmetic and genuine all-tree calculation are fully included. The four new ghost rows use multiples 1,2,4,1 of a genuine separator of E₃ from E₄ on the old donor block. The compensated receiver adds taps 1,1,1,−7 to them and +4 to the retained origin for clock balance. Its first three individual marked columns are nonzero and equal; the extra compensator remains in the construction. The original order is checked from all true rooted trees, independently of the abstract surgery formula. Every return and assertion in the output is exact. Run with a BigInt-capable ECMAScript engine.

~~~javascript
const a=(()=>{
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

const ref=3, M=Array.from({length:14},()=>z(14)),bw=b.concat(z(5));for(let i=0;i<9;i++)M[i]=A[i].concat(z(5));const cfs=[1,2,4,1];
for(let j=0;j<4;j++)M[9+j]=scale(Q(cfs[j]),delta).concat(z(5));
M[13]=A[ref].concat(z(5));M[13][0]=add(M[13][0],Q(4));for(let j=9;j<=11;j++)M[13][j]=Q(1);M[13][12]=Q(-7);bw[13]=bw[ref]=mul(Q(1,2),b[ref]);
const ts=core(M,7),R=14, incoming=M.map(r=>r.slice()),right=[9,10,11].map(j=>dot(bw,M.map(r=>r[j])));
OK(ts.length===85&&!err(ts,bw).length,'joint original');OK(right.every(nz)&&right.every(q=>!nz(sub(q,right[0]))),'all three first returns one');
const copyRemoval=(Qm,weights,del)=>[Qm.filter((_,i)=>!del.includes(i)).map(r=>r.map((v,j)=>j===0?del.reduce((x,d)=>add(x,r[d]),v):v).filter((_,j)=>!del.includes(j))),weights.filter((_,i)=>!del.includes(i))];
for(const j of [9,10]){let row=M[j].slice();incoming[j]=z(R);incoming[11]=plus(incoming[11],row)}
const [out,bo]=copyRemoval(incoming,bw,[9,10]),TT=core(out,7);
const [bad1,b1]=copyRemoval(M,bw,[9]), err1=err(core(bad1,7),b1);
const [six,b6]=copyRemoval(M,bw,[9,10,11]), sixerr=err(core(six,6),b6),sevenerr=err(core(six,7),b6);
OK(!err(TT,bo).length&&!sixerr.length&&err1.length>0&&sevenerr.length&&sevenerr[0].n===7,'simultaneous rank-one refund');
return {order7_tests:ts.length,marked_1_restriction:right.map(str),p7_certified_stages:[M.length,out.length],p6_also:[M.length,six.length],one_naive_failed_order7_conditions:err1.length,three_lower_target_failed_order7_conditions:sevenerr.length,first_naive_size:err1[0].n};
})(); console.log(JSON.stringify(a));
~~~

Exact evaluated output:
~~~json
{"order7_tests":85,"marked_1_restriction":["8/105","8/105","8/105"],"p7_certified_stages":[14,12],"p6_also":[14,11],"one_naive_failed_order7_conditions":9,"three_lower_target_failed_order7_conditions":9,"first_naive_size":7}
~~~
The 14→12 and 14→11 counts are physical stages left by these two specified surgeries, not claims of optimality for the seed or for general order-six/seven methods. The latter 11-stage specific table passes through order six but fails at order seven.
