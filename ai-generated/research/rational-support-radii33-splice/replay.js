const results = (() => {

const gcd=(a,b)=>{if(a<0n)a=-a;if(b<0n)b=-b;while(b)[a,b]=[b,a%b];return a};
const Q=(a,b=1n)=>{a=BigInt(a);b=BigInt(b);if(b<0n){a=-a;b=-b;}const d=gcd(a,b);return [a/d,b/d]};
const [O,U]=[[0n,1n],[1n,1n]], add=([a,b],[c,d])=>Q(a*d+b*c,b*d), sub=([a,b],[c,d])=>Q(a*d-b*c,b*d), mul=([a,b],[c,d])=>Q(a*c,b*d), div=([a,b],[c,d])=>Q(a*d,b*c), str=t=>t.join("/"), eq=(a,b)=>a[0]===b[0]&&a[1]===b[1], sum=a=>a.reduce(add,O), pow=([a,b],k)=>Q(a**BigInt(k),b**BigInt(k));
const poly=xs=>xs.reduce((p,z)=>[...p,O].map((w,j)=>sub(p[j-1]??O,mul(z,w))),[U]);
const basis=xs=>xs.map((x,j)=>{const ys=xs.filter((_,i)=>i!==j),r=ys.reduce((s,y)=>mul(s,sub(x,y)),U);return poly(ys).map(a=>div(a,r));});
const ev=(p,x)=>sum(p.map((a,j)=>mul(a,pow(x,j))));
const integ=(p,x)=>sum(p.map((a,j)=>div(mul(a,pow(x,j+1)),Q(j+1))));
const fl=(arr,func)=>arr.flatMap((x,i)=>func(x,i));
const radii=[0,6,11,16,21,25,29,31,32,33].map(n=>Q(n,33));
const masses=basis(radii.map(r=>pow(r,2))).map(p=>sum(p.map((a,j)=>div(a,Q(2*j+1)))));
const X=fl(radii,(r,i)=>i===0?[Q(1,2)]:[div(sub(U,r),Q(2)),div(add(U,r),Q(2))]);
const W=fl(masses,(w,i)=>i===0?[w]:[div(w,Q(2)),div(w,Q(2))]);
const I=(msg,cond)=>{if(!cond)throw msg;};
const dot=(a,b)=>sum(a.map((x,j)=>mul(x,b[j])));
function core(g,goal){
 let c=[g],A=[[g]], ids=[0], nodes=[g,...X.filter(x=>!eq(x,g))], receipts=0;
 for(let k=2;k<=goal;k++){
   const p=basis(ids.map(i=>c[i])), newids=(g[0]===0n||k===2)?[0]:[];
   for(const x of nodes.slice((g[0]===0n||k===2)?1:0,k)){
    const r=Array(c.length+1).fill(O);
    ids.forEach((idx,i)=>{r[idx]=sub(integ(p[i],x),mul(g,ev(p[i],x)));});
    r[c.length]=g;
    c.push(x);A.push(r);newids.push(c.length-1);
    for(let j=0;j<k-1;j++){I("core polynomial moment",eq(dot(r,c.slice(0,r.length).map(y=>pow(y,j))),div(pow(x,j+1),Q(j+1))));receipts++;}
   }
   ids=newids;
 }
 return {c,A,ids,p:basis(ids.map(i=>c[i])),receipts};
}
function construct(g){
 const G=core(g,10),R=core(g,9),B=R.c.length,w=Array(B).fill(O), cs=[...R.c],L=R.A.map(row=>Array.from({length:B},(_,j)=>row[j]??O));
 const noRep=g[0]===0n;
 const choose=X.map((y,i)=>R.c.flatMap((c,j)=>eq(y,c)?[j]:[]));
 for(let h=0;h<X.length;h++){
  const y=X[h],ids=choose[h], share=div(W[h],Q(ids.length+(noRep&&y[0]===0n?0:1)));
  for(const i of ids)w[i]=share;
  if(noRep&&y[0]===0n){I("zero cluster",ids.length===1&&ids[0]===0);continue;}
  const r=Array(B).fill(O);
  R.ids.forEach((idx,i)=>{r[idx]=mul(W[h],sub(integ(R.p[i],y),mul(g,ev(R.p[i],y))));});
  for(const i of ids)for(let j=0;j<B;j++)r[j]=sub(r[j],mul(w[i],sub(L[i][j],i===j?g:O)));
  while(r.length<cs.length)r.push(O);
  const row=r.map(a=>div(a,share));row.push(g);L.push(row);cs.push(y);w.push(share);
 }
 const N=cs.length,Lg=L.map(row=>Array.from({length:N},(_,j)=>row[j]??O));
 I("reverse rows",Lg.every((r,i)=>eq(sum(r),cs[i])&&eq(r[i],g)&&r.slice(i+1).every(a=>a[0]===0n)));
 let reverseIdentities=0;
 for(let h=0;h<X.length;h++)for(let j=0;j<B;j++){
  const y=X[h], idx=R.ids.indexOf(j);
  const lhs=sum(cs.map((z,i)=>eq(z,y)?mul(w[i],sub(Lg[i][j],i===j?g:O)):O));
  const rhs=idx<0?O:mul(W[h],sub(integ(R.p[idx],y),mul(g,ev(R.p[idx],y))));
  I("reverse identity",eq(lhs,rhs));reverseIdentities++;
 }
 const cr=cs.toReversed().map(x=>sub(U,x)),wr=w.toReversed();
 const T=cr.map((_,i)=>cr.map((_,j)=>div(mul(Lg[N-1-j][N-1-i],wr[j]),wr[i])));
 const S=G.c.length;
 const A=G.A.map(row=>Array.from({length:S+N},(_,j)=>row[j]??O));
 for(let i=0;i<N;i++){
  const y=cr[i],row=Array(S).fill(O);
  G.ids.forEach((idx,j)=>{row[idx]=sub(integ(G.p[j],y),dot(T[i],cr.map(x=>ev(G.p[j],x))));});
  A.push([...row,...T[i]]);
 }
 const c=[...G.c,...cr];
 const b=[...G.c.map(()=>O),...wr];
 I("full shape",A.every((row,i)=>row.slice(i+1).every(a=>a[0]===0n)&&eq(row[i],g)&&eq(sum(row),c[i])));
 I("full weights",X.every((x,i)=>eq(sum(b.filter((_,j)=>eq(c[j],x))),W[i]))&&b.filter(x=>x[0]!==0n).every(x=>x[0]>0n));
 for(let j=0;j<20;j++)I("bush",eq(dot(b,c.map(x=>pow(x,j))),Q(1,j+1)));
 const next=str(sub(dot(b,c.map(x=>pow(x,20))),Q(1,21)));
 I("next failure",next!=="0/1");

 const sparse=A.map(row=>row.flatMap((a,i)=>a[0]===0n?[]:[[i,a]]));
 const rows=Array.from({length:8},()=>[]); rows[1]=["[]"];
 for(let n=2;n<=7;n++){
  const pool=rows.slice(1,n).flatMap((ts,i)=>ts.map(t=>[t,i+1]));
  function forests(left,start){
   if(left===0)return [[]];
   return pool.slice(start).flatMap(([t,h],i)=>h>left?[]:forests(left-h,start+i).map(rest=>[JSON.parse(t),...rest]));
  }
  rows[n]=forests(n-1,0).map(t=>JSON.stringify(t));
 }
 const memo=new Map();
 for(let n=1;n<=7;n++)for(const t of rows[n]){
  const cc=JSON.parse(t).map(x=>memo.get(JSON.stringify(x)));
  const factorial=BigInt(n)*cc.reduce((f,x)=>f*x.factorial,1n);
  const col=c.map((_,i)=>cc.reduce((z,x)=>mul(z,x.primitive[i]),U));
  I("direct rooted tree",eq(dot(b,col),Q(1n,factorial)));
  memo.set(t,{factorial,primitive:sparse.map(row=>sum(row.map(([i,a])=>mul(a,col[i]))))});
 }

 return {trees: memo.size,gamma:str(g),stages:A.length,forwardStages:S,reverseStages:B,clusters:N,representatives:N-B,nonzeroWeights:b.filter(w=>w[0]!==0n).length,distinctContributingSites:new Set(c.filter((_,i)=>b[i][0]!==0n).map(str)).size,forwardLocalChecks:G.receipts,reverseLocalChecks:R.receipts,reverseIdentities,next};
}
return [construct(Q(1,66)),construct(O)];

})();
console.log(JSON.stringify(results, null, 2));
