# Standalone exact full classical replay for the rational seventh-order seeds and repeated Cauchy pole

All coefficients and identities use reduced rational BigInts or a single explicit real quadratic extension. The printed approximations are diagnostics only. Execute with Node.js (ES2020 or above); the code uses no packages. The script checks two prescribed rational grids and two distinct rational central parameters on each, including degree-six scalar words, all 85 classical trees on each seed, and both new nonlinear pilot contrasts and their signed co-site aggregate on all 85 trees. Each rational chart denominator for the displayed fifth proper knot is checked exactly.

```javascript
"use strict";
// ES2020, no imports; rational pair or element a+b*sqrt(Disc), all comparisons exact.
const abs=x=>x<0n?-x:x; function gcd(a,b){a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b]}return a||1n}
function q(n=0,d=1){n=BigInt(n);d=BigInt(d);if(!d)throw Error("zero rational denominator");if(d<0n){n=-n;d=-d}let g=gcd(n,d);return[n/g,d/g]}
const add=(a,b)=>q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]), neg=a=>[-a[0],a[1]], sub=(a,b)=>add(a,neg(b)), mul=(a,b)=>q(a[0]*b[0],a[1]*b[1]), div=(a,b)=>q(a[0]*b[1],a[1]*b[0]), nz=a=>a[0]!==0n, Q0=q(),Q1=q(1);
const sum=l=>l.reduce(add,Q0),prod=l=>l.reduce(mul,Q1),pow=(a,n)=>prod(Array(n).fill(a)), dot=(a,b)=>sum(a.map((t,i)=>mul(t,b[i]))),str=a=>a[0]+(a[1]===1n?"":"/"+a[1]),assert=(z,s)=>{if(!z)throw Error(s)};
function poly(a,b){let c=Array(a.length+b.length-1).fill(Q0);a.forEach((u,i)=>b.forEach((v,j)=>c[i+j]=add(c[i+j],mul(u,v))));return c}
const ev=(p,s)=>p.reduceRight((u,t)=>add(mul(u,s),t),Q0), ip=p=>[Q0,...p.map((u,i)=>div(u,q(i+1)))],trans=a=>a[0].map((_,j)=>a.map(v=>v[j]));
function solve(R,v){let a=R.map((r,i)=>[...r,v[i]]),n=v.length;for(let j=0;j<n;j++){let k=a.findIndex((row,i)=>i>=j&&nz(row[j]));assert(k>=0,"rational pivot");[a[j],a[k]]=[a[k],a[j]];let a0=a[j][j];a[j]=a[j].map(x=>div(x,a0));for(let i=0;i<n;i++)if(i!==j){let t=a[i][j];a[i]=a[i].map((x,l)=>sub(x,mul(t,a[j][l])))}}return a.map(r=>r[n])}
const K=[16,-120,240,-140].map(n=>q(n));
function seed(raw,free){let c=raw.map(z=>q(z,14)),y=c.map(x=>sub(Q1,x));let den=c.map((t,i)=>prod(c.filter((_,j)=>j!==i).map(x=>sub(t,x))));let w=c.map((t,i)=>div(ev(ip(c.filter((_,j)=>j!==i).reduce((p,a)=>poly(p,[neg(a),Q1]),[Q1])),Q1),den[i]));assert(!nz(sub(w[0],q(1,16)))&&w.every(nz),"mass");
 let T=c.slice(1,5).concat([Q1]).reduce((p,a)=>poly(p,[neg(a),Q1]),[Q1]);let coef=sub(ev(ip(T),Q1),div(T[0],q(16)));assert(nz(coef)&&!nz(add(ev(ip([Q0,...T]),Q1),neg(mul(c[5],coef)))),"four-dimensional chart");
 let u=c.map((_,i)=>div(Q1,mul(w[i],den[i]))),H=c.map((t,i)=>i?ev(K,t):Q0),sf=div(pow(c[1],3),mul(q(6),H[1])),h=H.map(t=>mul(sf,t));
 let v1=div(h[1],mul(c[1],u[1])),v2=div(h[2],mul(c[2],u[2])),slope=div(sub(v2,v1),sub(c[2],c[1])),r=sub(c[1],div(v1,slope));for(let i=0;i<7;i++)assert(!nz(sub(h[i],prod([slope,u[i],c[i],sub(c[i],r)]))),"Cauchy numerator");
 let k0=c.map((t,i)=>prod([u[i],c[i],y[i]])),ks=div(pow(y[5],3),mul(q(6),k0[5])),k=k0.map(t=>mul(ks,t));let B=c.map(()=>Array(7).fill(Q0));
 const target=(x,err,i,j)=>mul(w[i],add(div(pow(x[i],j+1),q(j+1)),j===2?err[i]:Q0));
 for(let i=0;i<4;i++){let nn=Math.min(i+1,3),xa=c.slice(0,nn),rows=xa.map((_,j)=>xa.map(t=>pow(t,j)));let sol=solve(rows,xa.map((_,j)=>target(c,h,i,j)));sol.forEach((t,j)=>B[i][j]=t)}
 for(let j=0;j<7;j++){let ix=c.map((_,i)=>i).filter(i=>i>=Math.max(4,j)),rows=ix.map((_,l)=>ix.map(i=>pow(y[i],l)));let sol=solve(rows,ix.map((_,l)=>sub(target(y,k,j,l),sum(c.slice(0,4).map((_,i)=>mul(B[i][j],pow(y[i],l)))))));ix.forEach((i,m)=>B[i][j]=sol[m])}
 const weights=(x,lo)=>x.slice(lo,lo+4).map((t,i)=>div(Q1,prod(x.slice(lo,lo+4).filter((_,j)=>j!==i).map(v=>sub(t,v)))));let U=weights(y,3),V=weights(c,0);for(let i=0;i<4;i++)for(let j=0;j<4;j++)B[i+3][j]=add(B[i+3][j],prod([free,U[i],V[j]]));
 for(let j=0;j<=2;j++)for(let i=0;i<7;i++){assert(!nz(sub(dot(B[i],c.map(x=>pow(x,j))),target(c,h,i,j))),"primal");assert(!nz(sub(dot(B.map(row=>row[i]),y.map(x=>pow(x,j))),target(y,k,i,j))),"dual")}
 let A=B.map((row,i)=>row.map(x=>div(x,w[i])));assert(!nz(sum(w.map((t,i)=>mul(t,pow(h[i],2)))))&&!nz(sum(w.map((t,i)=>prod([t,h[i],k[i]])))),"square/pair");return{A,B,c,w,h,k,r}}
function fld(D){const e=x=>[x,Q0],z=e(Q0),o=e(Q1),p=(a,b)=>[add(a[0],b[0]),add(a[1],b[1])],m=(a,b)=>[add(mul(a[0],b[0]),prod([D,a[1],b[1]])),add(mul(a[0],b[1]),mul(a[1],b[0]))],d=(a,b)=>[sub(a[0],b[0]),sub(a[1],b[1])],fd=(a,b)=>{let den=sub(pow(b[0],2),mul(D,pow(b[1],2)));assert(nz(den),"nonzero norm");return m(a,[b[0],neg(b[1])]).map(t=>div(t,den))},sc=(a,b)=>a.reduce((v,t,i)=>p(v,m(t,b[i])),z),zero=a=>!nz(a[0])&&!nz(a[1]),num=a=>Number(a[0][0])/Number(a[0][1])+Math.sqrt(Number(D[0])/Number(D[1]))*Number(a[1][0])/Number(a[1][1]);return{e,z,o,p,m,d,fd,sc,zero,num}}
function treecheck(A,c,f,verify){let {e,z,o,p,m,d,fd,sc,zero}=f,trees=[{n:1,g:Q1,u:c.map(()=>o)}],counts=[1];verify(trees[0]);
 for(let n=2;n<=7;n++){let old=trees.length;let rec=(left,max,ids)=>{if(left){for(let i=0;i<=max;i++)if(trees[i].n<=left)rec(left-trees[i].n,i,[...ids,i]);return}let g=prod(ids.map(i=>div(trees[i].g,q(trees[i].n)))),vals=ids.map(i=>A.map(row=>sc(row,trees[i].u)));let tt={n,g,u:c.map((_,j)=>vals.reduce((v,vv)=>m(v,vv[j]),o))};verify(tt);trees.push(tt)};rec(n-1,old-1,[]);counts.push(trees.length-old)}
 assert(counts.join()==="1,1,2,4,9,20,48","tree counts");return trees.length}
function checkseed(b){let f=fld(q(2));let {e,sc,d,zero}=f,aa=b.A.map(row=>row.map(e)),ww=b.w.map(e);let n=treecheck(aa,b.c,f,t=>assert(zero(d(sc(ww,t.u),e(div(t.g,q(t.n))))),"ordinary seed"));let W=[{v:b.c.map(()=>Q1),a:Q1}],nw=0;
 for(let j=0;j<=6;j++){for(let t of W){assert(!nz(sub(dot(b.w,t.v),div(t.a,q(j+1)))),"word seed");nw++}if(j<6)W=W.flatMap(({v,a})=>[{v:v.map((t,i)=>mul(t,b.c[i])),a},{v:b.A.map(row=>dot(row,v)),a:div(a,q(j+1))}])}assert(nw===127,"127");return n}
function main(){let seeds=[[0,1,2,5,8,12,14],[0,3,4,8,10,13,14]];for(let c of seeds)for(let free of [q(0),q(13,20000)])checkseed(seed(c,free));let b=seed(seeds[1],Q0),s=b.r;assert(!nz(sub(s,q(-46,63))),"shared pole");
 let br=b.w.map((t,i)=>div(t,sub(b.c[i],s)));assert(!nz(dot(br,b.h))&&!nz(dot(br,b.h.map(t=>pow(t,2)))),"actual double-error guard");let Q=[poly([Q0,q(-1),Q1],[Q1,q(-5),q(5)]),poly([Q0,q(-1),Q1],[q(-1),q(9),q(-21),q(14)])];for(let ff of Q)assert(!nz(ev(ff,Q0))&&!nz(ev(ff,Q1))&&!nz(ev(ip(ff),Q1))&&!nz(ev(ip([Q0,...ff]),Q1)),"Q basis");
 let E=Q.map(t=>ev(t,s)),I=Q.map(t=>ev(ip(t),s)),C=Q.map(ff=>dot(br,b.c.map(x=>ev(ff,x)))),L=Q.map(ff=>dot(br,b.c.map(x=>ev(ip(ff),x))));let det=(a,b)=>sub(mul(a[0],b[1]),mul(a[1],b[0])),coef=[det(I,E),neg(add(det(I,C),det(L,E))),det(L,C)];let D=sub(pow(coef[1],2),prod([q(4),coef[0],coef[2]]));assert(!nz(sub(D,q(529157130457n,506440367892900n)))&&D[0]>0n,"exact discriminant");
 let f=fld(D),{e,z,o,p,m,d,fd,sc,zero,num}=f,vs=[-1,1].map(sign=>fd([neg(coef[1]),q(sign)],e(mul(q(2),coef[2])))),gs=[],old=[...b.A.map(row=>[...row,Q0]),[...b.w,Q0]],c=[...b.c,Q1],A=old.map(row=>row.map(e)),etaList=[];
 let ex=Array(8).fill(z),ey=Array(8).fill(z);ex[0]=o;ey[7]=o;let base=[ex,ey,[...b.w.map(e),z],[...b.w.map((t,i)=>e(mul(t,b.c[i]))),z]];
 for(let v of vs){let dv=I.map((t,i)=>d(e(t),m(v,e(L[i])))),fv=E.map((t,i)=>d(e(t),m(v,e(C[i]))));let g=fd(dv[0],fv[0]);gs.push(g);assert(zero(d(dv[1],m(g,fv[1]))),"quadratic identity");let eta=[...br.map(t=>m(v,e(t))),z];etaList.push(eta);
 let ZZ=Array.from({length:6},(_,j)=>{let cj=c.map(t=>e(pow(t,j))),ij=c.map(t=>e(div(pow(t,j+1),q(j+1))));return d(d(e(div(pow(s,j+1),q(j+1))),sc(eta,ij)),m(g,d(e(pow(s,j)),sc(eta,cj))))});let rows=Array.from({length:6},(_,j)=>[q(j===0?1:0),Q1,q(1,j+1),q(1,j+2)]);let coefZ=trans([0,1].map(i=>solve(rows.slice(0,4),ZZ.slice(0,4).map(t=>t[i]))));for(let j=0;j<6;j++)assert(zero(d(ZZ[j],sc(coefZ,rows[j].map(e)))),"six lower moments");
 let Z=ex.map((_,j)=>sc(coefZ,base.map(row=>row[j]))),inc=Z.map((t,i)=>d(p(t,sc(eta,old.map(row=>e(row[i])))),m(g,eta[i])));A.push([...inc,...Array(A.length-8).fill(z),g])}
 A.forEach(row=>{while(row.length<10)row.push(z)});let ca=[...c,s,s],lam=fd(vs[1],d(vs[1],vs[0]));for(let i=0;i<10;i++){assert(zero(d(A[i].reduce(p,z),e(ca[i]))),"physical clock");for(let j=i+1;j<10;j++)assert(zero(A[i][j]),"triangular");}
 let n=treecheck(A,ca,f,tt=>{let sca=ca.map(x=>e(mul(tt.g,pow(x,tt.n-1)))),delta=tt.u.map((t,i)=>d(t,sca[i]));for(let j=0;j<2;j++)assert(zero(d(delta[j+8],sc(etaList[j],delta.slice(0,8)))),"complete ordinary pilot contrast");assert(zero(d(p(m(lam,tt.u[8]),m(d(o,lam),tt.u[9])),sca[8])),"complete ordinary signed mean")});return{seed:"4 x 85 full trees and 127 words",pilots:n,s:str(s),g:gs.map(num),lambda:num(lam),discriminant:str(D)}} 
console.log(main());
```
