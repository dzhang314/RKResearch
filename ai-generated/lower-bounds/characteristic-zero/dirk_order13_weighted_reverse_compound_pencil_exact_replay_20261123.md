# Standalone exact replay: unrestricted order-13 divided Jacobi pencil

Run the following standalone ES2020 JavaScript in Node or any recent JS engine with console.log. The companion denominator is never inverted. It builds each exterior-power entry as the literal determinant of a k×k submatrix, evaluates the degree-k polynomial in t at 0,…,k and integrates it exactly by interpolation. Reconstruct the u-polynomials through their proved max degrees 40 and 60, test two additional points, then compute polynomial gcd (not merely finite-field roots). For p=1009,1013 all unreduced integer operations are within 2^53, including the small binomial recurrence, checked by their integer values. Inputs D_n=L_(n+1)′ are unnormalized integer shifted-Legendre derivatives.

~~~javascript
function run(pr,k){
const mod=x=>(x%pr+pr)%pr;const pow=(x,n)=>{let y=1;while(n){if(n&1)y=mod(y*x);x=mod(x*x);n>>=1}return y};const inv=x=>pow(x,pr-2);const C=(n,k)=>{let z=1;for(let i=0;i<k;i++)z=z*(n-i)/(i+1);return Math.round(z)};
const val=(p,x)=>p.reduceRight((a,b)=>mod(a*x+b),0);
const derivL=n=>Array.from({length:n+1},(_,i)=>mod((i+1)*(-1)**(n-i)*C(n+1,i+1)*C(n+i+2,i+1)));
const n=5,A6=derivL(6),A5=[...derivL(5),0];function h(u){let a=val(A6,u),b=val(A5,u),r=0,q=[];for(let i=6;i>=1;i--){r=mod(u*r+b*A6[i]-a*A5[i]);q[i-1]=r}if(mod(u*r+b*A6[0]-a*A5[0]))throw Error("division");return q}
const I=[];for(let m=0;m<32;m++){let a=[];for(let i=0;i<5;i++)if(m>>i&1)a.push(i);if(a.length===k)I.push(a)}
const det=a=>{a=a.map(r=>[...r]);let d=1;for(let i=0;i<a.length;i++){let j=i;while(j<a.length&&!a[j][i])j++;if(j===a.length)return 0;if(j!==i){[a[i],a[j]]=[a[j],a[i]];d=-d}let pv=a[i][i];d=mod(d*pv);for(let j=i+1;j<a.length;j++){let f=mod(a[j][i]*inv(pv));for(let l=i+1;l<a.length;l++)a[j][l]=mod(a[j][l]-f*a[i][l])}}return d};
const interp=y=>{let base=[1],q=Array(y.length).fill(0),yd=[...y];for(let j=0;j<y.length;j++){base.forEach((v,i)=>q[i]=mod(q[i]+yd[0]*v));yd=yd.slice(1).map((v,i)=>mod(v-yd[i]));let r=inv(j+1);base=Array.from({length:base.length+1},(_,i)=>mod(((base[i-1]||0)-j*(base[i]||0))*r));}return q};
let ws=[];for(let a of [1,2]){ws[a]=Array.from({length:k+1},(_,l)=>{const q=interp(Array.from({length:k+1},(_,j)=>+(j===l)));return q.reduce((s,v,i)=>mod(s+v*inv(a+i+1)),0)});}
const m=I.length,cap=2*k*m,vals=[[],[],[]];for(let u=0;u<=cap+2;u++){let q=h(u),D=[[],[],[]];for(let l=0;l<=k;l++){let H=Array.from({length:5},(_,i)=>Array.from({length:5},(_,j)=>mod((i===j?u*l*(j===4?q[5]:1):0)+(j===4?q[i]:0)-(i===j+1&&j<4?1:0))));D[l]=I.map(r=>I.map(c=>det(r.map(i=>c.map(j=>H[i][j])))))}for(let a of [1,2])vals[a].push(det(I.map((r,i)=>I.map((c,j)=>D.reduce((s,M,l)=>mod(s+ws[a][l]*M[i][j]),0)))));}
const cs=[1,2].map(a=>interp(vals[a].slice(0,cap+1)));for(let i=0;i<2;i++)if(!cs[i].at(-1)||[1,2].some(j=>val(cs[i],cap+j)!==vals[i+1][cap+j]))throw Error("degree or check");
const trim=a=>{while(a.length&&!a.at(-1))a.pop();return a};function gcd(a,b){while(b.length){let d=[...a],c=inv(b.at(-1));while(d.length>=b.length){let z=mod(d.at(-1)*c),i=d.length-b.length;for(let j=0;j<b.length;j++)d[i+j]=mod(d[i+j]-z*b[j]);trim(d)}a=b;b=d}return a.map(t=>mod(t*inv(a.at(-1))))}
return {pr,k,cap,lc:cs.map(a=>a.at(-1)),gcd:gcd(...cs),v:vals.slice(1).map(a=>a.slice(-2))}}

for(const p of [1009,1013])for(const k of [2,3])console.log(run(p,k));
~~~

Each gcd is [1]. For modules 1009 and 1013 respectively, k=2 gives LCs (346,363) and (92,1003) with paired held-out residues ((208,404),(145,870)) and ((309,547),(741,947)); k=3 gives LCs (721,334),(795,287) with holdouts ((612,920),(537,898)), ((663,722),(337,953)). Full proof and singular/duplicated-root handling: dirk_order13_weighted_reverse_nonlocal_and_compound_pencil_forbids_sixteen_20261123.md.
