# Independent exact split-grid replay: only the fifth and sixth payments at order 20

The first loop constructs all five first/second primitive moment rows plus the value at a grid site, on the monomial basis 1,…,y⁵; the second integrates the entire five-omitted-site factor polynomial directly. Both use only bounded exact integer operations (all modular intermediate products below the exact JavaScript integer range), enumerate roots directly, and include both fixed endpoints. The split primes are those independently established as good in the prior real note; the products below were recomputed from scratch. The check fixes no unknown tableau coefficient or arrangement of stages. Each total product is symmetric over every permutation of the nine L′ roots, and its nonzero image excludes every possible zero factor in characteristic zero.

```javascript
function chart(p,which){
const m=n=>(n%p+p)%p, pw=(x,k)=>{let v=1;while(k){if(k&1)v=v*x%p;x=x*x%p;k=Math.floor(k/2);}return v;},inv=x=>pw(x,p-2);
function ch(n,k){let z=1;for(let j=1;j<=k;j++)z=z*(n-j+1)/j;return Math.round(z);}
let l=Array.from({length:11},(_,j)=>m(((10-j)%2?-1:1)*ch(10,j)*ch(10+j,j)));
let der=l.slice(1).map((a,j)=>m((j+1)*a));
function ev(a,x){let o=0;for(let j=a.length-1;j>=0;j--)o=m(o*x+a[j]);return o}
let rr=[];for(let x=0;x<p;x++)if(!ev(der,x))rr.push(x);if(rr.length!==9||rr.includes(0)||rr.includes(1))throw Error("bad split");
const grid=[0,1,...rr],non=grid.slice(1);
function det(A){A=A.map(r=>r.slice());let d=1;for(let i=0;i<A.length;i++){let k=i;while(k<A.length&&!A[k][i])k++;if(k===A.length)return 0;if(k!==i){[A[i],A[k]]=[A[k],A[i]];d=m(-d)}let v=A[i][i];d=d*v%p;let iv=inv(v);for(let l=i+1;l<A.length;l++){let g=A[l][i]*iv%p;for(let j=i;j<A.length;j++)A[l][j]=m(A[l][j]-g*A[i][j]);}}return d;}
let c=0,prod=1;
const I=(u,a)=>pw(u,a+1)*inv(a+1)%p;
if(which===1){for(let u of non)for(let v of non)if(u!==v)for(let z of grid){
let A=[];for(let h=1;h<=3;h++)A.push(Array.from({length:6},(_,j)=>I(u,j+h)));
for(let h=1;h<=2;h++)A.push(Array.from({length:6},(_,j)=>m(I(v,j+h+1)-u*I(v,j+h))));
A.push(Array.from({length:6},(_,j)=>pw(z,j)));let t=det(A);if(!t)throw Error("singular option 1");prod=prod*t%p;c++;
}}else{for(let u of non){let sites=grid.filter(x=>x!==u);
function gen(start,A,n){if(!n){
let im=h=>A.reduce((s,x,j)=>m(s+x*I(u,j+h)),0), t=m(im(1)*im(3)-im(2)**2);
if(!t)throw Error("singular option 2");prod=prod*t%p;c++;return;}
for(let i=start;i<=sites.length-n;i++){const z=sites[i],B=Array(A.length+1).fill(0);for(let j=0;j<A.length;j++){B[j]=m(B[j]-z*A[j]);B[j+1]=m(B[j+1]+A[j]);}gen(i+1,B,n-1);}}
gen(0,[1],5);
}}
console.log(p,rr.join(","),c,prod);return [c,prod];}
const a=chart(3373,1),b=chart(4523,2);if(a[0]!==990||b[0]!==2520)throw Error("count");
```

Executed output: prime, nine interior roots modulo it, number of cases, nonzero total product.
```
3373 103,505,511,895,1687,2479,2863,2869,3271 990 2859
4523 78,846,1455,1949,2262,2575,3069,3678,4446 2520 1384
```
