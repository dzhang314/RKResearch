# Right-end tests of a Jacobi-pencil factor, including the fixed visible endpoint

These standalone fixed-data tests complement dirk_order15_minimal_two_hidden_quartics_terminal_deleted_resultant_and_pencil_replay_20261123.md. Write J_d=L'_(d+1) for shifted Legendre. A nonzero monic Q of degree <=4 divides x(J_(n+1)+aJ_n), n=5 or 6. At a visible reflected node y=1-t, t either 0 or a root of the pencil, suppose Q(t)≠0 and t≠1. The two moments J[y Q(1-y)](1-t), J[y² Q(1-y)](1-t) cannot both vanish. To see this, the reflected pencil has parameter -a and Q(1-y) divides (1-y) times that pencil. At a nonfixed reflected root the factors not requiring 1-y were already tested in the companion main norm replay at j=1. If one explicit 1-y is removed, the residual root-subset factor has degree k<=3. The unnormalized primitive integrand has the extra factor 1-y, so after division by u^(j+1) replace 1/(j+1+k-l) by 1/(j+1+k-l)-u/(j+2+k-l) in the k-th compound companion. The full resulting numerator degree in u is (k+1)*binom(n,k)+n*binom(n-1,k-1), with unique maximal-degree diagonal from the -y part. k=0 gives functions 1/(j+1)-u/(j+2) for j=1,2, whose zeros 3/2 and 4/3 are distinct. At the fixed endpoint t=0, u=1, Q(t)≠0 excludes an explicit factor 1-y. Use all k-subsets of the varying pencil J_n+zJ_(n-1), n=6,7, with fixed integration endpoint 1. Only the columns containing the last companion index depend on z, with degree <=1, so the exact upper bound is binom(n-1,k-1) and the replay reaches it both times in all cases. Degree after reduction modulo 1009 is verified and every adjacent pair has gcd 1. The determinant-of-integrated-compound interpretation, valid at repeated roots, is detailed in the companion cited above.

```javascript
function replay(p=1009){
const m=a=>(a%p+p)%p, pw=(a,k)=>{let s=1;for(;k;k>>=1,a=m(a*a))if(k&1)s=m(s*a);return s},iv=z=>pw(z,p-2),choose=(a,b)=>{if(b<0||b>a)return 0;let s=1;for(let i=0;i<b;i++)s=s*(a-i)/(i+1);return s},trim=a=>{while(a.length&&!a.at(-1))a.pop();return a},ev=(a,z)=>a.reduceRight((s,v)=>m(s*z+v),0);
function subrem(a,b){a=a.slice();let t=iv(b.at(-1));while(a.length>=b.length){let d=a.length-b.length,c=m(a.at(-1)*t);for(let j=0;j<b.length;j++)a[j+d]=m(a[j+d]-c*b[j]);trim(a)}return a}
function gcd(a,b){while(b.length)[a,b]=[b,subrem(a,b)];let t=iv(a.at(-1));return a.map(z=>m(z*t))}
function interp(vals){let a=Array(vals.length).fill(0),b=[1];for(let i=0;i<a.length;i++){for(let j=0;j<b.length;j++)a[j]=m(a[j]+vals[0]*b[j]);vals=vals.slice(1).map((v,j)=>m(v-vals[j]));let c=Array(b.length+1).fill(0);for(let j=0;j<b.length;j++){c[j]=m(c[j]-i*b[j]);c[j+1]=m(c[j+1]+b[j])}b=c.map(z=>m(z*iv(i+1)))}return trim(a)}
function det(a){let d=1,n=a.length;for(let i=0;i<n;i++){let k=i;while(k<n&&!a[k][i])k++;if(k===n)return 0;if(k!==i){[a[k],a[i]]=[a[i],a[k]];d=m(-d)}let t=iv(a[i][i]);d=m(d*a[i][i]);for(let j=i+1;j<n;j++){let b=m(a[j][i]*t);if(b)for(let l=i+1;l<n;l++)a[j][l]=m(a[j][l]-b*a[i][l])}}return d}
function jac(d){return Array.from({length:d+1},(_,k)=>m((-1)**(d-k)*(k+1)*choose(d+1,k+1)*choose(d+k+2,k+1)))}
function sets(n,k){if(!k)return[[]];let a=[];for(let z=0;z<=n-k;z++)for(let s of sets(n-z-1,k-1))a.push([z,...s.map(i=>i+z+1)]);return a}
function norm(n,k,j,weight=0,at1=false){const hi=jac(at1?n:n+1),lo=jac(at1?n-1:n),S=sets(n,k),h=S.length,ids=new Map(S.map((s,i)=>[s.toString(),i])),c7=choose(n-1,k-1),D=at1?c7:(k+weight)*h+n*c7;
  const vals=[];for(let par=0;par<=D;par++){let u=at1?1:par;let H=ev(hi,u),L=ev(lo,u),t=0,q=[];for(let z=n+1;z>=1;z--){t=m(u*t+hi[z]*L-(lo[z]||0)*H);q[z-1]=t}if(!at1&&m(u*t+hi[0]*L-lo[0]*H))throw Error("CD");
    if(at1)q=hi.map((z,i)=>m(z+par*(lo[i]||0)));let M=Array.from({length:h},()=>Array(h).fill(0));for(let col=0;col<h;col++){let s=S[col];for(let mask=0;mask<1<<k;mask++){
      let l=0,old=s.map((v,i)=>{let b=mask>>i&1;l+=b;return v+b});let t0=m(pw(u,k-l)*(weight?m(iv(j+1+k-l)-u*iv(j+2+k-l)):iv(j+1+k-l)));let rep=old.at(-1)===n;
      for(let z=rep?0:old.at(-1),last=rep?n-1:z;z<=last;z++){const e=[...old.slice(0,-1),z];if(new Set(e).size!==k)continue;let sg=l+(rep?1:0);for(let i=0;i<k;i++)for(let o=i+1;o<k;o++)if(e[i]>e[o])sg++;
        let term=m(t0*(rep?q[z]:(s.at(-1)===n-1?q[n]:1)));let row=ids.get(e.sort((a,b)=>a-b).toString());M[row][col]=m(M[row][col]+(sg%2?-term:term))}}}
    vals.push(det(M))}
  let a=interp(vals);let lc=m(pw(m(hi[n+1]*lo[n]),c7)*pw(weight?m(-iv(j+k+2)):iv(j+k+1),h));if(!at1&&(a.length!==D+1||a.at(-1)!==lc||!lc))throw Error("degree");return a}
function syl(f,g){let n=f.length-1,d=g.length-1,M=[];for(let i=0;i<d;i++)M.push([...Array(i).fill(0),...f.slice().reverse(),...Array(d-1-i).fill(0)]);for(let i=0;i<n;i++)M.push([...Array(i).fill(0),...g.slice().reverse(),...Array(n-1-i).fill(0)]);return det(M)}
let out=[];for(const n of [5,6])for(let k=1;k<=3;k++){let a=norm(n,k,1,1),b=norm(n,k,2,1);out.push([n,k,'factor1-y',a.length-1,b.length-1,gcd(a,b)]);}
for(const n of [6,7])for(let k=1;k<=4;k++){let a=norm(n,k,1,0,true),b=norm(n,k,2,0,true);out.push([n,k,'u=1',choose(n-1,k-1),a.length-1,b.length-1,gcd(a,b)]);}return out;}
const o=replay(1009); for(const row of o){if(row.at(-1).toString()!=="1")throw Error("gcd");if(row[2]==="u=1"&&(row[3]!==row[4]||row[3]!==row[5]))throw Error("degree");}console.log(o);
```

Output: for n=5,6 and k=1,2,3, degrees with 1-y respectively (15,50,70) and (18,75,140), all six gcds 1; for endpoint n=6,7 and k=1,2,3,4 degrees (1,5,10,10) and (1,6,15,20), all eight gcds 1.
