# Standalone degree-six Jacobi-kernel and pencil squarefreeness replay

This supports the terminal-deleted seventeen-signature argument. Define J_d=L'_(d+1) for the shifted Legendre L_m. These are nonzero rational multiples of the monic Jacobi polynomials for x(1-x) dx. In either the degree-seven pencil J7+a J6 or a degree-six pencil J6+a J5, take a root u not equal to zero. If Q is monic, has degree at most four, divides x(J_(n+1)+a J_n) and Q(u) is nonzero, then its two moments J[xQ](u) and J[x²Q](u) cannot both vanish. The statement specializes to the fixed degree-six J6. Here n=5 or 6. The proof only tests the fixed rational pencil and no RK array coefficients.

Since consecutive Jacobi polynomials are coprime, J_n(u) is nonzero. The other n roots, including repetitions, are those of q(x,u)=(J_(n+1)(x)J_n(u)-J_n(x)J_(n+1)(u))/(x-u), up to units. A factor not containing x divides q. If the factor contains x once or more, take out one x only; the rest divides q. For each k=1,...,4 and j=1, or k=1,...,3 and j=2, take the product of the normalized primitive u^(-j-1)J[x^j V](u) over all degree-k monic root-subset factors V of q. (For k=0 the moment is a nonzero unit.) To check its numerator construct the k-th compound matrix of xI-M for the standard n-by-n column companion M of q. The basis is indexed by increasing k-subsets. Integrate its coefficients and take its determinant; triangularizing M proves the product identity even for repeated roots. Clear the common denominator q_n(u) in each compound column involving the last index. The resulting polynomial has degree precisely k*binom(n,k)+n*binom(n-1,k-1): in each column only the identity term x^k can have the full u degree, and its diagonal coefficient is 1/(k+j+1) times q_n where the last index occurs. The replay checks this leading unit in every interpolation. At p=1009 every adjacent pair for j,j+1 has monic gcd 1: exact degrees for n=5 at k=1,2,3,4 are 10,40,60,40; for n=6 they are 12,60,120,120. This proves nonzero rational resultants, not just absence of roots in the finite base field.

The final check interpolates the fixed-degree Sylvester resultant of J7+aJ6 and its x derivative as a polynomial in a. Its rational degree bound is 12 (the discriminant of a degree-seven polynomial has total coefficient degree 12, and the leading coefficient here is constant). Its actual degree is 12 modulo 1009, with ascending coefficients [515,0,397,0,639,0,337,0,921,0,905,0,922]. Its gcd with its a-derivative is 1 modulo this prime, hence in characteristic zero. A fiber with x-gcd degree at least two would have Sylvester rank deficiency at least two and its determinant would vanish to order at least two at that parameter (expand the determinant after choosing two kernel columns). Thus every degree-seven pencil member has at least six distinct complex roots; no restriction on its pencil parameter is needed. The fixed J6 itself has six simple roots.

```javascript
function replay(p=1009){
const m=a=>(a%p+p)%p, pw=(a,k)=>{let s=1;for(;k;k>>=1,a=m(a*a))if(k&1)s=m(s*a);return s},iv=z=>pw(z,p-2),choose=(a,b)=>{if(b<0||b>a)return 0;let s=1;for(let i=0;i<b;i++)s=s*(a-i)/(i+1);return s},trim=a=>{while(a.length&&!a.at(-1))a.pop();return a},ev=(a,z)=>a.reduceRight((s,v)=>m(s*z+v),0);
function subrem(a,b){a=a.slice();let t=iv(b.at(-1));while(a.length>=b.length){let d=a.length-b.length,c=m(a.at(-1)*t);for(let j=0;j<b.length;j++)a[j+d]=m(a[j+d]-c*b[j]);trim(a)}return a}
function gcd(a,b){while(b.length)[a,b]=[b,subrem(a,b)];let t=iv(a.at(-1));return a.map(z=>m(z*t))}
function interp(vals){let a=Array(vals.length).fill(0),b=[1];for(let i=0;i<a.length;i++){for(let j=0;j<b.length;j++)a[j]=m(a[j]+vals[0]*b[j]);vals=vals.slice(1).map((v,j)=>m(v-vals[j]));let c=Array(b.length+1).fill(0);for(let j=0;j<b.length;j++){c[j]=m(c[j]-i*b[j]);c[j+1]=m(c[j+1]+b[j])}b=c.map(z=>m(z*iv(i+1)))}return trim(a)}
function det(a){let d=1,n=a.length;for(let i=0;i<n;i++){let k=i;while(k<n&&!a[k][i])k++;if(k===n)return 0;if(k!==i){[a[k],a[i]]=[a[i],a[k]];d=m(-d)}let t=iv(a[i][i]);d=m(d*a[i][i]);for(let j=i+1;j<n;j++){let b=m(a[j][i]*t);if(b)for(let l=i+1;l<n;l++)a[j][l]=m(a[j][l]-b*a[i][l])}}return d}
function jac(d){return Array.from({length:d+1},(_,k)=>m((-1)**(d-k)*(k+1)*choose(d+1,k+1)*choose(d+k+2,k+1)))}
function sets(n,k){if(!k)return[[]];let a=[];for(let z=0;z<=n-k;z++)for(let s of sets(n-z-1,k-1))a.push([z,...s.map(i=>i+z+1)]);return a}
function norm(n,k,j){const hi=jac(n+1),lo=jac(n),S=sets(n,k),h=S.length,ids=new Map(S.map((s,i)=>[s.toString(),i])),c7=choose(n-1,k-1),D=k*h+n*c7;
  const vals=[];for(let u=0;u<=D;u++){let H=ev(hi,u),L=ev(lo,u),t=0,q=[];for(let z=n+1;z>=1;z--){t=m(u*t+hi[z]*L-(lo[z]||0)*H);q[z-1]=t}if(m(u*t+hi[0]*L-lo[0]*H))throw Error("CD");
    let M=Array.from({length:h},()=>Array(h).fill(0));for(let col=0;col<h;col++){let s=S[col];for(let mask=0;mask<1<<k;mask++){
      let l=0,old=s.map((v,i)=>{let b=mask>>i&1;l+=b;return v+b});let t0=m(pw(u,k-l)*iv(j+1+k-l));let rep=old.at(-1)===n;
      for(let z=rep?0:old.at(-1),last=rep?n-1:z;z<=last;z++){const e=[...old.slice(0,-1),z];if(new Set(e).size!==k)continue;let sg=l+(rep?1:0);for(let i=0;i<k;i++)for(let o=i+1;o<k;o++)if(e[i]>e[o])sg++;
        let term=m(t0*(rep?q[z]:(s.at(-1)===n-1?q[n]:1)));let row=ids.get(e.sort((a,b)=>a-b).toString());M[row][col]=m(M[row][col]+(sg%2?-term:term))}}}
    vals.push(det(M))}
  let a=interp(vals);let lc=m(pw(m(hi[n+1]*lo[n]),c7)*pw(iv(j+k+1),h));if(a.length!==D+1||a.at(-1)!==lc||!lc)throw Error("degree");return a}
function syl(f,g){let n=f.length-1,d=g.length-1,M=[];for(let i=0;i<d;i++)M.push([...Array(i).fill(0),...f.slice().reverse(),...Array(d-1-i).fill(0)]);for(let i=0;i<n;i++)M.push([...Array(i).fill(0),...g.slice().reverse(),...Array(n-1-i).fill(0)]);return det(M)}
let ms=[];for(let n of [5,6])for(let j of [1,2])for(let k=1;k<=(j===1?4:3);k++){let a=norm(n,k,j),b=norm(n,k,j+1),g=gcd(a,b);ms.push([n,k,j,a.length-1,g.length-1,g]);}
let H=jac(7),L=jac(6),vals=[];for(let t=0;t<=12;t++){let V=H.map((z,i)=>m(z+t*(L[i]||0))),d=V.slice(1).map((z,i)=>m(z*(i+1)));vals.push(syl(V,d))}let disc=interp(vals),g=gcd(disc,disc.slice(1).map((z,i)=>m(z*(i+1))));return {ms,disc,discG:g}
}
const {ms,disc,discG}=replay(1009);
if(ms.length!==14||ms.some(x=>x[4]!==0)||disc.length!==13||discG.toString()!=="1")throw Error("failed");
console.log(ms,disc,discG);
```

The numerical checks above were executed as written. Details of the general compound-norm derivation at n=8 can also be found in dirk_order19_cd_factor_norm_replay_20261123.md.
