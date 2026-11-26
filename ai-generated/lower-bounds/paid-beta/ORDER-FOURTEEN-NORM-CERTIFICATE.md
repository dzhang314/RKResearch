# A physical order for the omitted roots in saturated ERK charts

Scope: a field with the order factorial nonzero. All conclusions concern the stated quartic terminal charts, not a new tableau search. Source base c1d29976a37f7f264f7123bf0cd69a8126a107b3. Use the usual rooted pair rule: a column with polynomial profile F gets profile JF under one A, and multiplying a column by a clock polynomial multiplies its profile. J integrates formally from zero.

In the even order-2q chart, q=6,7,8, suppose e_s=H(c)+d with d∈F_q, H(1)=1 and H a nonzero multiple of x D_(q−1). The compensated quartic head is w=P(c) on its support S and zero on the support T of its invariant core; F_q is supported on S∪T. The head's polynomial P divides D_(q−1) in the branch P(0)≠0, and w is in F_4 for q=6, or w,Cw are in F_5 for q=7,8. Let e_T be the indicator in the core. Define z_M=(M P)(c)(1−e_T)−M(C)w. Its pair profile is MP, and on actual coordinates it is supported outside S∪T. For masks M of degree ≤q−4, z_M lies in E_q; an A action through deg M≤q−5 then reads J(MP)(c) exactly on every off-support coordinate. These degree claims follow by direct counting, using Cw∈F5 when q≥7.

Let R be the distinct nonzero clocks outside S∪T with P(c)≠0, excluding the terminal row. Each is a root of D_(q−1)/P, because e_s is zero there, F_q vanishes there, and H=x D_(q−1) up to nonzero scaling. If fewer than q−5 clocks occurred, take M=x∏_(u∈R)(x−u). Then z_M is a nonzero multiple of e_s: every nonterminal off entry is zero, and the terminal has c=1, H(1)=1, and P(1)≠0. Its polynomial component would have degree <q, contradicting separation and the degree-q terminal polynomial. Thus all q−5 roots of the complementary factor are distinct, nonzero, and attained at actual nonterminal rows outside both supports. Order them u_1,...,u_m by first physical occurrence, m=q−5. For every k≤m and 0≤h≤m−k, strict chronology at that first occurrence gives
  ∫_0^(u_k) x^(1+h) P(x) ∏_(i<k)(x−u_i) dx = 0.
Indeed its compensated column vanishes at all earlier rows, and its polynomial degree after applying A is at most q. In particular the last nonterminal clock u_m must satisfy
  ∫_0^(u_m) x D_(q−1)(x)/(x−u_m) dx = 0.
This condition depends on a single root, not a chosen set of quartic roots.
For a polynomial F with F(u)=0 and u≠0, synthetic division gives the exact harmonic test
  ∫_0^u x^(1+h) F(x)/(x−u) dx
    = u^(h+1) ∑_(i≥1) F_i u^i ∑_(j=0)^(i−1) 1/(h+j+2).
Use F = D_(q−1)/∏_(j>k)(x−u_j) at successive nonterminal sites. It is therefore natural to check the last root first, divide it out, and use the tests on the resulting smaller polynomial. This yields a triangular finite root-ring test.
## Exact two-norm result
The determinant computation below was run purely in one tool isolate with BigInt, not a project, solver, or external process. The first norm is for the later (second) physical nonterminal complement root, and the second is for the earlier first-root moment. Both are nonzero; their integer gcd is exactly 3^156·11^142·13^134. These are factorial units. A common field point annihilates both moments, whence both multiplication determinants vanish on that field; the gcd excludes it in every paid characteristic. No factorization of the two individual integers or search over fields is used.

The scaled monic coefficients are ["14530697473149","-914519421387","17764557525","-151833825","637065","-1287","1"]. The absolute determinants have 517 and 450 digits. The exact deterministic check, ready to replay in an isolated JavaScript cell, is:

```js
const L=429n;
const B=[1n,-27n,225n,-825n,1485n,-1287n].map((b,i)=>b*L**BigInt(5-i)).concat([1n]);
const zeroV=()=>Array(6).fill(0n);
const add=(a,b)=>a.map((x,i)=>x+b[i]); const scale=(a,s)=>a.map(x=>x*s);
const byV=a=>a.map((_,i)=>(i===0?0n:a[i-1])-a[5]*B[i]);
const prodV=(a,b)=>{let res=zeroV();for(let i=5;i>=0;--i)res=add(byV(res),scale(b,a[i]));return res};
const zeroUV=()=>Array.from({length:5},zeroV);
const quo=Array.from({length:6},(_,i)=>Array.from({length:6},(_,j)=>B[i+j+1]??0n));
const byU=a=>a.map((_,i)=>add(i===0?zeroV():a[i-1],scale(prodV(a[4],quo[i]),-1n)));
const multiplication=a=>{let cols=[];for(let j=0;j<5;j++,a=byU(a)){let b=a;for(let i=0;i<6;i++,b=b.map(byV))cols.push(b.flat());}return cols[0].map((_,k)=>cols.map(c=>c[k]));};
const vPower=(x,h)=>{for(let i=0;i<h;++i)x=byV(x);return x};
function uPower(q,h){let a=zeroUV();a[0]=q;for(let i=0;i<h;++i)a=byU(a);return a}
function first(k){let a=zeroUV();for(let i=1;i<=5;i++){let s=0n;for(let j=0;j<i;j++)s+=420n/BigInt(j+k+1);const u=uPower(quo[i],i+k);a=a.map((row,j)=>add(row,scale(u[j],s)));}return a}
let later=zeroUV();for(let j=0;j<=5;j++)later[0]=add(later[0],scale(vPower(quo[j],j+2),420n/BigInt(j+2)));
function det(M){M=M.map(a=>a.slice());let prev=1n,sgn=1n;for(let k=0;k<M.length-1;k++){let t=k;while(t<M.length&&M[t][k]===0n)t++;if(t===M.length)return 0n;if(t!==k){[M[t],M[k]]=[M[k],M[t]];sgn=-sgn};const b=M[k][k];for(let i=k+1;i<M.length;i++)for(let j=k+1;j<M.length;j++){const c=M[i][j]*b-M[i][k]*M[k][j];if(c%prev!==0n)throw Error("fraction");M[i][j]=c/prev};prev=b}return sgn*M.at(-1).at(-1)}
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b)[a,b]=[b,a%b];return a}
const d=later&&det(multiplication(later)), e=det(multiplication(first(1)));
if(gcd(d,e)!==3n**156n*11n**142n*13n**134n)throw Error("unexpected gcd");
text({later:String(d),first:String(e),gcd:String(gcd(d,e))});
```
