// Fixed SDIRK(11,8): exact whole-box chart-guard signs, not calibration.
// Standalone Node.js. Only BigInt polynomial arithmetic; no root calculation.
// s=(13+S)/32 and t=(25+T)/200, with 0<=S,T<=1.
// Output: guard name, s-degree, t-degree, min, max, positive Bernstein scale.
const key = (i, j) => i + ":" + j;
const ex = k => k.split(":").map(Number);
const mon = (c = 0n, i = 0, j = 0) => c ? new Map([[key(i, j), c]]) : new Map();
function add(p, q, a = 1n) {
  const r = new Map(p);
  for (const [k, c] of q) {
    const d = (r.get(k) || 0n) + a * c;
    if (d) r.set(k, d); else r.delete(k);
  }
  return r;
}
const sc = (p, a) => add(mon(), p, a);
function mul(p, q) {
  let r = mon();
  for (const [ab, c] of p) for (const [cd, d] of q) {
    const [i, j] = ex(ab), [k, l] = ex(cd);
    r = add(r, mon(c * d, i + k, j + l));
  }
  return r;
}
function bin(n, k) {
  let a = 1n;
  for (let i = 1; i <= k; i++) a = a * BigInt(n + 1 - i) / BigInt(i);
  return a;
}
function fac(n) {
  let r = 1n;
  for (let i = 2; i <= n; i++) r *= BigInt(i);
  return r;
}
const ipow = (a, n) => a ** BigInt(n);
const s = mon(1n, 1), t = mon(1n, 0, 1), z2 = add(mon(1n), sc(s, 3n));

function timesLinear(poly, c0, c1) {
  const q = Array.from({length:poly.length+1},()=>mon());
  for(let k=0;k<poly.length;k++) {
    q[k]=add(q[k],mul(c0,poly[k]));
    q[k+1]=add(q[k+1],mul(c1,poly[k]));
  }
  return q;
}
const w=[mon(2n),add(mon(1n),s),sc(s,2n),sc(t,2n)];
const P=Array.from({length:4},(_,i)=>{
  let q=[mon(1n)];
  for(let k=0;k<4;k++) if(k!==i) q=timesLinear(q,sc(w[k],-1n),z2);
  return Array.from({length:5},(_,n)=>
    q.reduce((r,p,k)=>add(r,sc(p,840n/BigInt(n+k+1))),mon()));
});
function det3(A) {
  let v=mon();
  for(let i=0;i<3;i++){
    const j=(i+1)%3,k=(i+2)%3;
    v=add(v,mul(A[0][i],add(mul(A[1][j],A[2][k]),mul(A[1][k],A[2][j]),-1n)));
  }
  return v;
}
const Q=P.map(a=>det3([a.slice(0,3),a.slice(1,4),a.slice(2,5)]));
const R = P[1];
const m=Array.from({length:4},(_,j)=>add(mul(z2,R[j+1]),mul(w[1],R[j]),-1n));
const A=Array.from({length:3},(_,j)=>
  add(sc(mul(z2,add(R[0],R[j+2],-1n)),12n/BigInt(j+2)),
      sc(mul(w[1],add(R[0],R[j+1],-1n)),12n/BigInt(j+1)),-1n));
const J=det3([A,m.slice(0,3),m.slice(1,4)]);
function bernsteinRange(poly) {
  const terms = [...poly].map(([k, c]) => [...ex(k), c]);
  const m = Math.max(...terms.map(([i]) => i));
  const n = Math.max(...terms.map(([, j]) => j));
  const p = Array.from({length: m + 1}, (_, k) =>
    Array.from({length: n + 1}, (_, l) =>
      terms.reduce((a, [i, j, c]) => i < k || j < l ? a :
        a + c * bin(i, k) * ipow(13n, i - k) * ipow(32n, m - i) *
            bin(j, l) * ipow(25n, j - l) * ipow(200n, n - j), 0n)));
  let min, max;
  for (let a = 0; a <= m; a++) for (let b = 0; b <= n; b++) {
    let c = 0n;
    for (let k = 0; k <= a; k++) for (let l = 0; l <= b; l++) {
      c += p[k][l] * bin(a, k) * bin(b, l) *
        fac(k) * fac(m - k) * fac(l) * fac(n - l);
    }
    if (min === undefined || c < min) min = c;
    if (max === undefined || c > max) max = c;
  }
  const scale = ipow(32n, m) * ipow(200n, n) * fac(m) * fac(n);
  return {m, n, min, max, scale};
}

const guards = [...Q.map((p,i)=>["Omega"+i,p,[-1,1,-1,1][i]]),["J0",J,1]];
for (const [name,p,sign] of guards) {
  const {m,n,min,max,scale}=bernsteinRange(p);
  if (sign > 0 ? min <= 0n : max >= 0n) throw Error("inconclusive: "+name);
  console.log([name,m,n,min,max,scale].map(String).join(" "));
}
