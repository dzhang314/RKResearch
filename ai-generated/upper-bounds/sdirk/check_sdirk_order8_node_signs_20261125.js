// Exact signs for the fixed SDIRK(11,8) quadrature node audit.
// Standalone Node.js, integer arithmetic only. No root evaluations/search.
// For s=(13+S)/32, t=(25+T)/200 with 0<=S,T<=1, certify the
// signs of D, N_B(0), N_B(1+3s) by bivariate Bernstein coefficients.
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
let Z = [mon(1n)];
for (const r of [mon(2n), add(mon(1n), s), sc(s, 2n), sc(t, 2n)]) {
  const q = Array.from({length: Z.length + 1}, () => mon());
  for (let k = 0; k < Z.length; k++) {
    q[k] = add(q[k], mul(r, Z[k]), -1n);
    q[k + 1] = add(q[k + 1], Z[k]);
  }
  Z = q;
}
const powers = [mon(1n)];
for (let i = 1; i <= 7; i++) powers.push(mul(powers[i - 1], z2));
const M = Array.from({length: 4}, (_, j) =>
  Z.reduce((p, c, k) => add(p, sc(mul(c, powers[j + k]), 840n / BigInt(j + k + 1))), mon()));
const D = add(mul(M[0], M[2]), mul(M[1], M[1]), -1n);
const N1 = add(mul(M[1], M[2]), mul(M[0], M[3]), -1n);
const N0 = add(mul(M[1], M[3]), mul(M[2], M[2]), -1n);
const NBz = add(add(mul(D, powers[2]), mul(N1, z2)), N0);
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
const checks = [["D", D, 1], ["N_B(0)", N0, -1], ["N_B(z2)", NBz, -1]];
for (const [name, poly, sign] of checks) {
  const {m, n, min, max, scale} = bernsteinRange(poly);
  if (sign > 0 ? min <= 0n : max >= 0n) throw Error("inconclusive sign: " + name);
  console.log([name, m, n, min, max, scale].map(String).join(" "));
}
