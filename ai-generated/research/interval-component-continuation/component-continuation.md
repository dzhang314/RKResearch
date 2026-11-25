# Component-aware interval continuation and two exact further rules

The [real window criterion](../interval-real-pencil/interval-real-pencil.md)
separates an interior real split cubic from a reachable rational
point on its ordered elliptic curve. This note adds two deterministic
selection tools: a linear-time negative-pole pair gate after sorting
the finite support, and a continued-fraction target for one elliptic
multiple in a certified reachable real arc. They are not rational
grid searches.

Starting from the checked order-16 rule, the bounded prescribed path
below gives **15 interval sites at exact order 17** and **16 at exact
order 18**. Its next negative-pole pair has an exactly negative real
window. The path stopped there; no interval result at orders 19 or
20 follows.

## 1. Choose a negative-pole pair without guessing

Let \(P\) be the monic nodal polynomial of an exact order-\(n+2\)
rule on \(n\) distinct contributing rational sites in \([0,1]\).
Write \(h=\mathcal I(X^2P)\ne0\) and
\(C_x=\mathcal I(P/(X-x))\ne0\).
For each **interior** site define its buffer
\[
                      \rho_x=\frac{|h/C_x|}{x(1-x)}.
\]
A pair \(0<u<v<1\) has both residues negative exactly when
\(h/C_u<0<h/C_v\). Indeed the two residues in
\(F(X)=X+R_u/(X-u)+R_v/(X-v)\) are \(R_u=h/(C_u(v-u))\) and
\(R_v=-h/(C_v(v-u))\).
For such a pair the interval-window width is
\[
       F(1)-F(0)
        =1-\frac{\rho_u+\rho_v}{v-u}.
\]
So the gate is simply
\[
                        u+\rho_u < v-\rho_v.              \tag{1}
\]
It is an exact condition for this all-split negative-pole class,
not a condition for mixed-sign poles.

Sort the interior nodes. At each possible right site with
\(h/C_v>0\), keep the least \(u+\rho_u\) among earlier nodes
with \(h/C_u<0\), breaking ties by label; comparing it to
\(v-\rho_v\) tests whether any left site for this \(v\) passes.
This is one pass after the cofactor data and sorting are available.
It can maximize the additive margin in (1) and deterministically
propose another pair when a required fresh pair fails. A failed
comparison for all right sites excludes the entire negative-pole
class, not mixed-sign windows. A positive-margin pair still needs
a smooth nontorsion model for a density-based fallback; one can
check smoothness and the three exact multiples of its infinity
point, or directly check a proposed rank-free triple.

If using consecutive fresh triples, the canonical negative pair
needs no whole-support pass. Sort the last three new sites as
\(L<M<R\) (they are on the left, middle, right branches of the old
negative-pole map). If \(\delta=h_{\rm current}/h_{\rm previous}\),
take \((L,M)\) for \(\delta<0\) and \((M,R)\) for \(\delta>0\).
This gives both negative signs by the exact fresh-cofactor
formula, but (1) must still be checked. In particular, when
(1) fails for that selected pair, no elliptic multiple can
repair its real window. Switching pairs requires a separate
gate, not additional arithmetic on the failed curve.

A useful fixed priority is: try the canonical fresh pair if it
passes (1); otherwise use the best witnessed alternative from
the finite support. If no negative pair is certified, use the
general four-cut test and explicitly track the split component
for any mixed-sign trial. Under fixed resource limits, uncertainty
in a sign, width, component, or arithmetic test gives a stop,
not a proof of nonexistence. The actual replay below is narrower:
it tests only the canonical fresh pair, and stops before the
fallback upon its first failed gate.

## 2. One targeted real elliptic multiple, rather than a scan

Suppose an ordered real arc on a smooth completion curve \(E\)
has all the strict interval signs and avoids the finite collision,
inactive-weight and unpaid-defect conditions. The arc must lie on
a reachable component. For \(E(\mathbb R)^0\) take offset \(A=O\);
for the other component first require a verified rational offset
\(A\) there. Let \(D\) be a rational nontorsion point. Translation
by \(-A\) moves the target to \(E(\mathbb R)^0\).

Use the invariant differential for an oriented group coordinate
\(\phi:E(\mathbb R)^0\to\mathbb R/\mathbb Z\), normalized by its
real period and with \(\phi(O)=0\). Integrals of the invariant
differential are additive modulo that period. A certificate may
choose any rational phase subinterval \((a,b)\) strictly within
the translated arc, not crossing the coordinate cut. Shrinking
an open interval and choosing rational endpoints are legitimate
after the finite exclusions. Set \(w=b-a>0\) and let
\(\theta=\phi([2]D)\); \(\theta\) is irrational because \(D\) is
nontorsion.

Take a continued-fraction convergent \(p/m\) of \(\theta\) with
\(m>3/w\), so \(|\theta-p/m|<1/m^2\). Let \(j/m\) be the closest
grid point **in the phase circle** to \((a+b)/2\), and solve the
single congruence
\[
                     kp\equiv j\pmod m,\qquad 0\le k<m .
\]
No elliptic points corresponding to the other \(m-1\) phases
are evaluated. Since \(\gcd(p,m)=1\), the selected \(k\) is unique
after the chosen nearest-grid tie rule, and
\[
 \operatorname{dist}_{\mathbb R/\mathbb Z}
       \bigl(k\theta,(a+b)/2\bigr)
        < \frac1m+\frac1{2m}<\frac w2.
\]
Thus the one exact point \(A+[2k]D\) lies in the chosen target
arc. Double-and-add uses \(O(\log m)\) group operations once \(k\)
is known. Strict certified enclosures suffice to compute the
continued fraction and choose the phase interval; the irrational
phase never equals a rational decision boundary. The first eligible
denominator \(m\) can be large, and no small uniform bit budget for
exact elliptic coordinates is asserted. An implementation should
stop before a too-large exact group operation.

For clarity, the needed real phase enclosures can be computed
without trusting approximate root solves. In a real model
\(Y^2=f(X)=X^3+A_E X^2+B_E X+C_E\), let \(e\) be its largest
real root. The identity component uses \(X\ge e\) and \(O\).
For \(Y>0\), the phase integral from the origin is
\(\int_X^\infty dx/(2\sqrt{f(x)})\), divided by
\(2\int_e^\infty dx/(2\sqrt{f(x)})\); the lower branch gives
its negative, modulo 1. The substitution \(x=e+s^2\), followed
by \(s=t/(1-t)\), gives the regular positive integrand
\[
 \frac{1}{\sqrt{t^4+(3e+A_E)t^2(1-t)^2+f'(e)(1-t)^4}}
                            \quad(0\le t\le1).
\]
Indeed \(f(e+s^2)=s^2\{f'(e)+(3e+A_E)s^2+s^4\}\),
positive away from \(s=0\), and \(f'(e)>0\).
This compact form has positive denominator also at both endpoints,
so validated root isolation and interval Riemann bounds converge
on any required subintegral. Use the exact ordering and real
branch to enclose the target arc after translating by the rational
offset. This is a deterministic fallback design, not an implemented
phase search in the replay below. It cannot help when (1), or the
more general real-window test, proves the interval empty.

## 3. Bounded prescribed continuation from order 16

Use the exact order-16 rule from the [interval pencil archive](../interval-real-pencil/interval-real-pencil.md).
The root labels \(ja,jb,jc\) append the three new sites in the
rank-free formula order of move \(j\), starting with the four
centered interval-seed moves and the two previous continuations.
Every tested pair was prescribed by the sign-selected adjacent
rule; no candidates on alternate pairs were evaluated.

All following enclosures are scaled by \(10^6\).
The common certificate prime is \(q=2147483647\).

| Target exact order | Pair | Enclosure for \(F(1)-F(0)\) | Root enclosures in rank-free order | First unpaid defect mod \(q\) |
|---:|:---|:---|:---|---:|
| 17 | \(6b,6c\) | \([513229,513230]\) | \([933841,933842], [39389,39390], [415023,415024]\) | 1450210654 |
| 18 | \(7c,7a\) | \([750659,750660]\) | \([400959,400960], [443727,443728], [964226,964227]\) | 844394583 |
| 19 attempt | \(8b,8c\) | \([-1831693,-1831692]\) | not evaluated | not evaluated |

For the two accepted moves the designated pair's smoothness and
\([6]D,[9]D,[12]D\ne O\) all pass as explicit affine residue
calculations. The rank-free triple already lies inside; no
continued-fraction or rational multiple fallback is needed. Both
endpoints survive. Every SLP division is available mod \(q\), the
retained and new roots have distinct residues, the full final
cofactors have nonzero residues, and the displayed first failures
are nonzero. Inductive paid nodal identities give the exact
rational equalities; no rational equality is deduced from a zero
residue. Hence the actual orders are exactly 17 and 18 with
respectively 15 and 16 distinct contributing sites in \([0,1]\).
No weight sign assertion is made.

For the stopped pair both residues are strictly negative, and the
frame has \(F(0)\in[256637,256638]10^{-6}\),
\(F(1)\in[-1575056,-1575055]10^{-6}\). Thus this pair has no
interval window even over \(\mathbb R\); this is a **proved
real failure**, not inconclusive arithmetic or a failure of
just one of its rank-free roots. No group operations or alternate
pairs were attempted after this gate. A different pair on the
verified order-18 rule might still work.

The [checker](verify-continuation.py) reuses the exact seed checker,
288-bit outward dyadic enclosures, and the fixed prime. It
stops at its first nonpassing gate, and the [receipt](exact-check.txt)
is the exact observed prefix. No expanded wide fractions, fixed
grid, background run, or Lean proof was used. There is no claim
of positivity, interval order 19 or 20, minimum support, or
an RK stage endpoint.
