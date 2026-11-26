# What the chronological Gram exit buys at the next ordinary plateau

Use degree \(j=|t|-1\), so the size-six surplus is \(\dim F_5\ge5\). For the ordinary or actual weighted Beta setting, assume the paid model ranks on the separated portion. In particular ordinary order at least 14 separates degree seven, and order at least 16 separates degree eight. The same thresholds apply to the retained tree size of a Beta-exact prefix. The previous verified size-six surplus at those high orders already supplies \(\dim F_5\ge5\); any conditional extension of that input to shorter weighted prefixes does not introduce an extra midpoint copy of it here.

We use two existing pure-rank rents from the paid logarithmic proof:
(1) if \(U\subseteq F_j\) is clock-invariant and degree \(j\) separated, then \(\dim F_{j+1}\ge\dim U+\lfloor(j+1)/2\rfloor\);
(2) if all \(F_j\) itself is clock-invariant at separated \(j\ge5\), then \(\dim F_j\ge\lceil3j/2\rceil-3\). The first comes from the early Hermite reads in the clock-supported coordinate compression. The second uses the chronological order-\(j\) endpoint providers at the \(j\) distinct nonzero clock labels and the usual ordinary order-\(j\) floor. These rents are paid over the same fields; their proofs use no ordered step.

## A forced small core through degree seven

Assume \(\dim F_7\le7\). Then \(F_5,F_6,F_7\) have dimensions \(5,6,7\) by strict pure growth. The first two flags are noninvariant by rent (1), and the endpoint by (2). The actual one-head interval thus has base \(a=5\), length two, and invariant core \(U\) of dimension at most three (rent (1) on \(F_5\)). Apply the general Gram exit to the second-order defect \(\mathbf q\), with cost \(e=2\). We obtain:
[
      \mathbf q\in U,qquad D_{\mathbf q}U\subseteq U,
      \qquad \mathbf q=0\text{ on the complementary head support}.
]
By projecting \(\mathbf q\) onto the joint clock/q-value blocks and dividing its nonzero value, \(U\) contains the indicator of each such nonzero type. Distinct clock labels with the same q count separately, as do different nonzero q-values at the same clock. Therefore there are at most three genuine carrier types. Four or more force \(\dim F_7\ge8\), with no numerical chronology assumptions on where the carriers occur.

There are two further automatic exits when \(\dim F_4=3\). In either, \(\dim F_3=2\), and \(F_3\) is noninvariant by rent (1), so \(F_4=F_3+CF_3\).

* If \(F_4\) is already clock-invariant, it equals \(U\), by maximality of the core and its dimension cap. For any \(f\in F_3\), multiplication by \(f\) maps \(U=F_4\) into \(F_7\); on a single-clock piece the head-root argument then puts the product in \(U\). Thus each such multiplier preserves \(U\). Applying zero-constant polynomials to a basis of \(F_3\) creates the support indicator of each basis vector in \(U\); those same diagonals preserve \(U\) as polynomials in the paid multipliers. Taking unions by \(1_{S\cup T}=1_S+1_T-1_S1_T\) gives the indicator of the whole support of \(F_3\), which equals the support of \(F_4\).
* If there are exactly three nonzero joint q-types, \(U\) is their indicator span, supported entirely on the carriers. The head can be chosen zero on those carriers by the paid \(\mathbf q\) exit. If \(f\in F_3\) were outside \(U\), its nonzero head projection is a constant times \(w\): here the head width of \(F_5\) is two, and \(Cf\in F_4\subset F_5\) forbids a nonconstant linear head coefficient by clock interpolation on the effective labels. The vector \(f\) is constant on each of the three core types, so multiplication by it preserves \(U\). Write \(f=\alpha w+u\), with \(\alpha\ne0,u\in U\). Then \(D_f w=(f^2-D_f u)/\alpha\) is in \(F_6\), and its actual head profile polynomial has degree at most two (head width three at \(F_6\)). In the chronological contrast with \(Q=X\), the rooted cost of \(f\) is three. Degree seven therefore pays all \(R\) of degree at most two at the same exit; the shifted Gram kills its nonzero quadratic profile. Thus \(F_3\subseteq U\), so \(F_4=U\) and its support indicator is available directly.

In both exits let \(S\) be the core support. There are at most three distinct live core clocks because \(\mathbf1_S,C\mathbf1_S,\ldots\) lie in its rank-three space. On every stage off that support, \(F_4\) vanishes, yielding exact primitive moments through degree three. Its actual incoming functional on \(U\) annihilates \(F_3\), since \(A F_3\subset F_4=U\) has zero off-core value. Such core feeds thus lie on a fixed line. Their first nonzero off-core clock \(\theta\) identifies the shared primitive line, and the two tests \(X(X-\theta),X^2(X-\theta)\) rule out every new nonzero off-core clock by \(3(y/\theta-1)^2=0\). There are at most five actual clocks in total, incompatible with separated degree five. This completes the two extra measured exclusions.

Feeding \(F_7\ge8\) into the actual ordinary midpoint gives a paid **order-15 floor of 23 in these branches** (currently unconditional 22 over arbitrary rings and unordered characteristic-zero fields; ordered fields already have 23). At order 14 it reaches 21, already the unconditional paid floor. No condition-free table change is claimed. The nonzero joint-type premise transfers to a ring only when it survives a specialization. The stated implication about field ranks and invariance is not automatically a condition on a ring module rank.

## Degree eight: only a quartic over a rank-three core remains

Assume \(\dim F_8\le8\). The genuine 5-to-8 flag has increments one and is noninvariant even at the endpoint, by the same rents. The chronological Gram exit with \(e=3\) gives \(F_3\subseteq U\) in **every paid field**, not only an ordered field. This strengthens the earlier cubic-square positivity argument, without changing its native source or exercising a held endpoint.

If \(\dim F_4=3\), the same reasoning gives \(F_4=F_3+CF_3=U\), and \(D_f\) stability for \(f\in F_3\) produces its support indicator. The preceding rank-one core argument excludes it over every paid field.

Otherwise \(\dim F_4=4\) and the 4-to-8 interval is also genuinely flat. The invariant core is the same U: the head only grows by appending the next single clock power until the endpoint, where it is still not exhausted. If \(\dim U\le2\), put \(k=4-\dim U\ge2\), and choose an actual head generator \(f\in F_4\). Apply the block and multiplier argument jointly with the actual multipliers \(f,C^{k-1}f\), both in \(F_4\). Their raw head profiles have degree at most four, and on the common head support the second is \(X^{k-1}\) times the first. There are at least \(k+5\) effective labels, more than both polynomial degrees in this comparison. Thus the first nonzero profile \(P\) has \(\deg P\le4-(k-1)\le3\).

The chronological exit with \(Q=X\) pays all \(R\) of degree at most two, since the rooted cost of \(f\) is four. If \(\deg P\le2\), this already contradicts the paid Gram. Otherwise dilate its first nonzero exit \(u\) to 1. The three moments show \(XP\) proportional to \(H'''\), where
\[
                         H(X)\coloneqq X^4(X-1)^3.
\]
Indeed its first three ordinary moments vanish by integration by parts, it is divisible by X, and the paid shifted three-by-three Gram gives uniqueness. A second contrast with \(Q=X(X-1)\) gives an actual exit \(a'\ne0,1\), with both \(\deg R\le1\) moment tests. This says the functional \(V\mapsto I_{a'}(V H''')\) on polynomials of degree at most two kills those with \(V(1)=0\). It is therefore \(\lambda V(1)\). Test \(V=(X-a')^j\), \(j=0,1,2\), and integrate by parts. The boundary values are \((-1)^j j!H^{(2-j)}(a')=\lambda(1-a')^j\), so
\[
             H\equiv\lambda(X-1)^2/2\pmod{(X-a')^3}.
\]
Dividing by the unit \((X-1)^2\) in that local polynomial quotient makes \(X^4(X-1)\) constant to second order at \(a'\). Its first derivative is \(X^3(5X-4)\), which has only a simple nonzero root, so its first and second derivatives cannot both vanish there. This is a fully paid cubic two-exit contradiction.

Consequently at degree eight the only remaining general paid branch consists of a rank-three invariant core and a single quartic head at degree four. The elementary chronological Gram does not supply its missing fourth moment, and no exceptional-prime or held order-specific closure is invoked. Before that remaining branch is resolved, no unconditional ordinary floor is raised here. The reduction is a source-only strengthening, not a new Lean receipt.
