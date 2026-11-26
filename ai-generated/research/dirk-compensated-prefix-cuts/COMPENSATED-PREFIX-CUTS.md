# Nonminimal anchored cuts: effective roots, prefix masks, and exact loss

## Scope

Source-only. No numerical gate, replay, compiler, solver, repository work, or held endpoint was used. This extends dirk_anchored_future_pulse_divided_differences_20261126.md beyond its fully separated anchored-minimal applications. It is a conditional cross-order theorem, not a new stage floor. It distinguishes the measured nullity of a terminal-deleted mask chart, the genuine degree cost of a correction, the rank of leakage on a physical prefix, and the independent question of a diagonal refund.

Use a coefficient field in which the relevant integration denominators are units; for cleared order-\(p\) RKOC over a nonzero commutative ring this follows from the tall-tree equation and reduction to a residue field. Work over a splitting extension if desired. All chronology is the order of literal physical rows, not an order on clock values. Write \(J\) for the formal primitive from zero.

## 1. One unrepresented/repeated root can save one genuine degree

Use the actual mask data of the preceding theorem. Let \(D=TQ\), raw scalar fit \(P=TS\), and raw head coefficient \(kS\). On terminal deletion assume the exact alias \(D(c)=u_D+k w Q(c)\) with true shift-invariant core \(U\). Here \(Q\) is monic of degree \(N\), \(g=\gcd(S,Q)\), and the actual nonterminal quotient support consists of effective clocks \(\mathcal U\) at which \(Q(u)=0\) and \(T(u)S(u)\ne0\). The true mask representation is obtained by dividing \(SM\) by \(Q\): if its remainder is \(R\), the compensated column has genuine scalar profile \(TR\), head coefficient \(-kR\), and its actual quotient at \(u\) depends on \(R(u)=S(u)M(u)\). All remainders \(g\mathbb P_{N-\deg g-1}\) are available, since this is precisely the image of multiplication by \(S\) on \(K[x]/Q\). As before, the genuinely reduced head, scalar and compensation budgets must be supplied by the actual tableau, not inferred from the formal remainder alone.

Let \(\sigma\) be an upper bound on the dimension of the **actual** space of these remainder profiles that vanish numerically after deleting the terminal and taking the core quotient. This is not the total number of stages above an earlier lower bound. Evaluation on the effective clocks has rank \(|\mathcal U|\): the remnant \(g\) is nonzero there and the polynomial evaluation is Vandermonde. Every zero evaluation gives zero quotient on the deletion, so
\[
 d\coloneqq N-\deg g-|\mathcal U|\le \sigma .
\]
The quantity \(d\) counts lost distinct effective slots, including roots repeated in the residual polynomial, roots overlapping the scalar fit, and unrepresented roots. It is not a count of artificially repeated physical pivots.

Write \(Q_{\mathrm{eff}}=\prod_{u\in\mathcal U}(x-u)\). It divides \(Q/g\). Instead of the untrimmed pulse \(Q/(x-u)\), choose the desired remainder \(gQ_{\mathrm{eff}}/(x-u)\). It is in the image ideal, gives the same intended single effective clock support, and saves \(d\) degrees in **both** the scalar and head profiles. The saved degree only turns into a budget improvement if the actual lower head powers and core corrections fit the lower grades. If the previous read required \(r\) degrees of genuine drop and the trimmed pulse actually saves \(d\), then only \(r'=\max(0,r-d)\) further divided differences are needed. For any fixed policy about the actual origin, if \(m_0\) counts the potential nonzero slots with that origin convention, then
\[
 (m_0-d)-r' = m_0-r\quad\text{when }d\le r .
\]
Thus one actual null direction can hide one repeated/overlapping effective slot **without reducing the number of independent future-pulse observations** when it simultaneously saves the one needed grade. Neither side of this trade refunds a physical diagonal.

## 2. Direct prefix remainders are stronger than insisting on single-port pulses

Let \(d_R\) be the genuine remainder degree cap at which the scalar profile, head and core are affordable and the A-discrepancy is exactly read at the comparison detectors. This may be lower than the formal mask cap \(N-1\). Let \(\epsilon=1\) if the actual origin is an effective mismatch, and \(0\) if the offset is already absent there. Put
\[
 B=Tg\,x^\epsilon,\qquad k=d_R-\deg g-\epsilon+1,\qquad
 B=x^e P_0,\quad P_0(0)\ne0,\quad \ell=\deg P_0.
\]
Here \(k\) is the number of polynomial-weight observations at the first **refunded** effective nonzero pivot, not a count of stages or of numerically independent vectors. An anchor absent from the mismatch is not masked automatically. If it is present, the true first row is earlier than all these nonzero pivots.

Let the actual nonzero effective clocks be \(u_1,u_2,\ldots\) in order of first physical mismatch, and write \(M_i=\prod_{j\le i}(x-u_j)\), \(M_0=1\). At the physical comparison pivot \(u_i\), prescribe any remainder
\[
 R=g\,x^\epsilon M_{i-1} H,\qquad \deg H\le k-i .
\]
Every such remainder is in the actual image ideal. At every earlier effective clock it forces the raw mask to vanish, because \(S\) is nonzero there. After the true core correction, all previous physical entries vanish. If the current diagonal is paid, the A-output is zero through the current physical pivot. The actual detector therefore gives
\[
 \left(J[B M_{i-1} H]\right)(u_j)=0\qquad(1\le j\le i)
\]
whenever the other earlier detectors also read the pure discrepancy through this budget. In particular at \(u_i\) these are \(k-i+1\) independent polynomial-weight moments. This is exactly the span obtainable by future divided differences when every effective slot is present and affordable. It remains valid when some slots are missing: the moment count comes from the actual degree cap, not from the number of future single-port vectors. Even if two true profile columns are numerical aliases, each true rooted lift separately gives its exact moment at the genuine detector. This does not claim independent numerical or stage directions.

If an own diagonal is unrefunded, prescribe instead \(R=g x^\epsilon M_i H\) with \(\deg H\le k-i-1\). Now the input vanishes **through** the comparison pivot, so lower triangularity gives the same for its A-output without any diagonal premise. The price is one observation and a new integrand factor \(x-u_i\). The same literal through-prefix argument is supplied by using only strictly later pulses. Thus a one-surplus chart with \(\sigma=1\) may lose no first-two moments at all provided at least two real nonzero detectors survive, their genuine lower read budgets still hold, and whichever own diagonals are used have separately been paid.

### A two-cut exclusion even with neither diagonal refunded

Assume \(k\ge3\), two actual distinct nonzero comparison pivots \(a,b\), and exact reads for the through-prefix masks just stated. At \(a\) there are \(h=k-1\) exact moments of \((x-a)B\). Their \(h\)-fold primitive has origin order at least \(e+h\) and order at least \(h+1\) at \(a\), since the integrand already vanishes there. If \(\ell<h\) this is impossible by degree. If \(\ell=h\), its shape is forced:
\[
 F=J^h[(x-a)B]=\kappa x^{e+h}(x-a)^{h+1},\qquad \kappa\ne0 .
\]
The second, through-prefix comparison gives \(h-1=k-2\) exact moments of \((x-b)(x-a)B\). But
\[
 J^{h-1}[(x-b)(x-a)B]=(x-b)F'-(h-1)F
\]
has value \(-(h-1)F(b)\ne0\) at \(b\). Contradiction. Thus \(\ell\le k-1\) is excluded with two genuinely observed zero-through cuts and no \(\mathcal D\) refund. With both diagonals refunded, the preceding future-pulse theorem excludes \(\ell\le k\) for \(k\ge3\). Forgoing both refunds in this comparison therefore costs one in the selected degree threshold, not two. This is a sufficient loss bound, not a claim of sharpness.

There is a useful mixed variant. If only the first is refunded and \(k\ge4\), there is no loss at the boundary \(\ell=k\). The proof is exact: the \(k\) first moments force \(F=J^k B=\kappa x^{e+k}(x-a)^k\). Put \(n=k-2\); the unrefunded second moment polynomial is
\[
 H=J^n[(x-a)(x-b)B]
   =(x-a)(x-b)F''-n(2x-a-b)F'+n(n+1)F .
\]
If \(H(b)=0\), write \(s=b-a\) and \(L=F'/F\); then \(sL(b)=n+1\). Differentiation gives \(H'(b)=(n-1)(-sF''(b)+nF'(b))\). Also \(sF''(b)/F(b)-nL(b)=L(b)+sL'(b)=(e+k)a/b^2\ne0\). As \(n\ge2\), this contradicts the \(n\) second moments, which require a double zero. If only the second is refunded, the strict first already gives the above \(\ell=k-1\) boundary shape, and the second directly asks the same \(F\) to vanish at \(b\), impossible. No claim is made about the first-refunded-only boundary for \(k=3\).

This explicitly agrees with the corrected marked prefix warning: deleting/repeating a mask factor does not cancel a residual diagonal-square term at the same physical fibre. Choosing an input that truly vanishes through that fibre avoids requiring such a cancellation. It does not prove the diagonal zero.

## 3. Unknown observed leakage: a quantitative prefix-rank bound

Here is the version with nonzero measurable discrepancy, with or without a cheap full core. At a fixed physical comparison prefix ending at \(u_i\), use a family \(B M_{i-1}\mathbb P_{k-i}\) of formal profiles of dimension \(t=k-i+1\). It can come from the direct remainder construction or genuine future differences, where \(k=m-r\). Assume the input lifts have the stated zero-prefix property and the own diagonal is paid. For the strictly-future/no-diagonal version use \(B M_i\mathbb P_{k-i-1}\) and \(t=k-i\).

Suppose selecting the genuinely affordable lifts loses at most \(c_i\) dimensions (for example the actual core projection to the expensive quotient), and on those lifts the map of true A-discrepancy to the \(i\) actual detector readings has rank at most \(\delta_i\). Both are ranks **on this physical prefix**, not ambient estimates. Write \(\Lambda_i=c_i+\delta_i\); when the joint loss is better, use its actual rank. If \(t>\Lambda_i\), at least \(t-\Lambda_i\) independent formal profiles have exact zero primitive values at all \(i\) observed pivots.

Let \(\nu_j=\operatorname{ord}_{u_j}B\), usually zero when all \(u_j\) are effective mismatch clocks. For the own-refunded version these exact primitives have degree at most \(e+\ell+k\) and are divisible by
\[
 x^{e+1}\prod_{j<i}(x-u_j)^{\nu_j+2}\,(x-u_i)^{\nu_i+1}.
\]
Comparing dimensions of the degree-capped divisible subspace gives
\[
 i+\sum_{j\le i}\nu_j\ \le\ \ell+\Lambda_i .
\]
The strictly-future version has one fewer allowed coefficient but one extra derivative zero at \(u_i\), so the bound is the same. Any additional genuine earlier detector at a distinct nonzero clock where every profile has an a priori zero of order \(\mu\) contributes \(\mu+1\) to the left. A second numeric row with the same clock is not such a distinct detector and does not by itself give a derivative observation.

When all relevant prefixes exist and \(\Lambda_i\le\Lambda\), choose \(i=k-\Lambda\) in the own-refunded version, or \(i=k-\Lambda-1\) in the strictly-future version; use only a positive existing \(i\). In the no-overlap case this gives necessary \(k\le\ell+2\Lambda\), or \(k\le\ell+2\Lambda+1\), respectively. With more limited physical detector availability, the displayed bound at the available \(i\) is the actual conclusion. Thus one arbitrary measured leakage/correction rank costs at most two omission slots in the long-prefix criterion, not one stage and not automatically a loss of all taps.

Compare Mark's corrected PAID-HERMITE-EXIT-WITH-PREFIX-LEAKAGE result (one-surplus reverse flags audit): its outgoing transported-covector rank is \(d-\ell_I\), with \(\ell_I\) measured in the actual prefix quotient \(\pi_I W/\pi_I M_j\); the incoming version compares with the full current increment and cannot additionally subtract a clock extension without another containment. The present forward comparison is of profiles of actual input lifts and primitive outputs, not transported incoming covectors. The factor of two in the fallback bound never comes from counting one leakage direction twice in a single comparison: one copy decreases the kernel dimension and the other decreases the latest usable prefix where the future coefficient space can still have a nonzero kernel. If a one-surplus marked character has independently transferred to this actual forward correction channel, one may do better as below; the marked result alone does not prove that transfer.

A verified leading-coefficient leakage functional can be removed simply by lowering the remainder ceiling one degree, costing one tap and no selected factor. A verified finite evaluation leakage at \(\nu\) can be killed by an extra factor \(x-\nu\), provided its actual core consequence was proved. An unmasked nonzero \(\nu\) can cost one degree and add one to the selected nonorigin degree; \(\nu=0\) adds only to the origin order, and an already forced root costs nothing. At \(\nu=a\) in the first literal comparison, the strict through-\(a\) mask already kills that character; this is a route to exact moments, not a diagonal refund. Apply neither statement to an arbitrary one-extra rank without its actual character.

## 4. Repaired leakage can replace the rank loss by its real degree cost

If actual leakage on the observed ports has derivative-compatible representatives, one can keep the **full** affordable formal coefficient family instead of first taking its leakage kernel. A useful sufficient form is the following. For a lifted profile \(f\), let \(L_f^{\rm rep}\) be a linear-in-the-lift polynomial, or a rational function with a fixed denominator \(W\), matching the actual observed primitive discrepancy at the sampled ports. Let
\[
 \Psi_f=W(Jf-L_f^{\rm rep})
\]
be a polynomial of degree at most \(e+\ell+k+\eta\). At nonexceptional earlier ports assume the derivative of the rational representative vanishes to order at least \(\nu_j+1\), \(W\ne0\), and the observed value is correctly matched. At the current nonexceptional paid port the derivative vanishes to order at least \(\nu_i+1\) as well; in the strict comparison the same condition preserves the extra derivative zero there. Require the order at the anchored origin separately. Let \(\rho\) be the aggregate of any verified missing multiplicities in these root counts, rather than presuming a repeated effective clock gives an extra measured jet.

For injectivity, if \(\Psi_f=0\), then \(f=(L_f^{\rm rep})'\) rationally. Any future effective port on which this derivative has order at least \(\nu+1\) forces one zero of the free coefficient polynomial of \(f\), because the prior mask is nonzero there. If there are at least \(t\) such distinct future ports, the polynomial is zero. (More generally, it suffices to prove this injectivity independently.) In a divided-difference window with \(n\) future ports and \(t=n-r\), up to \(r\) exceptional future clocks are harmless to this injection count. The argument does not assume that every exception has a new physical detector. For direct prefix masks with fewer available future ports than this condition, use the unknown-rank kernel instead unless there is a different injection proof.

Now the affordable family has dimension at least \(t-c_i\), rather than \(t-c_i-\delta_i\). The same divisible-space comparison gives
\[
 i+\sum_{j\le i}\nu_j\ \le\ \ell+c_i+\eta+\rho .
\]
Thus a genuinely one-degree repair with all needed jets costs one rather than two slots when an exact core family fits and the latest comparison supplies a nonzero family. The actual degree cost \(\eta\) must be measured relative to the **current trimmed/differenced** family, not an old untrimmed degree. For example the folded \(JD\) representative and the moving \(\chi\)-repair in dirk15_anchored_leakage_repaired_hermite_20261126.md cost one degree in their original full-pulse windows, but can cost more relative to a lowered cap if the same leakage persists. In the moving case the identity \(\chi L'-B_{\mathrm{Jac}}D'=-(q+1)^2D\) shows that \((L-B_{\mathrm{Jac}}D/\chi)'\) is a multiple of \(D\) at clocks regular for \(\chi\). The exceptional repeated root where \(\chi=0\), or a bad origin, must be excluded from the injection count or handled by a literal separate jet calculation. This theorem does not silently repair such a root.

## Consequences and exact boundaries

A genuine one-null anchored chart with two actual nonzero comparison clocks, a true exact remainder cap giving \(k=4\), and a selected nonorigin cubic is excluded even with neither comparison diagonal paid, by §2. The conclusion still holds if one residual root was repeated or overlapped a canceled factor, provided the stated effective clocks and exact cap were actually proved. If instead only a rank-one arbitrary leakage bound is known, §3 is the safe fallback and requires the stated later physical prefix. If the one-extra rank is only a global stage surplus, or if a trimmed head genuinely misses the necessary lower grade, neither result follows without further data. This is a reusable criterion for nonminimal tableaux, not an assertion that any particular unreduced order through twenty realizes those hypotheses.
