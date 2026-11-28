# The adjacent invisible ghosts: terminal weight and cyclic-room exits

Work over any characteristic-zero field in the
[two invisible distinct-defect-clock normal form](ERK10-TWO-INVISIBLE-DISTINCT-DEFECT-CLOCKS.md).
The hypothetical strict explicit 14-stage order-ten tableau has
exactly two zero output weights, at physical 2 and 3. Its original
quadratic defect \(d\) is supported on those two sites, has nonzero
values there, and their clocks are distinct. Thus
\(F_3=G=\langle e_2,e_3\rangle\) and
\(A_{i3}=\kappa A_{i2}\) at every live row, with
\(\kappa=-d_2/d_3\).
The conclusions \(A_{32}\ne0\), \(b_{14}=1/30\) below apply
to the whole adjacent chart. The later deductions concern
a specified cyclic rank-two branch; they do not exclude the
remaining adjacent chart or change the unconditional stage interval.

## 1. Actual stage-3 tap and actual fifth-grade terminal value

Write \(\theta=c_2\ne0\), \(\eta=c_3\ne\theta\),
\(\Gamma_j=\theta^j+\kappa\eta^j\) for \(j\ge1\), and
\(r_i=A_{i2}\) on the live set, extended by zero at both ghosts.
At the actual first nonorigin live stage 4,
\[
             2 r_4\Gamma_1=c_4^2,\qquad
             3 r_4\Gamma_2=c_4^3,\qquad c_4\ne0 .
\]
Since \(d_3=\theta A_{32}-\eta^2/2\) and \(2\kappa d_3=\theta^2\),
\[
                    \Gamma_2=\theta^3 A_{32}/d_3 .
\]
The second actual row equation makes \(\Gamma_2\ne0\);
therefore **\(A_{32}\ne0\)**, without needing \(\eta\ne0\).

The old \(F_3=G\) is clock-invariant. The genuine grade-three
outgoing Hermite rank and \(f_5=5\) force \(f_4=4\).
On the live set \(F_4\) projects down to
\[
 W=\langle r,z\rangle,\qquad z_i=(A c^3-c^4/4)_i.
\]
Indeed the only new unary pure directions through degree four
are advances of the true \(F_3\) and the quartic polynomial
primitive error; products of two quadratic pure factors and
old clock multiples of \(F_3\) remain ghost-supported.
The live advances of both ghost axes are proportional to \(r\).
This proves the displayed span, whose rank is exactly two.

The old \(F_4\) cannot itself be invariant under the clock
operator, since its genuine outgoing gain would then force
\(f_5\ge6\). Accordingly \(F_5=F_4+C F_4\); all these old
pure vectors vanish at physical 14 by its paid grade-four
point exactness and preserved terminal zero under \(C\).
For the actual \(e_{14}\in E_5\), its exact grade-five model
from [the equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md)
is \(30 b_{14}H\), where
\[
 H(X)=X L_4(X),\qquad L_4(X)=42X^4-84X^3+56X^2-14X+1.
\]
Its terminal value is the literal value 1 since the pure
part is now zero there. As \(H(1)=1\), this gives
**\(b_{14}=1/30\)** and genuine original point exactness
through grade five at the terminal. No new reverse exactness
is inferred from that weight.

## 2. The fixed cyclic projection and actual terminal relation

The one-dimensional subspace
\(\{v\in W:Cv\in W\}\) is exact: \(W\) has rank two and
\(W+CW\) rank three. Its generator is either a clock
eigenvector, or a vector \(p\) with \(p,Cp\) independent.
This note treats the second, **cyclic** branch, so
\(W=\langle p,Cp\rangle\).
Both are genuine separate old grade-four pure lifts; subtract
the ghost coordinates with \(G\) to make each zero there.
They vanish at both old endpoints.
Moreover
\[
                  F_5=G+p\,\mathcal P_{\le2}(c)
\]
as actual pure vectors. The active clock count of \(p\)
is at least four: two would make \(F_4\) invariant,
and three would make \(F_5\) invariant and imply \(f_6\ge8\).
The representability of the actual terminal indicator is
\[
                    e_{14}=H(c)-Q(c)p-H(\theta)e_2-H(\eta)e_3,
                    \qquad \deg Q\le2.                       \tag{1}
\]
In particular \(H(c_i)=Q(c_i)p_i\) at **every** nonterminal
live row, and every \(p\)-dormant nonterminal live clock
is a root of \(H\). This is a statement about actual
numeric stages, not a reconstructed tableau.

## 3. The identically zero \(Q\) is impossible

In this case all eleven nonterminal live clocks belong to the
five roots of \(H\), and together with the terminal they have
exactly six distinct ordinary effective labels by the anchored
ordinary support floor. They form the six-site Lobatto rule.
Every pooled \(bp\) mass is zero by its first six clock moments.
Each active label requires at least two active rows.
The four grouped \(bp^2\) moments through degree three are
paid: \(p,Cp\) both have true grade-four lifts, so their squares
and their single clock multiples cost at most nine.
If at most four active labels occur, all square pools vanish.
Then each two-row group cancels ordinary mass and a larger
group saves at least two physical rows; with at least four
labels this leaves at most four ordinary support sites.

Thus there are five active pairs, exhausting all ten
non-endpoint live rows, one pair at each root of \(H\).
The five square pools, with four zero moments, are either
all zero or all nonzero. If all zero, each pair cancels
ordinary, impossible. Hence each pair has two **distinct**
nonzero amplitudes, and each pair's \(bp\) mass cancels.

Let \(I\) be the twelve live rows. The old \(V_j=E_{8-j}^\perp\)
for \(j=1,2,3\) are fully live because the two ghost indicators
are already in \(E_3\). The origin clock block now has three
physical rows: the old origin and the two active rows at 0.
Let \(q_0\) be any nonzero row on just that triple annihilating
its \(1,p\) columns. At this block those columns are independent.
Since the old \(E_5|_I\) consists of clock polynomials plus
\(p\,\mathcal P_{\le2}(c)\), this really gives \(q_0\in V_3\).
Then
\[
                  V_3=\langle bp,bCp,q_0\rangle.
\]
The first two rows are paid from \(F_4\); independence follows
by looking on the other four distinct active labels.
In contrast \(bC^2p\notin V_3\): evaluating it on the actual
\(C^2p\in F_5\) gives the degree-four moment of the grouped
square masses, which is nonzero (otherwise all five moments
would vanish). This is an exact numerical separation, not a
claimed paid degree-ten moment. As \(q_0 C=0\) and
\(V_2 C\subset V_3\), the clock filtration now forces
\(V_2=\langle bp,q_0\rangle\) by rank. Likewise
\(V_1C\subset V_2\) forces \(V_1=Kq_0\).

For clarity use the genuine restricted weighted transpose
\(A^\vee=B_I^{-1}A_{II}^{\mathsf T}B_I\) in reverse physical
order, and reflected clock \(Y=1-C\). It has this clock
by the literal \(bA=bY\).
Its true quadratic seed \(u=A^\vee Y-Y^2/2\) is the
scaled \(V_1\) row divided by live weights, so it is
supported at old clock zero. The actual reduced cubic
pure room is \(W_2=B_I^{-1}V_2=\langle u,p\rangle\):
the linear moves \(A^\vee,Y\) are true by duality, and the
cubic polynomial primitive defect is in that room by
formal integration by parts against old \(E_6\).
Similarly the quartic primitive error and the linear moves
from \(W_2\) belong to \(W_3=B_I^{-1}V_3\) by tests
against \(E_5\). The only possible additional pure product
through grade four is \(u^2\). These statements use only
the actual linear and product recursions through four,
never ordinary reverse order ten.

The first reversed nonorigin stage is physical 13, with
\(Y_{13}\ne0\) by the sharp shift-one prefix. Its genuine
\(u_{13}=-Y_{13}^2/2\ne0\) forces \(c_{13}=0\) and
\(u_{13}=-1/2\). Write \(j<13\) for the other \(p\)-active
zero-clock row (not the physical origin 1).
The two identities \(b_jp_j+b_{13}p_{13}=0\) and
\(b_j u_j p_j+b_{13}u_{13}p_{13}=0\) give
\(u_j=u_{13}\); the latter is \(q_0p=0\).
The paid reverse rank growth \(V_2=V_1+V_1 A+V_1Y\)
and \(V_1Y=V_1\) show \(A^\vee u\) is independent of \(u\).
Since it vanishes at the first reverse carrier 13, it is
a nonzero multiple of \(p-(p_{13}/u_{13})u\).

Here is the literal reverse head contradiction, written in
local reversed stage order. In the first five reverse rows
old origin 1 is absent. On this head \(s=-2u\) is the
indicator of the first carrier 13 and possibly the other
carrier \(j\). Set \(R_*=A^\vee s\).
It is proportional to \(p-(p_{13}/u_{13})u\); in particular
it is zero at the first carrier, nonzero at the second,
and on noncarriers is proportional to \(p\).
The cubic pure room is \(\langle s,R_*\rangle\);
the quartic room **on the head** is contained in
\(\langle s,R_*,Y R_*\rangle\), since \(u^2\) is proportional
to \(u\) on these first five physical rows.
If \(j=12\), the first two carrier clocks are 1 with equal
quadratic defect; the second's only nonorigin tap is then
zero by the quadratic condition, so \(R_*=0\) there,
contradiction. If \(j=11\), the fourth reversed row is a
carrier at clock 1 after the first noncarrier of clock \(t\).
Its two nonorigin taps \(a,b\) satisfy
\(a+t b=0,\ 2t a+3t^2b=0\) by the actual quadratic and
cubic tests. They vanish, again contradicting its nonzero
response.

If \(j\le10\), the first two noncarriers (physical 12,11)
have distinct nonzero reflected clocks \(t,p_0\).
Indeed following the first carrier, the literal cubic and
quadratic equations at equal \(t\) would duplicate the actual
incoming lists and their \(R_*\) amplitudes; the true pair
has distinct \(p\)-amplitudes. No live nonorigin reverse
clock is zero since old \(c=1\) occurs only at the terminal.
At the fourth reverse row the actual coefficients are
\[
 (R_*)_4=p_0^2(3t-2p_0)/(2t),\qquad
 a_{43}=p_0^2(p_0-t)/t^2,\qquad
 A^\vee R_*=\gamma(Y-t)R_*\ \text{on the head},\
 \gamma=t/(3t-2p_0).
\]
These use only the shared three-direction quartic profile
on the first five rows; every noncarrier response is nonzero.
The old
[fifth-head calculation](ERK10-ZERO-INJECTIVE-INTERNAL-EXCLUSION.md#3-genuine-fifth-contact-and-use-of-the-pure-ghost-direction)
uses precisely that local span. Explicitly at fifth clock
\(w\) the true quartic \(X^2(X-w)(2X-3t)\) gives
\(6a_{54}p_0(p_0-t)(p_0-w)=0\).
If \(a_{54}=0\), the local quadratic/cubic and \(A^\vee R_*\)
equations force a literal repeat of an earlier row; this is
impossible here from the unequal true \(p\)-amplitudes in
every noncarrier pair and the unequal response in the two
carrier positions. Hence \(a_{54}\ne0\) and \(w=p_0\).
A fifth carrier is then impossible since \(p_0\ne1\).
In the noncarrier repeat the exact difference equations give
\(p_0=2t\), as in the
[paid doubling calculation](ERK10DoubledEntranceGate.lean).
Both reflected \(t,p_0\) are interior \(L_4\) roots
(\(L_4(1-X)=L_4(X)\)).
The [exact Lobatto doubling norm](ERK10InvisibleReversePooledGate.lean)
with constant 59 excludes this. All possibilities for \(j\)
contradict, so \(Q\equiv0\) is impossible.

## 4. Paid residual system for nonzero \(Q\)

If the pooled \(bp\) row is zero, every active clock off the
roots of \(Q\) has uniform amplitude by (1), hence both its
ordinary and square pools vanish. Only the at most two
exceptional roots of \(Q\) could contribute to pooled \(bp^2\);
the four square moments kill those too.
Every active pair then cancels ordinary, and higher groups
save at least two rows each. Since there are at least four
active labels, the ordinary support capacity is at most four.
Thus pooled \(bp\) is **nonzero** for every surviving nonzero \(Q\).

If \(Q\) has degree two, (1) paired with \(c^4\) gives
\(b C^4 Q(c)p=0\) by the exact model of \(e_{14}\).
In detail \(b C^4 e_{14}=b_{14}\), and the model integral
\(\int X^4 H=b_{14}\), both paid at grade nine; subtract.
As the degree-four and degree-five \(bp\) moments were
already zero, the top coefficient gives the **additional**
degree-six zero moment. This is an actual extra paid scalar
condition, not an equality of formal tracks.

Let \(D\) be the monic product of the \(q\) active clock
factors. Write \(\nu=(bp)_{\rm pooled}=P/D'\) and
\(\mu=(bp^2)_{\rm pooled}=M/D'\).
The elementary Lagrange moment bounds yield
\[
 \deg M\le q-5,\quad
 \deg P\le
 \begin{cases}q-8,&\deg Q=2,\\q-7,&\deg Q\le1.\end{cases}
\]
On active labels (1) gives \(Q\mu=H\nu\), hence the true
polynomial identity
\[
                                  Q M=H P.                    \tag{2}
\]
Both sides have degree below \(q\), so no nonzero pooled
mass at a particular label had to be assumed for (2).
The exact support range is \(8\le q\le10\); if \(d=\deg Q\le1\)
then (2) sharpens it to \(q\ge10-d\) and
\(\deg P\le q+d-10\).
If \(q=8\), \(Q\) is genuinely quadratic and \(Q\mid H\).
If \(q=9\) and \(Q\) is quadratic, it has at least one factor
in common with \(H\), since \(Q/\gcd(Q,H)\mid P\) and
\(\deg P\le1\).
For constant \(Q\), \(q=10\) and \(P\) is constant.
For linear \(Q,q=9\) one has \(Q\mid H\) and \(P\) constant.
These are all exact algebraic conditions, not solutions.

Finally if \(q=8\) and every active amplitude agrees with a
literal cubic polynomial \(R=H/Q\), the whole branch closes
by the [terminal-anchored cubic support proof](ERK10-TWO-INVISIBLE-DISTINCT-DEFECT-CLOCKS.md#3-scalar-support-the-terminal-indicator-and-the-nonzero-origin-exit).
The only grade adjustment is that here \(p\) costs four:
the compensated mask \(T=R(c)-p-\sum R(c_g)e_g\)
has \(CT,(1-C)T,(C-w)T\) each still of grade four, because
\(p,Cp\) are independently earned grade-four lifts. Therefore
both the old one-middle and the zero-origin two-middle paid
products transfer literally at \(4+1+4=9\).
This excludes all eight singletons (including any singleton at
a root of \(Q\)), and all eight-label cases whose only repetitions
are uniform or away from the roots of \(Q\).
Indeed \(P\) is nonzero constant at \(q=8\), and (2) gives
\(\mu/\nu=R\) at every label; a uniform label therefore has
the literal \(R\)-amplitude. The remaining eight-label case
needs a nonuniform active repetition at a root of \(Q\).
The higher-label rational/repeated profiles and the eigenline
fork of §2 remain open in this packet.

[ERK10AdjacentInvisibleKrylovGate.lean](../lean/RKCert/ReviewedNative/ERK10AdjacentInvisibleKrylovGate.lean)
checks the tap identity, exact clock filtration into two and
one dimensions, equal reverse carrier amplitudes, and the extra
top moment. Exact Lobatto certificates and local contact
arithmetic are the separately checked linked modules.
The actual grading, ranks and physical cuts are the proof above.
