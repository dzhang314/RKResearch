# A five-slot terminal obstruction for a sharp-prefix ERK11 branch

Consider a hypothetical ordinary explicit order-eleven method over a
characteristic-zero field, with 17 *physical* rows and output \(b\).
All spaces/actions below are actual numerical rooted spaces through
grade \(j=|t|-1\), with polynomial models in the usual pair space.
Write \(E_j,F_j\) for its actual numerical image and pure subspace,
\(c=A\mathbf1,\ C=\mathrm{diag}(c),\ Y=I-C\).
The established order-eleven floor and strict truncation force
\(b_{17}\ne0\). No ordering is assumed except in the separate sign
count at the end.

**New result.** The six-pure midpoint branch \(\dim F_5=6\) cannot
have a nonendpoint final clock. In its surviving endpoint branch
there is a single-clock pure late \(v\) with \(Av=0\), supported on
at least two physical sites, and an actual charged grade-six late
direction. Removing only the first support coordinate of \(v\) in a
*linear word quotient* gives a five-slot terminal exception with a tied
initial nonendpoint clock, live adjacent edges, and a rational
weight certificate on the literal first eleven stages. That quotient is
not claimed to be a smaller Runge–Kutta tableau.

This excludes a distinct subcase of the sharp-prefix branch. It does
not exclude the endpoint survivor or any general \(F_5=5\) equality
case, including the measured one-spare spike. The ordinary interval
remains 17–18.

## Two exact obstructions on a full literal prefix

Let a strictly explicit prefix have \(E_g=K^k\) on its \(k\)
physical coordinates. This is numerical surjectivity in a specified
grade; no extension to higher grades is assumed. If an actual
row \(r_m\) on that prefix is exact for \(\ell_m\) through size
\(g+2\), its first seed
\[
               (m+1)r_m A-r_mY
\]
kills \(E_g\), so it vanishes as an actual row. If another actual
row \(r_{m+1}\) is exact for the next shift through that same size,
then \(r_m A=r_{m+1}\): both are exact for \(\ell_{m+1}\) on
\(E_g\), where \(A\) extends a tree by one vertex. Consequently
\((m+1)r_{m+1}=r_mY\), making its nonzero support avoid
clock 1. But its own zero first seed implies its last nonzero
physical clock is 1, since \(A\) is strict. Contradiction.
Thus this prefix cannot have *both consecutive shifts* through
size \(g+2\).

If a single row is exact through size \(g+3\), its second seed
\((m+2)r_mYA-r_mY^2\) also vanishes coefficientwise.
The positive clock-weighted row \(r_mY\) is nonzero by its
constant read. At its last physical nonzero coefficient the
\(A\)-term is zero whereas \(r_mY^2\) is nonzero, contradiction.
Thus a full grade-five prefix admits no single Beta row exact
through size eight, and no consecutive Beta pair through size
seven. Both statements are valid over fields paying the relevant
factorials. They use exact chronological support, not a guessed
polynomial model for an arbitrary early row.

## Pure rank six forces a genuine one-clock line

Use the measured cutoff at \(s=17,r=11,g=L=5,k=11\)
from [the two weighted floors](ERK11-AFTER-TWO-WEIGHTED-NINE-FLOORS.md).
Set \(\epsilon=[h_1\ne0]\), \(\eta=[c_{17}=1]\), and
\(H_j=E_j+K e_{17}\) when \(\eta=1\), \(H_j=E_j\) otherwise.
For \(\dim F_5=6\), the rank ledger gives
\(\epsilon+\eta=1,\ \omega=0,\ \dim E_5=12\).
The two actual weighted size-nine floors pay the strict cutoff
guard at both shifts. Therefore the literal first 11 separate
models through grade five and have full \(E_5^{\rm pre}=K^{11}\)
by the paid dense width 11. The map \(E_5\to K^{11}\) has
a one-dimensional kernel \(K v\) and \(v\in F_5\).
The late \(H_5\) space is \(Kv\) plus the endpoint line when
present. We use “late” for zero on rows 1–11.

The cap \(\dim H_6\le \dim H_5+1=13+\eta\) gives
\(\dim H_6^{\rm late}\le2+\eta\). If \(Cv\notin Kv\), it lies
outside \(Kv+K e_{17}\) even when the latter is present:
\(Cv\) and \(v\) are pure through grade six, and \(e_{17}\)
cannot be pure because \(b_{17}\ne0\). In this event the
entire late \(H_6\) space is spanned by \(v,Cv\) and the optional
endpoint line. All positive taps \(bA^a\) on grade-six inputs,
\(1\le a\le4\), kill this space (by purity of \(v,Cv\), and
\(A e_{17}=0\) on the endpoint line). Hence they give genuine
weighted size-seven outputs on the first eleven physical rows.
In particular shifts 1 and 2 would contradict the preceding
full-prefix lemma. So \(Cv=\theta_v v\) and all the physical
support of \(v\) has the same clock.

The identical span argument with \(Av\), also pure, shows
\(Av\in Kv\) (not merely modulo the endpoint); strictness then
forces \(Av=0\). The full-prefix lemma moreover means \(H_6\)
needs a genuinely new charged late direction \(u\), since
if both \(bA,bA^2\) killed its late space they would factor
there and give the forbidden consecutive pair. Thus
\[
           H_6^{\rm late}=Kv+Ku+(\eta\,K e_{17})
\]
with independent summands; \(\eta\,K e_{17}\) is omitted when
\(\eta=0\). A positive read on \(u\) is nonzero.
Writing \(\mu_a=bA^a u\), no consecutive pair
\(\mu_a,\mu_{a+1}\) for \(a=1,2,3\) can both vanish: both
rows would vanish on this entire late space and give consecutive
weighted size-seven outputs on the same prefix. This argument
does not assert a finite-dimensional model projection in
grade six; it uses only the actual factor criterion there.

## A literal five-slot linear quotient and its exceptional clock

Let \(i\) be the first physical support coordinate of \(v\);
normalize \(v_i=1\). It is among rows 12–16 (if \(i=17\),
\(v\) is a multiple of \(e_{17}\), inconsistent with \(b v=0\)).
On the six-dimensional tail, discard just the \(i\)-coordinate
in the quotient by \(Kv\), by choosing \(x-x_i v\) as representative.
\(A\) descends since \(Av=0\), \(Y\) descends diagonally
since \(v\) is a single-clock eigenvector, and \(b\) descends
since \(b v=0\). The induced \(A\) is *strict in the order of
the five remaining physical slots*: for input \(e_j\) with
\(j\ne i\), it is \(A e_j-(A e_j)_i v\).
If the correction is nonzero, \(i>j\) and \(v\) starts at \(i\),
so it cannot affect any coordinate at or before \(j\).
The quotient output has the original coefficient at every
retained slot and is live at 17. All linear words in \(A,Y\)
have exactly the original scalar response on the quotient
class of \(u\). No assertion is made that coordinatewise
products or arbitrary RK tree data descend.

These five slots have the four-word budget for actual grade-six
\(u\) at ordinary order eleven. If the auxiliary \(e_{17}\)
was used to choose \(u\), all positive words kill it, so it
does not change any required positive test. Apply the local
[FourTap](WEIGHTED-ORDER-NINE-FOUR-TAP.md) calculation at shift
\(m=0\), without importing its separate twelve-row stage argument.
It gives \(\mu_4=0\Rightarrow\mu_3=0\), now impossible.
If \(\mu_4\ne0\) but \(\mu_3=0\), the top Krylov basis has
nonzero first subdiagonal clock shifts \(4-i\) and thus distinct
adjacent diagonal clocks \(y_i\), including \(y_0\ne y_1\) and
\(y_3\ne y_4\). The two-clock identity for \(i=0,1\) and
\(j=3,4\) gives \(y_i y_j\mu_2=0\). If \(\mu_2\ne0\), at least
one of \(y_0,y_1\) is nonzero, forcing \(y_3=y_4=0\).
Thus \(\mu_2=0\), also impossible by the consecutive-pair
obstruction. This forces \(\mu_3,\mu_4\ne0\).

The exact local exception now requires final clock 1, so
\(\eta=1,\ \epsilon=0\). Label the surviving five physical
positions \(t_0<t_1<t_2<t_3<t_4=17\). All their adjacent
induced \(A\) edges are live and
\[
 c_{t_0}=c_{t_1}\ne1,\quad c_{t_2}\ne c_{t_1},\quad c_{t_3}\ne1,
 \quad c_{t_4}=1,\qquad  bA=bY.
\]
The quotient top response also forces the last position of
\(bA^a\) to be \(t_{4-a}\) for each \(0\le a\le4\): the
strict five-slot suffix and unique live path give exactly
these last reads in the quotient. In the full array an output
annihilating \(v\) cannot have its last nonzero coordinate at
the omitted pivot \(i\), because \(v_i\ne0\) and \(v\) starts
there. Thus the quoted physical positions hold before taking
the quotient as well. The next tap \(bA^5\) ends by 11.

The five-slot word tests alone cannot exclude this endpoint
pattern, even with the local first seed zero. Exact rational
data have \(Y=\operatorname{diag}(4,4,2,1,0)\),
\(b=(3/32,1/16,1/2,1,1)\), \(u=e_0\), and
\[
 A=\begin{pmatrix}
 0&0&0&0&0\\1&0&0&0&0\\1/2&1&0&0&0\\0&-1/2&1&0&0\\
 1/16&1/4&0&1&0
 \end{pmatrix}.
\]
Here \(bA=bY\); the 31 words of lengths zero through four have
the appropriate ordinary responses with
\((\mu_0,\mu_1,\mu_2,\mu_3,\mu_4)=(3/32,3/8,3/4,1,1)\).
An earlier origin column can pay the specified clock sums.
These are **local** word data, not a full method, and \(u\)
is not asserted to have a rooted-model lift. The unresolved
ordinary branch needs additional rooted structure.

## A paid custom order-eight weight on the sharp prefix

For the endpoint survivor, put \(y=1-c_{t_0}\ne0\).
The exceptional response equations give
\[
           y\mu_1=2\mu_2,\quad y\mu_2=3\mu_3,\quad y\mu_3=4\mu_4 .
\]
So for weights \(Q(Y)\in \operatorname{span}\{Y,Y^2,Y^3,Y^4\}\)
the charge of \(u\) is a nonzero multiple of \(Q(y)\):
the \(Y^a\) response is \(a!\mu_a\).
Unlike a Beta weight, \(w(Y)=Y(Y-y)(2Y-y)\) is zero at \(y\),
and its upper primitive (integrating from zero in the \(Y\)
variable) is \(T w=Y^2(Y-y)^2/2\), also zero at \(y\).
The no-spare cap and live \(Au\) at \(t_1\) give exactly
\(H_7^{\rm late}=\langle v,u,Au,e_{17}\rangle\).
The actual \(w\)-weighted row is the corresponding combination
of \(a!\,bA^a\) for \(a=1,2,3\), hence is exact through size
eight on the full tableau. It kills \(u\) by \(w(y)=0\),
and \(Au\) by \(Tw(y)=0\). It kills \(v,e_{17}\).
By factorization it therefore supplies a genuine **custom**
size-eight output \(\rho\) on the literal first 11 rows,
for \(P\mapsto\int_0^1 w(1-X)P(X)dX\).

On that prefix (with its own actual \(A,Y\)) the paid
polynomial identity \((2Y-y)Tw=Y(Y-y)w/2\) becomes the exact
row equation
\[
        2(\rho A)Y-y\rho A=\tfrac12\,\rho\,Y(Y-y).
\]
Indeed both sides act as the same polynomial weight on every
degree-five rooted input (cost at most two), and \(E_5\) is
the full physical space. Hence the last nonzero clock of
\(\rho\) has reflected label 0 or \(y\); and \(\rho A\) is
zero at both labels by the same equality. This is a
shorter-prefix necessary condition produced by the mixed
root/clock calculation, not a Beta exactness claim.
The single-weight size-eight obstruction above concerns
ordinary Beta weights and does not rule out this custom one.

## Zero coefficients, causal pure-coordinate deletion, and scope

The paid order-eleven **mixed root product** additionally
gives the full moment form
\[
     b(v_1\odot v_2)=\int_0^1 P_{v_1}P_{v_2}
                 \qquad (v_1,v_2\in E_5).
\]
Let \(Z\) be the zero support of \(b\), \(z=|Z|\),
\(f=\dim F_5\), and \(k=\dim(F_5\cap K^Z)\).
The kernel of restriction of \(E_5\) to the live coordinates is
pure by the nonsingular degree-five ordinary Gram. Its image has
dimension \(6+f-k\) and radical of dimension \(f-k\) in the
ambient nondegenerate diagonal form of size \(17-z\).
The annihilator of the image contains the radical, so
\(17-z\ge6+2(f-k)\). In the \(f=6\) branch,
\(2k\ge z+1\) and \(z\ge1\). Over an ordered field the
number of positive weights is at least \(6+f-k\), and of
negative weights at least \(f-k\): the positive projection
is injective on the image (its induced form is positive
semidefinite), and the negative projection is injective on
its totally isotropic radical. No ordered inequality is used
in the rank and terminal conclusions.

A physical pure coordinate has a useful *graded* deletion
test. Suppose \(e_i\in F_d\) and the row-\(i\) evaluation on
\(E_{d-1}\) is a fixed linear read of earlier coordinates.
Let \(S\) be replacement of coordinate \(i\) by that read
(and leave the other coordinates unchanged).
On grades below \(d\), \(S\) is the identity on rooted data.
At higher grades its change is a scalar multiple of \(e_i\),
so it preserves the polynomial model of every formal pair.
The actual padded matrix \(AS\) is still strict and ignores
column \(i\), as does \(bS\). Rooted induction (unary
extension and root product) shows \((AS,bS)\) exact on all
paid trees, since every new numerical profile has its old
exact model in the original graded pair space. Thus the
physical row can be removed, preserving exact order.
This is not an inference from mere output invisibility.

In the \(f=6\) cutoff case the late pure kernel cannot be a
coordinate line. If \(v\propto e_i\), take its first pure grade
\(d\le5\). Through grade \(d-1\) the prefix projection is
injective: its potential extra direction is \(K e_i\),
which cannot occur earlier with a nonzero model because
\(E_5\) separates. Hence row \(i\) has an earlier representative
on this grade, and the deletion test contradicts the old
ordinary floor. In particular if there is exactly one
zero output weight, the mixed Gram makes that coordinate
pure and it must be among the first eleven.

The core Lean file checks the abstract tests for first and
second seed, strict quotient representatives, middle-tap
elimination, root-profile substitution, and local arithmetic.
The actual RK rank/cutoff and rooted space transfers above
are paper deductions. All post-cutoff arguments use only a
field with the relevant paid small factorials and the actual
dense/pure hypotheses. The unconditional implication for the
six-pure 17-row branch here uses the two weighted floors in
characteristic zero. For ring coefficients rank, support and
the weighted assumptions must survive a suitable specialization;
no additional unconditional arbitrary-ring floor is asserted.

### A separate causal detector test, also available in the one-spare branch

In any stage-minimal ordinary order-eleven tableau, a nonzero first
seed \(h_1=bA-bY\) cannot end at a zero output coefficient. If \(i\)
is its actual last support, \(h_1\) gives an earlier representative
for row \(i\) on \(E_9\). Replacing that one coordinate as above
now leaves **every** original rooted numerical profile unchanged
through grade ten: each nontrivial unary step only needs its child
through grade nine, and root products preserve the inductively
unchanged values. If \(b_i=0\), the replacement leaves the output
unchanged as well, ignores the pivot column, and deletes a physical
row. This contradicts stage minimality. The proof does not require
the pivot coordinate to be pure or the prefix to be dense.
For a hypothetical 17-row order-eleven tableau, it gives the
necessary condition \(b_i\ne0\) at the terminal support of every
actual nonzero \(h_1\). This test alone does not discharge the
genuine one-spare rank-spike branch.
