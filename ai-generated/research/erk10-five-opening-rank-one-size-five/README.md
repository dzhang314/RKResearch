# One actual size-five high error direction

**Theorem.** Retain the regular
[five-row opening](../erk10-five-opening-nonsplit-kernel/README.md)
and the output restriction to the old origin and high rows.
Allow arbitrary strict high taps and arbitrary old-contact
coefficients that make the high rows pure through derivative
size four, but allow their **actual** size-five error space
to have rank one. If \(P/X\) is nonsplit over a field with
\(10!\ne0\), order ten requires at least **ten** high physical
rows (at least 15 total). With exactly ten, the raw first
reverse primitive \(K\boldsymbol w=Y\boldsymbol w\) is
forced and hence the last live high clock is \(1\).
This holds with arbitrary clock repeats, high zeros and
physical scores. It does not claim a 14-stage exclusion for
other openings or error rank two. Over \(\mathbb Q\) the same
width-14 exclusion holds **also for split \(P/X\)**, by the
[split evaluation and erasure argument](SPLIT-EVALUATION.md).
The width-ten adjoint assertion here is for the nonsplit
or full-mark rank-two case, not the separate evaluation tilt.

There is a stronger **rational** restriction on the fixed
physical decoder \(L=(EJ-BE)\Pi\) without its high purity
gate: if \((2p-s)v-3qs^2\ne0\), even a genuinely dirty
ten-high continuation is impossible over \(\mathbb Q\).
Its actual size-five model sources recover the entire
previous rational obstruction. The mixed-tilted branch
at ten high is **not** asserted excluded over \(\mathbb Q\).

## Weak plateau assumptions and the rank debit

The earlier [rank-three plateau](../erk10-five-opening-plateau-endpoint/README.md)
does not need all length-five words. It consumes only:
a strictly causal reverse \(K\); mark \(Y\) by \(1-x\);
an increasing flag \(D_j\), with \(K,Y\) taking \(D_j\)
into \(D_{j+1}\); actual seeds \(K\boldsymbol w-Y\boldsymbol w
\in D_1\) and
\(\boldsymbol u=K(Y\boldsymbol w)-Y^2\boldsymbol w/2\in D_2\);
\(D_4\subseteq\ker\mu\) for the positive forward pairing
\(\mu(\boldsymbol f)=\boldsymbol x^T\boldsymbol f\);
\(\mu(Y\boldsymbol w)\ne0\); and \(\dim D_4\le3\).
These imply the first seed vanishes. Neither individual
score nor endpoint sign enters.

The same inputs **without** the grade-one seed and rank cap
already force \(\dim D_4\ge3\). If \(\dim D_4\le2\), an
escape from the silent subspace
\(S=\bigcap_{k\ge0}\ker(\mu Y^k)\) at grade two would cost
three dimensions, so \(D_2\) is silent. Its seed cannot
vanish: the causal masked-primitive argument applied to
the zero invariant space would give \(Y\boldsymbol w=0\).
Thus \(\dim D_2\ge1\). A grade-three escape would add
two nonsilent directions and is also impossible.
Both successive steps \(D_2\to D_3\to D_4\) must then
be strict, by the same pure plateau argument, contradiction.
The [native rank floor](../../lean/RKCert/ReviewedNative/ERK10DirtyPlateauRank.lean)
checks exactly this implication.

In the cases below the original pure tests survive through
word length four. They give the same literal word defects,
\(D_4\subseteq\ker\mu\) and nonzero nominal \(1/6\), and
the shifted Hilbert \(5\) nominal span, independent modulo
\(D_4\). Length-five tests are used only to prove *actual
dual residuals*, not assumed to remain pure. If a space
of rank \(r\) of paired residuals is earned, the exact
dimension ledger is therefore
\[
                         n\ge 5+3+r=8+r
\]
for high physical width \(n\). For \(n=10,r\ge2\) this
saturates the grade-four cap, so the paid first primitive
follows with no additional short word.

## What “one direction” means physically

Use the same \(P=X^3+uX^2+vX\), opening clocks
\(0,e,s,p,q\), and decoder \(\Pi\) as in the
[regular opening](../erk10-five-opening-nonsplit-kernel/README.md).
There are four independent actual opening profiles through
size three: the three quadratic models and the pure
\(\boldsymbol d_o=A_o\boldsymbol c_o-\boldsymbol c_o^{\odot2}/2\),
which has its nonzero pivot at \(e\).
The full physical opening rank through size four is five.
In particular \(A_o\boldsymbol d_o\) is the additional
direction: on \(s,p,q\) it is proportional to
\(\boldsymbol V=(1,\alpha,\beta)\), and the old evaluation
of \(P\) has that same direction modulo the \(e\)-pivot.
Write \(\rho\) for the covector annihilating all size-at-most-three
profiles, normalized by \(\rho(A_o\boldsymbol d_o)=1\).

An arbitrary high-to-old block giving actual high purity
through four is necessarily
\[
                L=(EJ-BE)\Pi+\boldsymbol\eta\,\rho .
\]
Indeed the required unary read on each true size-at-most-three
child fixes \(L\) on exactly their four-dimensional physical
span; the displayed decoder gives those reads. Conversely
those reads and causal induction pay every normalized
derivative through size four. Define
\(\boldsymbol d=(BE-EJ)P\).
At size five the only possibly new error is a unary
above a size-four child. On its actual old input, the
decoder reduces the cubic mod \(P\), and \(\rho\) gives
one contact coefficient. All these errors thus lie in
\(\operatorname{span}(\boldsymbol d,\boldsymbol\eta)\).
Conversely \(A^2\boldsymbol d_o\), interpreted on the
full tableau using the supported quadratic defect, has
high part \(\boldsymbol\eta\). The actual cubic primitive
difference
\(\boldsymbol q_3=A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\)
has high part
\(\boldsymbol d+\rho(E_oX^3)\boldsymbol\eta\).
These are true zero-model combinations through size five.
This proves that the stated one-direction condition is
exactly the rank of these two literal columns, and permits
genuine old-contact changes.

## Two exhaustive early-null alternatives

Consider the actual tree-combination space through size
five with its old profile, high profile and model polynomial.
On the early-null subspace (zero old profile) the model
image is \(U=X\mathcal P_3\) by the regular old rank ledger.
Let \(\boldsymbol\delta\ne0\) span the high error line
and record its coefficient. If a **zero-old, zero-model**
combination has nonzero coefficient, subtract it to make
the high response exactly \(Ef\) for each \(f\in U\).
If none does, the coefficient factors through a linear
functional \(\ell:U\to F\). If this functional is zero,
the pure response again follows. Thus either the whole
original pure-word tests are earned without needing
pointwise size-five purity, or the mixed response is
\[
                    \widetilde E f=Ef+\ell(f)\boldsymbol\delta,
                    \qquad \ell\ne0.
\]
All outer contexts on these actual early-null columns
act by the strict high block or mark. By order ten,
any length-\(\le5\) word on a tilted column has the
prescribed nominal integral, even though it need not
agree on the raw \(Ef\).
In the pure alternative the two original forward
witnesses are available, so the grade-four floor
already gives \(n\ge10\), and the width-ten plateau
applies.


For the **fixed** decoder \(\boldsymbol\eta=0\),
the model-zero columns
\(\boldsymbol d_o,A_o\boldsymbol d_o,C_oA_o\boldsymbol d_o,
A_o^2\boldsymbol d_o\) all have zero high parts, including
the last (the decoder kills \(A_o\boldsymbol d_o\)).
If \((2p-s)v-3qs^2\ne0\), the
[old determinant](../erk10-five-opening-nonsplit-kernel/README.md)
makes them span the four old nonorigin coordinates.
Subtract them directly from the true bushes for \(Ef\).
All pure-word constraints of the
[full rational plateau exclusion](../erk10-five-opening-plateau-endpoint/README.md)
follow, even if \(\boldsymbol d\ne0\).
The endpoint census there uses only the actual short words
once earned; deleting an unscored terminal prefix or
inserting unused unscored clones preserves those words
by strict causality. None of its scalar/physical reverse
exits needs \(BEP=EJP\) separately. This closes the
new generic dirty fixed-decoder stratum over \(\mathbb Q\).
In the mixed fixed-decoder stratum the opening has
\((2p-s)v=3qs^2\); its normalized functional is
\(\ell(f)=-\tau(E_o f)/\tau(\boldsymbol q_{3,o})\), with
\(\tau\) the nonzero old covector annihilating those four
zero-high columns. The replay includes an explicit
rational fixture with genuinely nonzero tilt and
negative discriminant, not a complete method.

## The pure words that survive a genuine mixed tilt

In the mixed case, subtract a formal bush combination
with the same model from any actual combination. Bushes
have no high error. On zero-model combinations the
coefficient of the high error factors through the old
pure space (otherwise a zero-old, zero-model combination
would have carried a removable high direction).
The old pure space is all nonorigin coordinates through
size five, so \(\ell(f)=-\tau(E_o f)\) for a linear
functional \(\tau\) there. It kills
\(\boldsymbol d_o,A_o\boldsymbol d_o,
C_o A_o\boldsymbol d_o\), since their true high parts
are zero even with free old contact. In particular \(\ell\)
is a combination of the three **nonzero distinct** point
evaluations at \(s,p,q\); its coefficient covector kills
\(\boldsymbol V,C_o\boldsymbol V\).
Consequently \(\ell(P)=\ell(XP)=0\).
The true early-null \(P\) is available already at size
four, so its real added unary gives the useful exact
identity
\[
                    \widetilde E(JP)=B EP .
\]
In particular \((BE-EJ)P=\ell(JP)\boldsymbol\delta\)
without requiring \(\ell(JP)\ne0\) in advance.

Write \(Q=\ker\ell\) inside \(U\). The pure size-five
model test subspace is \(Q\). If \(Q+XQ\) is not full in
\(X\mathcal P_4\), a nonzero functional on the latter
annihilates both summands. Its first four consecutive
values are proportional to the four \(\ell(X^i)\),
\(1\le i\le4\), and the next four are also proportional.
Neither proportionality constant can vanish: then the
first or last three \(\ell(X^i)\) vanish, impossible
by the three nonzero-node Vandermonde. The sequence is
geometric with ratio \(z\ne0\); thus \(\ell\) is a
multiple of \(E_z\) on \(U\). The polynomial
\(X(X-s)(X-p)(X-q)\) forces \(z\in\{s,p,q\}\).
The independence of these three evaluations then
forces \(V_z=0\) from \(\tau(\boldsymbol V)=0\).
For nonsplit \(P/X\) all three \(V_z=P(z)/P(s)\)
are nonzero. Accordingly **\(Q+XQ=X\mathcal P_4\)**.
No split assumption is needed if this full span
holds by some other proof.

For every word length \(m\le4\), pure size-five sources
in \(Q\) and \(5-m\) allowed clock marks generate the
full \(X\mathcal P_{8-m}\), first by the preceding
growth and then because further marks of a full
consecutive monomial space extend it by one. Thus all
pure words through length four survive. At length
five the pure sources \(Q\) and the tilted \(U\)
are available, but no full pure length-five claim
is made. This is the exact grade distinction.

## Three actual dual receipts and the surviving rank

Let \(\mathcal A_4\) be the annihilator of the five
nominal columns and all \(D_4\) observers.
Both \(\boldsymbol\delta\) and \(C\boldsymbol\delta\)
belong to it, for the forward diagonal \(C\).
For the first subtract the pure and tilted reads at
any \(f\in U\) with \(\ell(f)\ne0\), using words of
length at most four on both. This gives
\(\boldsymbol w^T W\boldsymbol\delta=0\) for all
these words. For the marked column choose \(f\) of
degree at most three with \(\ell(f)\ne0\), available
by the same nonzero-node Vandermonde. The actual
difference \(C\widetilde E f-\widetilde E(Xf)\)
has zero old and model parts and size at most six;
all length-at-most-four contexts kill it. Subtract
the already proved multiple of \(\boldsymbol\delta\);
this gives the true \(C\boldsymbol\delta\) receipt.
In nominal probes take words of just marks, and for
actual \(D_4\) use the transposed words, so these
pairings really annihilate the combined observer space.

For every \(f\in U\), the tilted forward residual
\[
                 \widetilde T(f)=B\widetilde E f-EJf
\]
belongs to the same annihilator. Its first term is
paid by the true length-five tilted context (apply
one \(B\) followed by a word of length four or less);
its second by the pure length-at-most-four words
(\(\deg Jf\le5\)). This also holds for all nominal
probes, using marks for their polynomials. Ordinary
polynomial integration by parts matches their nominal
values. No unproved relation on \(B\boldsymbol\delta\)
is being charged separately.

Set
\(r=\dim\langle\boldsymbol\delta,C\boldsymbol\delta,
\widetilde T(U)\rangle\).
The previous ledger gives \(n\ge8+r\). In particular
three independent receipts are impossible at width ten,
and two force the raw paid endpoint. If the physical
dirt visits at least two different clock labels,
\(\boldsymbol\delta,C\boldsymbol\delta\) are already
independent. At width ten their span then contains
**every** \(\widetilde T(f)\), since the combined
nominal and defect observer dimension is exactly eight.
In particular every clean high row there must act
literally as \(J\) on the tilted inputs. This is a
physical equality, not a pooled mean.

## Rank one is impossible in the nonsplit chart

Assume \(r=1\). Then \(\boldsymbol\delta\) is supported
at one clock (it is an eigenvector of \(C\)); all
\(\widetilde T\) values at clean coordinates are zero.
Let \(h,z\) be the first and second distinct nonzero
forward clocks. They exist by shifted Hilbert support.

If dirt is supported at clock zero, every prior
high input when \(h\) debuts is a multiple of
\(\ell\). Exactness at its clean row forces
\(J_h\) proportional to \(\ell\). When \(z\) debuts,
the earlier inputs span at most \(E_h,J_h\), so
\(J_z\) must belong to that span. This is impossible:
\[
 f(X)=X(X-h)(X-h/2),\quad
 E_h f=J_h f=0,\qquad
 J_z f=z^2(z-h)^2/4\ne0.
\]
If dirt is at a nonzero clock other than \(h\), the
first \(h\) row has only zero clean predecessor inputs,
so it cannot be exact. Thus the dirty clock is \(h\),
and its first physical row is dirty since its residual
is \(-J_h\). Call its error coordinate \(\delta_1\ne0\).
All zero-clock rows are clean and give zero tilted
input. Evaluating the rank-one proportionality at
this first \(h\) row gives the identity on every row
\[
       \widetilde T(f)=-\,J_h(f)\boldsymbol\delta/\delta_1 .
\]

Before the first distinct \(z\), suppose an \(h\)-copy
is the earliest whose \(\delta_i\ne\delta_1\), including
a possible clean copy. All its old \(h\)-inputs are
identical to the first \(E_h+\delta_1\ell\).
But by the rank-one equation its read equals
\((1-\delta_i/\delta_1)J_h\ne0\) as a functional.
Therefore \(\ell\) belongs to \(\langle E_h,J_h\rangle\);
the first \(z\) is clean and the same cubic \(f\)
gives the same contradiction. It follows that every
\(h\) copy before \(z\) has identical tilted input.

At the first \(h\) row the physical input \(BEP\)
vanishes, because \(P(0)=0\) and all predecessors
have zero clock. Hence the common tilted donor
\(E_h+\delta_1\ell\) annihilates \(JP\).
At the clean \(z\), its exact read on \(P,XP,JP\)
thus gives
\[
 J_z(XP)=h J_z P,\qquad J_z(JP)=0 .
\]
The polynomial identity \(J(XP)=XJP-J(JP)\)
then yields \((z-h)J_z P=0\), so \(J_zP=0\).
Since \(P(h)\ne0\) (as \(P/X\) is nonsplit),
this makes the sole effective scalar tap into the
common donor zero. Then \(J_z\) is the zero functional,
contradicted already by \(J_z(X)=z^2/2\).
This obstruction covers arbitrary placements and
weights and multiple dirty copies. It only needs
\(P(h)\ne0\) at this final step, so can be used
conditionally in a split case too.

If instead \(P(h)=0\), the same proof still reaches
identical donor inputs before \(z\). Exactness on \(P,JP\)
then gives \(JP(z)=J^2P(z)=0\) directly. Their two
scalar primitive equations with \(z\ne0\) give
\[
                  u=-6z/5,\qquad v=3z^2/10 .
\]
Substitution into \(P(h)=0\) gives
\((10h-6z)^2=6z^2\).
Thus the remaining rank-one geometry is also impossible
over any paid field without a square root of \(6\), in
particular over \(\mathbb Q\), even if \(P/X\) splits.
The only exception left by this marked-word ingress is
a true single-evaluation tilt, where \(Q+XQ\) was not full.
The [separate erasure argument](SPLIT-EVALUATION.md) closes
that distinct case at width 14 over the rationals.

Thus mixed nonsplit continuations have \(r\ge2\),
and hence need at least ten high rows. This closes
the stated relaxed real and rational **14-stage**
architecture and forces the physical endpoint at
width fifteen. A genuinely mixed width-fifteen
rational tableau with saturated dual rank remains
an open construction question.

## A further first-dirt score test at the width-fifteen frontier

Choose any actual zero-model combination through size
five with high response \(\boldsymbol\delta\), rescaling
if necessary; its old response need not vanish. Multiplying
two such normalized profiles at the same root is an actual
linear combination through size nine, with zero nominal
model. One extra clock mark is still paid by order ten.
Since the old origin's coordinate of every zero-model
combination is zero, and all other old scores vanish,
these two tests give
\[
 \boldsymbol w^T\boldsymbol\delta^{\odot2}=
 \boldsymbol w^T C\boldsymbol\delta^{\odot2}=0.
\]
Combined with the linear receipts, if dirt occupies exactly
two distinct clocks, the linear and square-weighted dirt
masses vanish separately at each of those clocks by the
two-site Vandermonde. A single dirty component there is
unscored. Two components with distinct nonzero dirt values
there also have both physical scores zero (invert the two
columns \(\delta_i,\delta_i^2\)). This does not delete
their actual outgoing taps. In an ordered field with
nonnegative scores, the first square test alone forces
every dirty row unscored, without any support guard.

For example over \(\mathbb Q\) at high width ten, if dirt
occupies just two distinct visible interior singleton labels,
the paid endpoint and the anchored degree-nine scalar floor
require at least nine visible high labels: both dirty
singleton scores vanish, and their removable scalar sites
are neither endpoint. This is a conditional remaining
chart restriction, not a tableau certificate.

## Reproduce and scope

    python3 -B audit.py
    sha256sum -c ai-generated/research/erk10-five-opening-rank-one-size-five/sources.sha256

The replay checks actual rooted stage profiles for all 17
tree shapes through size five on both a generic control
and an exceptional rational fixture, plus the symbolically
cleared scalar identities of the rank-one exit.
See [Lean scope](LEAN.md). The old-contact and actual
rooted-word adapters here are mathematical. No unrestricted
lower or upper stage endpoint has changed.
