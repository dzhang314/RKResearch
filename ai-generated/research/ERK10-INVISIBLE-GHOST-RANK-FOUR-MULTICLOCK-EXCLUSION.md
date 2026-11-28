# Rank-four at a sole invisible ghost forces at most two reverse defect clocks

Work over an arbitrary characteristic-zero field with a genuine
14-stage strict explicit order-ten tableau. As in the
[single invisible ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md),
there is exactly one zero output weight and all actual original
quadratic defects are invisible. The ghost is physical 2, its
indicator \(e=e_2\) is genuine pure grade two, and \(r=Ae\)
is pure grade three. On the thirteen live rows let \(A^\vee\)
be the actual reduced weighted transpose in reversed chronology
and \(u\) its actual quadratic defect.
Assume the **original** pure rank \(f_4=\dim F_4=4\).

**Result.** The true reverse defect \(u\) is nonzero at at most
two distinct numerical clocks. Both zero and nonzero pooled
\(bu\) are covered. This note does not exclude one- or two-clock
\(u\), original \(f_4=3\), multiple ghosts, or visible original
defects. It does not change the unrestricted 14–15 stage interval.

## 1. Genuine low dual rooms and the old endpoints

Use the paid \(W_1,W_2,W_3\) of ranks \(1,2,3\), obtained by
dividing the live entries of \(E_7^\perp,E_6^\perp,E_5^\perp\)
by the live output weights; the rows themselves have no ghost
component because \(e\in E_2\). In particular \(W_1=Ku\),
\(C W_j\subseteq W_{j+1}\) at \(j=1,2\), and
\(r_I\in W_2\). Here \(I\) denotes the original live set.

Suppose \(u\) is active at \(q\ge3\) different clocks.
Then
\[
     W_2=\langle u,Cu\rangle,\qquad
     W_3=u\,\mathcal P_{\le2}(c_I),\qquad
     r_I=L(C)u,\quad \deg L\le1 .
\]
All spans are exact by distinct-clock interpolation and the
three paid ranks, and \(L\ne0\) since \(r_3\ne0\).
The previously proved **linear** incoming Hermite bound
says \(W_3\) is not clock invariant in the genuine reduced
reverse; its proof uses the actual primitive defects through
grade four, not reflected order ten or preservation of squares.
If \(q=3\), the three clock powers of \(u\) isolate each active
clock block and \(W_3\) is clock invariant, contradiction.
Thus \(q\ge4\).

Paid grade-four/grade-five orthogonality gives the inclusion
\(F_4|_I\subset W_3\). The only vector direction lost in
restriction is \(Ke_2\): there is exactly one ghost coordinate
and its full indicator already lies in \(F_2\). Thus \(f_4=4\)
gives exactly \(F_4|_I=W_3\), not merely an inclusion.
Every old pure grade-four vector is zero at the original
origin (physical 1) by its model anchor. It is also zero at
physical 14: \(e_{14}\in E_5\) by the ordinary annihilator,
and its weighted pairing with \(F_4\) costs \(5+4=9\).
As \(b_{14}\ne0\), the terminal value is zero.
Consequently **\(u_1=u_{14}=0\)**, and at most eleven live
physical rows are active. Neither endpoint vanishing is inferred
from an unproved full reverse order.

## 2. Balanced pooled defect is impossible

If the pooled clock masses \(\nu_x=\sum_{c_i=x} b_i u_i\)
are all zero, every active clock has at least two physical
rows, so \(4\le q\le5\). We also have zero grouped square
masses \(\mu_x=\sum_{c_i=x}b_i u_i^2\):
* If \(L\) is nonconstant, the actual old pure grade-four lift
  of \(u\) pays the first four square moments against \(bu\).
  The tests of \(C^j r\), \(0\le j\le4\), give the
  \(L\)-weighted square moments, adding two by its nonzero
  slope. The resulting six moments kill all \(q\le5\) pools.
* If \(L\) is constant and nonzero, \(u\) has a genuine old
  pure grade-three lift \(r/L\). Hence five ordinary square
  moments \(b u C^j u=0\), \(0\le j\le4\), are paid
  against \(bu\in E_7^\perp\) and kill all the pools.

At a two-row active clock the first and second amplitude
moments force equal amplitudes and opposite ordinary weights,
so both rows together contribute no ordinary support site.
An active group of at least three rows contributes at most one
ordinary scalar support site. Thus every active clock saves
at least two of the thirteen live rows, giving at most
\(13-2q\le5\) ordinary scalar sites. This contradicts the
anchored degree-nine six-site floor at the live endpoint 1.

## 3. Nonzero pooled defect with nonconstant affine \(L\)

Nonzero pooled \(\nu\) requires \(q\ge9\) by its eight clock
moments. The two
[affine singleton and partial-repeat proofs](ERK10-INVISIBLE-GHOST-UNBALANCED-AFFINE-CLOSURE.md)
and the
[colliding pole and triple exits](ERK10-INVISIBLE-GHOST-AFFINE-REPEAT-EXITS.md)
cover exactly this branch, including a root of \(L\) on a
repeated active clock, or a repeated barycentric pole in the
singleton eleven-label chart. They use the paid old grade-four
lift explicitly. No positivity, sample numeric fit, or rank
assumption stronger than \(f_4=4\) is added.

## 4. Nonzero pooled defect with constant \(L\)

Now \(L\ne0\) is constant, so write \(u=r/L\) also for its
genuine whole old pure grade-three extension, which is zero at
the ghost. The terminal evaluation functional on \(F_6\) is
nonzero in every original 14-stage order-ten equality chart:
take the genuine \(e_{14}\in E_5\) and its model \(P\).
Its paid mean is \(\int_0^1 P=b_{14}\ne0\).
The actual strict advance \(Ae_{14}\) is the zero numerical
column, with scalar model \(J P\) at grade six. Subtract the
ordinary degree-six clock model to obtain a pure \(F_6\)
vector with terminal value \(-b_{14}\ne0\).
Because the exact original rank is \(f_6=7\), its terminal-zero
kernel has dimension six.

The three separate \(u,Cu,C^2u\) directions have paid old
grade-four lifts by §1. Subtract their ghost coordinates
times \(e_2\) to choose them all zero there. Advancing just
the **clock powers** of the last lift gives \(C^3u,C^4u\)
in grades five and six. Since \(q\ge9\), these five independent
live polynomial directions, plus \(e_2\), fill the terminal-zero
kernel. The actual pure grade-six square \(u^2\) vanishes at
physical 14, so it belongs to that kernel. Hence on every
live active site
\[
                             u_i=G(c_i)
\]
for one literal polynomial \(G\) of degree at most four.
The statement also means repeated active amplitudes agree;
it does not assume their weights have a nonzero pool.

Let \(D\) be the monic active clock hull. Exact moment
interpolation gives \(\nu=P/D'\) with \(\deg P\le q-9\).
The five unweighted square moments of \(bu\) against
\(C^j u\), \(0\le j\le4\), give numerator \(Q\) for the
grouped square with \(\deg Q\le q-6\).
The literal equality \(u_i=G(c_i)\) implies \(Q=P G\) at
all \(q\) labels, including any zero pooled label; the degree
bound \(2+4<q\) makes this a polynomial identity.
We also have the paid first two cubic moments of \(bu\)
against \(u^2,Cu^2\) in grades six and seven, which are
the Lagrange sums of \(P G^2\) and \(X P G^2\).
Their degree-\((q-1)\) leading coefficients give:
* \(q=9\): \(P\) constant and \(\deg G\le3\) from \(Q=P G\).
* \(q=10\): linear \(P\) gives \(\deg G\le3\) from the
  same identity; constant \(P\) and quartic \(G\) would give
  a nonzero degree-nine coefficient of \(X P G^2\).
* \(q=11\): quadratic \(P\) gives \(\deg G\le3\);
  linear \(P\) and quartic \(G\) would give a nonzero
  degree-ten coefficient of \(X P G^2\). Constant \(P\)
  may leave the degree-four bound.

The actual scalar \(G\)-weighted quadrature on live dormant
rows is exact through degree seven by the ordinary clock
moments and the \(bu\) moments. If at least ten live rows
are active, there are at most three dormant sites, including
the endpoints. With one internal dormant clock, \(\deg G\le3\),
so the anchored \(X(1-X)\)-Gram on \(G\) times the one
internal clock factor is nonsingular using the degree-seven
tests; if there are only the endpoints the same argument
already works for \(\deg G\le4\). Thus only \(q=n=9\) with
nine active rows and four dormant rows could survive.

For degree at most two, the four-dormant case is exactly
the fixed-four reflected contact from the
[affine proof, §3](ERK10-INVISIBLE-GHOST-UNBALANCED-AFFINE-CLOSURE.md#3-nine-labels-including-two-repeats-or-a-triple-at-the-root).
It did not use the nonconstant slope once the literal
quadratic profile was supplied: the genuine reverse clean
rows are point exact through four, and the grade-three
mask \((1-C)(G(c_I)-u)\) gives the forbidden first
reflected clean primitive. Three or fewer clean clocks,
or linear \(G\) at four clean clocks, are excluded directly
by the same anchored Gram.

Finally take **cubic \(G\)**. The old \(E_5^\perp\) is
\(b W_3\), supported entirely on active rows, so the four
individual dormant indicators belong to \(E_5\).
The original \(F_5|_I\) is exactly
\(u\,\mathcal P_{\le3}(c_I)\): the paid grade-four lifts and
their single clock advance already give four independent
live directions, and there is precisely the pure ghost kernel
in old \(f_5=5\).
Thus an old \(E_5\) vector supported on dormant rows has
live representation \(H(c)+u\,S(c)\) with
\(\deg H\le5,\ \deg S\le3\).
At nine distinct active labels it gives \(H+G S=0\),
a polynomial of degree at most six. This is a polynomial
identity, so \(\deg S\le2\).
Its four dormant coordinates are then
\(-G(c_i) S(c_i)\), ranging over a space of dimension
at most three. They cannot include four independent
individual dormant indicators. This contradiction closes
the constant case without an unearned reverse grade-five
formula.

The [affine scalar](../lean/RKCert/ReviewedNative/ERK10InvisibleUnbalancedSingletonGate.lean)
and [terminal alias](../lean/RKCert/ReviewedNative/ERK10InvisibleAffineRepeatGate.lean)
Lean receipts check the exact algebra used across the seams.
Low graded ranks, interpolation, and the dormant indicator
dimension argument are the mathematical proof above.
