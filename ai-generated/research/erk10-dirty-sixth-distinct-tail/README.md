# Actual marked trees rule out a distinct six-row tail of the dirty relay

This is a conditional mathematical obstruction to the literal
[nine-row dirty relay](../erk10-dirty-sixth-relay/README.md) with
six subsequent physical stages, not a general ERK10 lower bound.
It does not require literal reverse co-order as an input. It works
with arbitrary rational output signs and permits late zero-output
stages. It requires the actual decoder cross-feed below and distinct
late clocks away from three earlier sites.

## Tableau and decoder assumptions

Use any nonzero scaling of the nine-row literal, with the FSAL
clock \(\xi\), ghost \(z=\xi/3\), and clean relay \(w=2\xi/3\).
Scale its degree-four decoder \(\Pi\) coherently. Let \(E\) evaluate
polynomials in all nine high stage clocks (FSAL, ghost, relay,
plus the six appended). Let \(B\) consist of the actual late-to-late
strict block padded by zero in its first three high rows and columns;
the early indices are supplied through the old physical block instead.
The appended rows use the actual rational cross-feed
\[
       \bigl[(EJ-BE)\Pi\bigr]_i
\]
into the first nine physical coordinates, where \(J\) is the
polynomial primitive from zero. Their remaining strict coefficients
are \(B\). The full first nine rows remain the genuine literal.
Finally \(\boldsymbol b\) is supported on the origin and the nine high
rows; no weight restrictions beyond this support are imposed.
The six appended clocks are pairwise distinct and disjoint from
\(0,\xi,w\).

The actual FSAL and relay incoming rows equal \(J_\xi\Pi,J_w\Pi\)
on all first-nine physical columns, with the needed trailing
zeros. This is checked independently in the replay. The size-six
ghost has a nonzero degree-six derivative defect. Every appended
stage is pure through derivative size six by chronology and
the true degree-four prefix decoder: all its predecessors' profiles
through size five are exact in the high block and read exactly
by \(\Pi\) in the first nine physical rows.
Any order-ten output on the stated support must therefore have
\(b_z=0\) by the literal ghost defect at size six.
This does not assume all other high weights are live.

## Six residual sources from actual finite rooted trees

For a rooted tree \(\tau\), write
\[
 g_\tau(X)=|\tau|X^{|\tau|-1}/\gamma(\tau),\quad
 H_\tau=g_\tau-\Pi\boldsymbol\Phi_\tau^{\rm old}.
\]
When all immediate children of \(\tau\) have size at most five,
its full high derivatives are ideal at the FSAL, relay, and all
late stages, even if \(|\tau|>6\): each child primitive is paid
exactly, and the actual derivative is their product. The ghost
may differ, but is never read through \(B\) and has zero final mass.
Then \(H_\tau(0)=H_\tau(\xi)=H_\tau(w)=0\) by the three
physical decoder cardinal aliases relevant to these roots
(origin, FSAL, relay).

At size six choose three genuine sources: the bush, the root
with one leaf and one bush of size four, and the unary above the
bush of size five. Their \(X,X^2,X^3\) coefficient minor is exactly
\(11/1728\) at unit scaling, by the independent literal replay.
They therefore span \(Q\mathcal P_2\), \(Q=X(X-\xi)(X-w)\),
since every such source has degree at most five.
Adjoin the bushes of sizes seven, eight, nine, all of whose
immediate children are leaves. Their residuals have leading
coefficients one at respective degrees six, seven, eight,
because the decoder has degree at most four.
Through those respective sizes their union with the first three
sources spans \(Q\mathcal P_3,Q\mathcal P_4,Q\mathcal P_5\).
Nonzero homothety preserves all these spans.

## Marked actual order forces full D(1), D(2) at the late columns

Define \(L=EJ-BE\). Attach a unary root to one of the source trees
above; its actual output differs from the nominal integrated
derivative by \(-\boldsymbol b^\top L H_\tau\).
This follows directly from the decoder feed and the actual ideal
high source values; the zero-mass ghost term is invisible.
For a new root with that same source child and one extra leaf,
the difference is \(-\boldsymbol b^\top C L H_\tau\), where
\(C\) is the high clock diagonal, because the leaf primitive is
the actual clock. The genuine order-ten scalar moments pay the
nominal terms in both cases.
The unary tests apply through source size nine (total at most ten);
the second marked tests apply through source size eight
(total at most ten). Thus
\[
  \boldsymbol b^\top L(Q\mathcal P_5)=0,\qquad
  \boldsymbol b^\top C L(Q\mathcal P_4)=0 .
\]

By polynomial integration by parts, the two equations mean
that the late parts of the actual reverse errors
\[
 \boldsymbol r_j=\boldsymbol b^\top C^j B-
   \boldsymbol b^\top(1-C^{j+1})/(j+1),\qquad j=0,1 ,
\]
annihilate evaluations of \(Q\mathcal P_5,Q\mathcal P_4\),
respectively. Other coordinate contributions are zero because
\(Q\) vanishes at the origin, FSAL and relay and the ghost
has no output or raw \(B\) column. The integrations have
total degree at most nine, as required.

The six late clocks are distinct and \(Q\) evaluates nonzero
on them, so the first equation (six dimensions) gives
\(\boldsymbol r_0=0\) on every late column.
There is some nonzero late weight, because the other output sites
alone cannot integrate even degree four. At the chronologically
latest nonzero late weight all later coefficients in the weighted
read vanish, so its clock is 1. Its \(\boldsymbol r_1\) coordinate
is already zero (both the weighted read and target vanish).
Now \(Q\mathcal P_4\) has independent evaluations on the five other
late columns, so \(\boldsymbol r_1=0\) on those too.
This argument does not require the final physical row to be live.

Scalar degree-nine precision moreover requires at least one
additional nonzero late weight away from 1: otherwise at most four
distinct scalar sites are live, contradicted by the integral of their
squared hull (degree at most eight).
At the chronologically latest such interior live coordinate
\(x\ne1\), every strictly later nonzero weight is at clock 1.
The two reverse identities at its column have the same left-hand
side and give respectively \(b_x(1-x)\) and \(b_x(1-x^2)/2\).
This forces \((1-x)^2 b_x=0\), a contradiction.

Consequently, within this literal decoder architecture any
15-stage rational order-ten candidate must have a repeated late
clock or a collision of a late clock with \(0,\xi,w\).
The conclusion neither assumes nor excludes a zero root mass at
an otherwise admissible late slot, and does not cover other
decoder architectures.

## Replay and native scope

    python -B audit.py
    sha256sum -c sha256.txt

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.ERK10DirtySixthDistinctTailScalars

The Lean gate kernel-checks the denominator-cleared actual
size-six minor from the previous relay's integer matrix/decoder,
and the last scalar equality. The separated physical/marked
proof and Vandermonde arguments are given mathematically above.
