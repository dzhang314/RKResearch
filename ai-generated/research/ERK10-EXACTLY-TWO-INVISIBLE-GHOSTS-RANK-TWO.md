# Exactly two invisible ghosts always leave cubic pure rank two

Work over any characteristic-zero field. Consider a genuine strict
explicit fourteen-stage order-ten tableau with **exactly two zero
output weights** and **every original quadratic defect invisible**:
\(B d=0\) for \(B=\operatorname{diag}(b)\) and
\(d=Ac-c^2/2\). The two zero-weight clocks may agree or differ;
either only one ghost quadratic entry may be nonzero or both may
be nonzero. No assumption on the relative amplitudes is made.

**Result.** The old pure rank is \(f_3=2\).
If the origin is a ghost, \(f_4=3\).
If \(f_4=4\), both ghosts are internal and their individual
coordinate indicators are already genuine pure grade-four
vectors. Under this **extra** rank-four hypothesis the literal
live vector \((Ad)|_I\) is either zero or supported on just
one clock. Its zero case forces adjacent ghosts 2 and 3
and the two old ghost axes already at grade three.
These are necessary reductions, not a complete exclusion
or a change in the unrestricted 14–15 interval.

## 1. A fully live three-row annihilator cannot be a rank-four projection

Use the [14-stage equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md).
In particular \(f_5=5,f_6=7\), strict low pure growth,
\(V_1=E_7^\perp,\ V_2=E_6^\perp,\ V_3=E_5^\perp\)
have ranks \(1,2,3\), and \(bA=b(1-C)\).
Physical 14 and physical 13 are live, with \(c_{14}=1\).
The origin value of every old pure vector is zero, and
all old \(F_4\) vectors have terminal value zero by
pairing with the actual \(e_{14}\in E_5\) and \(b_{14}\ne0\).

Let \(I\) be the original live set and \(Z\) the two-dimensional
coordinate space of the ghosts. Physical 2 is a ghost:
otherwise \(d_2=-c_2^2/2\ne0\) would be visible; \(c_2=0\)
is excluded by literal duplicate removal. Thus \(d\ne0\) and
\(F_4\cap Z\) contains at least one direction. This argument
does not require the *other* ghost entry of \(d\) to be nonzero.

Suppose the old \(F_4\) has live projection of rank three.
Then \(f_4=4\), its ghost kernel has rank one, and by
paid grade-four/grade-five orthogonality
\[
                             B F_4=V_3 .
\]
Thus \(V_1,V_2,V_3\) are all supported on live coordinates;
each ghost indicator is in the actual old \(E_5\).
For an internal ghost \(g\), its degree-five model \(P_g\)
vanishes at 0 by the true original anchor. Its first five
moments vanish by pairing the indicator with \(1,C,\ldots,C^4\),
which is paid through grade nine and is numerically zero
because \(b_g=0\). The nonsingular anchored \(X\)-Gram on
\(P_g/X\) makes its model zero. Thus every such internal
indicator is actually **pure \(F_5\)**.

If both ghosts are internal, both axes of \(Z\) therefore
belong to \(F_5\). Since \(F_4\cap Z\) has rank one and
\(f_5-f_4=1\), the whole increment is a ghost direction.
In particular \(F_5|_I=F_4|_I\), and \(C F_4\subset F_5\)
implies \(C(F_4|_I)\subset F_4|_I\).

This last invariance is impossible for a genuinely reduced
strict reverse chart with the fully live linear flags just
earned. Here are the exact gates, not an assumed reverse order.
Use \(A^\vee=B_I^{-1}A_{II}^{\mathsf T}B_I\) on the live rows
in reverse chronology. It has actual reflected clock \(Y=1-C\)
by \(bA=bY\). Put \(W_j=B_I^{-1}(V_j|_I)\).
The first four linear polynomial primitive errors for
\(A^\vee\) land in the appropriate \(W_j\)'s:
indeed \(bY^i A-bY^{i+1}/(i+1)\) annihilates \(E_{8-i}\)
by the formal integration by parts test at grade nine,
and has no ghost entries. Further \(A^\vee W_2\subset W_3\)
by exact right flag growth.
If \(W_3\) were invariant and at most one clock block failed
to have its constant indicator in \(W_3\), a nonzero linear
polynomial vanishing at that exceptional clock would have its
stage values in \(W_3\). Pairing with \(b,bY\) would contradict
the nonsingular two-by-two scalar moment Gram. Hence there
are two failed clock blocks.
The
[linear incoming Hermite rank test](ERK10-SINGLE-INVISIBLE-GHOST.md#2-the-true-linear-reverse-rooms-with-the-square-exposed)
then gives \(2+2\le3\), impossible for these two linear rooms.
Its exact requirements are the just-paid primitive defects
and \(A^\vee W_2\subset W_3\), not closure of any reverse
nonlinear square. In the assumed rank-three projection
\(W_3=F_4|_I\), the rejected invariance.

If one ghost is the origin, do **not** assume its indicator
is pure. Its genuine \(E_5\) model, here, is the normalized
shifted Legendre polynomial
\[
             \Lambda_5=1-30X+210X^2-560X^3+630X^4-252X^5.
\]
It is uniquely specified by value 1 at the origin and the
same five zero moments. It has value \(-1\) at 1.
Thus \(e_1-\Lambda_5(c)\) is genuinely pure \(F_5\), with
terminal value 1. It spans the sole increment modulo
the terminal-zero \(F_4\).
Since \(C F_4\) is terminal zero, it must already lie
in \(F_4\); this clock invariance contradicts the genuine
grade-four outgoing bound against \(f_5=5\).
This proves in both cases that old projected \(F_4\) has
rank at most two.

## 2. Rank-three cubic room is impossible without amplitude assumptions

If \(f_3=3\), strict growth into \(f_5=5\) gives \(f_4=4\).
By §1 the ghost kernel in \(F_4\) then has rank two, so it
is all of \(Z\). This excludes the origin-ghost case at
rank four, since pure old coordinates at the origin vanish.

If \(F_3\cap Z\) has rank one, then \(F_3|_I=F_4|_I\)
of rank two. Hence \(C(F_4|_I)\subset F_4|_I\) by
\(C F_3\subset F_4\). The **full** ghost axes are in \(F_4\),
so this projected invariance lifts to the original \(F_4\):
subtract from \(Cx\) an old \(F_4\) lift with the same live
coordinates; their difference is a ghost vector in \(F_4\).
Again the outgoing bound contradicts \(f_5=5\).

Otherwise \(F_3\) contains both old ghost indicator axes.
Choose any third old pure grade-three direction \(p\), and
use those axes to clear its ghost coordinates. The full
[arbitrary third-direction exclusion](ERK10-TWO-INVISIBLE-DISTINCT-DEFECT-CLOCKS.md#2-third-pure-direction-exact-profile-and-actual-late-removal)
applies mechanically: once \(F_3=Z+Kp\) with both ghost
axes actually paid at grade three, its proof of the terminal
kernel and the one- and two-middle scalar seams no longer
uses distinct ghost clocks or the particular quadratic error
values. Do not invoke its optional early removal argument
or identify \(p\) with \(Ad\). The two ghost axes are
individually clock-stable whether or not their clocks agree.
For reference the rank chain is
\(F_4=Z+p\mathcal P_{\le1},\ F_5=Z+p\mathcal P_{\le2}\)
and the terminal kernel \(Z+p\mathcal P_{\le3}\).
It forces a literal cubic-or-less live \(p\)-amplitude
using the genuine grade-six square. At least eight distinct
active sites then remain or the support floor fails; the
true terminal indicator and the cited causal seams exclude
all of those supports.

Therefore \(f_3=3\) never occurs. Strict lower growth gives
\(f_3=2\). If the origin is a ghost, \(f_4=4\) was excluded
in §1 and growth now forces \(f_4=3\).
This proof covers exactly one nonzero quadratic defect entry,
two equal nonzero amplitudes, or unequal amplitudes at either
equal or different defect clocks.

## 3. With \(f_4=4\), the live advance is zero or one-clock

Assume the **additional** \(f_4=4\) hereafter.
The ghost axes \(e_2,e_g\) are actual \(F_4\) by §1.
If \(p=(Ad)|_I\) is nonzero, the untrimmed actual old
\(p^{\sharp}=Ad\) is genuinely pure grade three, and
\(F_3=\langle d,p^{\sharp}\rangle\) by rank.
Suppose the live \(p\) has at least two distinct active clocks.
Then \(F_4|_I=\langle p,Cp\rangle\) and the full ghost axes
complete the original \(F_4\). Exactly two live clocks would
make original \(F_4\) invariant, impossible. Hence at least
three; \(F_5|_I=p\mathcal P_{\le2}(c_I)\) by dimension.
Exactly three would in turn make \(F_5\) invariant and
force \(f_6\ge8\). Thus at least four.

The terminal-zero kernel of old \(F_6\) is
\[
                           Z+p^{\sharp}\mathcal P_{\le3}(c).
\]
The displayed six columns have the correct degrees and are
independent by the four active labels; their terminal values
vanish since \(p^\sharp\) is pure of grade three.
The kernel has exactly rank six as usual from the genuine
\(e_{14}\in E_5\): its numerical zero advance and scalar
primitive of mean \(b_{14}\ne0\) give a grade-six pure
vector with nonzero terminal value after subtracting its
clock model.
The actual square \((p^\sharp)^2\) costs grade six, and
is terminal zero. **No trimmed grade-four square is used.**
By that kernel equality \(p\) really agrees with a nonzero
polynomial \(R\), of degree at most three, on all its live
active rows.

The same support argument in the cited two-ghost proof
now requires at least eight distinct active labels from
the first seven \(b p^\sharp\) moments (or zero pooled
mass and too few ordinary support sites).
For the genuine compensated mask use
\[
       T=R(c)-p^\sharp-\sum_{g'\ {\rm ghost}}
                       (R(c_{g'})-p^\sharp_{g'})e_{g'} .
\]
Although the last terms may cost grade four as old pure
vectors, multiplying either indicator by any clock
polynomial only scales it numerically, hence costs no
additional actual pure grade. Therefore \(CT,(1-C)T\)
and \((C-w)T\) each have grade at most four and the correct
formal polynomial model, since the rest of \(T\) costs
grade three. The known one- and two-middle cuts pay
total grade nine with these exact lifts. When there are
eight active rows, \(F_5|_I=p\mathcal P_{\le2}\) makes
every live dormant row genuinely point exact through five
and the same terminal-indicator constraint controls their
clock supports. This is precisely the previously verified
same scalar argument; the amended grade accounting here
is its only change.
It excludes \(p\) on two or more clocks in the rank-four
chart.

If instead \(p=0\) live, a live physical row 3 would have
\((Ad)_3=d_2 A_{32}\ne0\), as its first live quadratic
formula forces \(A_{32}\ne0\). Thus the ghosts are 2 and 3.
If \(Ad\ne0\) numerically, its only possible nonzero coordinate
is then physical 3 and \(F_3=Z\) follows immediately.
If \(Ad=0\) numerically then \(A_{32}=0\).
A zero \(c_3\) would duplicate origin and \(c_3=c_2\)
would duplicate row 2 (both are Euler rows when \(A_{32}=0\)).
Otherwise both ghost Euler defects are nonzero at distinct
clocks, so \(d,Cd\) already span \(Z=F_3\).
This latter case in fact contradicts the exact first live
cubic constraint as in the adjacent distinct-clock packet,
but the asserted ghost-axis conclusion does not need that exit.
Every live row in this zero-advance case is exact through
old grade three, and \(d_2 A_{i2}+d_3 A_{i3}=0\) there,
whether or not \(d_3=0\).

The new graded rank reduction above is a mathematical proof. The
linked scalar seams are the separately verified Lean components;
there is no end-to-end native theorem for this broader statement.
