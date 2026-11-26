# Split local arithmetic runs and the common-diagonal p>=11 floor

This extends the [seven-clock argument](sdirk-local-seven-clock-floor.md) to two shorter runs. A common-diagonal
triangular tableau over a characteristic-zero field, of order at least
\(p\ge11\), has at least \(p+1\) physical stages. No signs, real embedding,
stability, or restriction on the prescribed common diagonal are assumed.
This does not give a bound for differing-diagonal DIRK, sharpness, or a new
all-chart conclusion below this range.

The new structural obstruction is a pair of disjoint arithmetic clock runs
of the same nonzero step, with at least five clocks in one and three
in the other, in the cyclic nonzero-diagonal degenerate rectangle chart at
\(p=s\). The offset of either run is free and they may be separated
by arbitrary physical clocks. Without the rectangle-chart assumption,
five and four such clocks still suffice. The proof uses only literal
occupied-slot placement and the stated paid words.

## 1. Placement: one endpoint overrun can be harmless

Work first at \(p=s\), with \(A=\gamma I+B\) (\(\gamma\ne0\)),
\(B\) strictly lower triangular, \(c=Ae\), and actual
\(L=b^TB^{s-1}e\ne0\). Write \(a_i=B_{i,i-1}\), which are all
nonzero, as is \(b_s\). Let the two disjoint physical runs have
the same nonzero step \(\delta\), with no condition on their offsets.
Suppose first that the length-five run is earlier:
\([a,a+4]\) and a later length-three subrun \([b,b+2]\),
so \(b\ge a+5\). If a length-four later run is specified below,
use \([b,b+3]\) instead.

A path on \(m=s-h\) occupied sites has increasing physical positions
\(v_i\), and \(i\le v_i\le i+h\) for every occupied slot \(i\).
Its passed-hole count \(v_i-i\) is nondecreasing. At an occupied
link \(i\) to \(i+1\), the number of holes across the link is
\(g_i=v_{i+1}-v_i-1\). For a desired count \(d\ge1\) mark the
directed clock difference with
\[
            P_d(c_{v_{i+1}}-c_{v_i})
               =\prod_{j=1}^{d}(c_{v_{i+1}}-c_{v_i}-j\delta).
 \tag{1}
\]
If both endpoints belong to one of the two runs, it vanishes for
\(g_i<d\), and its value is \(\delta^d d!\) for \(g_i=d\).

**Pairs \((d,1)\) for \(d=1,2,3\).** Take \(h=d+1\) holes.
Place the marks at occupied links \(a\) and \(b-d\) respectively.
These links are strictly ordered: \(b-d\ge a+2\).
The donor of the first link is at most \(a+h\le a+4\).
If its receiver is in \([a,a+4]\), a nonzero first mark requires
at least \(d\) holes in that gap. The only possible exit is
\(h=4\) with receiver \(a+5\): all \(h\) holes have then been
passed, since this receiver is at occupied slot \(a+1\).
In either case for a path that is not already killed,
at least \(d\) holes have passed by the donor of the second link.
Its actual endpoints are therefore in
\[
                           [b,b-d+h+1]=[b,b+2].
\]
The last bound also verifies the existence of the occupied links
since \(b-d+h+1\le s\). In the exit case the second link has no
extra holes, so its mark kills that path. Otherwise both
normal arithmetic tests apply. Their product survives exactly
when the marked hole counts are \(d,1\) and there are no other
holes. The literal retained gaps are \(a\) to \(a+d+1\) and \(b\)
to \(b+2\).

**The triple \((1,1,1)\).** Take \(h=3\) and occupied
links \(a,a+1,b-2\). The first endpoints lie in \([a,a+4]\).
A path surviving the first mark has passed at least one hole
by the second donor, putting this donor in \([a+2,a+4]\).
Only its receiver \(a+5\) could exit the first run, and in
that case all three holes have already passed. On any path
that can now survive, at least two holes have passed by the
third donor, and its endpoints lie in \([b,b+2]\).
The exit case gives zero at this last mark. Thus the only
surviving hole allocation is one in each marked gap and none
elsewhere. The actual first two gaps are \(a\) to \(a+2\) and
\(a+2\) to \(a+4\), and the third is \(b\) to \(b+2\).
The two gaps within the first run share a retained endpoint,
but not a strict edge.

**The extra pair \((2,2)\).** With a later run of length four,
take \(h=4\) and links \(a,b-2\).
Just as for the first pair construction, the only possible
exit of the first receiver is \(a+5\), which consumes all
four holes and is killed by the later mark of target two.
Otherwise after possible survival at least two holes have
passed, so the later endpoints lie in \([b,b+3]\).
The unique surviving allocation has two holes in each of
the two marked gaps.

The proof works when the longer run is later as well: reflect only
the increasing physically indexed retained lists by
\(v'_i=s+1-v_{m+1-i}\). The original runs in the reflected clock list
have step \(-\delta\). Apply the same geometric placement argument to
these lists, and choose the corresponding physical links in the
original increasing orientation. The reflected clock difference is
the negative of the original one, so
\(P_d(-w;-\delta)=(-1)^d P_d(w;\delta)\) preserves the zero pattern
and the original surviving value remains \(\delta^d d!\).
This is only an index reflection for placement; it does not reverse
the directed RK tableau, its output weights, or the formal operator
payment.

## 2. Exact multiplicative moment identities from those placements

For each marked internal physical gap \(u\) to \(v\) that survives in
Section 1, calibrate its normalized skip
\(B_{v,u}/(a_{u+1}\cdots a_v)\) using the single mark at occupied
slot \(u\) among paths with \(d=v-u-1\) holes.
Every possible actual endpoint then lies in \([u,v]\), which is
inside the appropriate arithmetic run, so the mark really isolates
this one physical skipped interval. This is the same single-mark
calibration as the seven-clock proof. The surviving combined
physical path has normalized weight the product of those
specific calibrated skips. This holds with position-dependent
or zero skips, since the omitted intervals replace disjoint
blocks of the full adjacent product and no skip is divided by.

Let \(J\) be formal integration from zero, \(T=J-\gamma I\),
\(X\) multiplication by the variable, and \(\ell\) integration
from 0 to 1. The rooted clock model maps \(B,C\) to \(T,X\),
where \(C=\operatorname{diag}(c)\). A link polynomial \(P_d\)
is modeled by \(Q_d(T)\) with \(w^0 B\) mapped to \(T\) and
\(w^jB\) for \(j\ge1\) mapped to \(j!J^{j+1}\).
This follows from the commutators \([X,J^j]=jJ^{j+1}\).
A marked path of \(s-h-1\) strict hops and total mark degree \(h\)
pays \(s\) rooted vertices, including its initial leaf.
Both the isolated and combined tests in Section 1 meet this
budget at equality \(p=s\).

Define \(t=\delta/\gamma\) and
\(Q_d(T)=d!T^{d+1} F_d(\gamma/T)\) as a formal polynomial
identity after clearing \(T\). In terms of \(y=\gamma/T\)
and \(w=1+y\), these are
\[
 \begin{aligned}
 F_1&=w^2-t y,\\
 F_2&=w^3-\tfrac32 t y w^2+t^2 y^2,\\
 F_3&=w^4-2t y w^3+\tfrac{11}{6}t^2y^2w^2-t^3y^3.
 \end{aligned}
\]
Let \(\lambda_j=b^TB^je=\ell(T^j1)\) be the paid tall values,
and write \(\mu(y^k)=m_k=\gamma^k\lambda_{s-1-k}/L\).
In the formal marked words, all \(Q_d\) commute with \(T\).
The \(d+1\) reverse grades add with the unmarked hop powers
to \(s-1\); the total formal answer is therefore \(L\) times
the product of mark factorials times \(\mu\) on the corresponding
polynomial product. The actual combined word gives the product
of the individually calibrated factors with exactly this same
normalization. This proves multiplicativity for
\[
              F_1^2,\quad F_1F_2,\quad F_1F_3,\quad F_1^3
 \tag{2}
\]
under the five-plus-three layout, and additionally for \(F_2^2\)
under five-plus-four. The isolated single tests use at most
five consecutive clocks individually. These are exactly the
products used by the earlier grade-six contradiction; hence
five-plus-four works without any rectangle rank premise.

## 3. Why the degenerate rectangle needs no pair (2,2)

Use the exact cyclic rectangle chart at \(s=p\ge8\), with
\(\gamma\ne0,L\ne0\). Let its coefficients be \(D,E,F\) and
\(\Delta=DF-E^2\). In the degenerate branch \(D\ne0\),
the common slope \(\delta=-E/D\ne0\).
Write \(U,V\) for the consecutive tall expressions
\(U=MK-LR,\ V=LS-K^2\), with \(M,K,R,S\) the paid moments
\(\lambda_{s-2},\ldots,\lambda_{s-5}\). The exact rectangle
identities are \(E=-2\gamma D+\gamma^2U\),
\(D=LK-M^2\), and \(\Delta=\gamma^4(DV-U^2)=0\).
Normalize them by
\[
 {\cal D}=m_2-m_1^2,\quad {\cal U}=m_1m_2-m_3,\quad
 {\cal V}=m_4-m_2^2 .
\]
Then \({\cal D}\ne0\), \({\cal D}{\cal V}={\cal U}^2\), and
\(2-t={\cal U}/{\cal D}\), where \(t=\delta/\gamma\).
Thus the centered monic quadratic \(q=F_1-\mu(F_1)\)
satisfies
\[
       \mu(q)=0,\quad
       \mu(q y)=-{\cal U}+(2-t){\cal D}=0,\quad
       \mu(q y^2)={\cal V}-(2-t){\cal U}=0.                  \tag{3}
\]
These statements are actual scalar consequences of the
degenerate branch, not assumed positivity or square tests.

If \(t\ne2/3\), the cubic coefficient of \(F_2\) is
\(1-3t/2\ne0\). From the paid \(F_1F_2\) and (3),
\(\mu(q F_2)=0\) gives \(\mu(q y^3)=0\).
Only that single pair is needed for this generic slope;
in particular one local run of six clocks suffices, since
the pair has \(h+q_{\rm links}=3+2=5\) and fits wholly there.

If \(t=2/3\), set \(u=y+1-t/2\) so \(F_1\) is even in \(u\).
The odd cubic coefficient of \(F_3\) in \(u\) is \(4/81\),
from the exact expansion in the arithmetic core. Subtract
a scalar multiple of the monic quartic \(F_1^2\) to remove the
quartic term of \(F_3\); the remainder has degree three and
nonzero cubic coefficient. The paid \(F_1F_3\) and \(F_1^3\)
in (2) make \(q\) orthogonal to that remainder (the latter
uses \(\mu(F_1^2)=\mu(F_1)^2\), already implied by (3)).
Hence again \(\mu(q y^3)=0\). No product \(F_2^2\) was used.

Now \(\mu(q y^k)=0\) for \(k=0,\ldots,3\) means
\(m_0,\ldots,m_5\) satisfy one fixed monic quadratic recurrence.
The reverse tall recurrence is
\[
 (s-k)m_k=(\xi-2(s-1-k))m_{k+1}-(s-2-k)m_{k+2},
                       \quad \xi=1/\gamma,\quad m_0=1 .
\]
The fixed-recurrence rejection in the sealed arithmetic core
already needs only \(k=0,\ldots,3\), not \(k=4\).
For clarity, distinct nonzero quadratic roots give a residual
sequence that is a combination of two exponential-affine modes
and has a fixed fourth-order recurrence. Four consecutive
zero residuals force it identically zero; the residual affine
factor for a mode \(r^k\) has slope \(-(1+r)^2\) and at
\(r=-1\) is \(\xi\ne0\), so neither mode can remain.
For a repeated nonzero root the residual divided by \(r^k\)
is quadratic in \(k\); the same first rows force it identically
zero and then eliminate its coefficients, exactly as in the
core. A zero root leaves a single geometric mode from \(k=1\)
on, ruled out by rows 1 and 2, or directly \(m_1=m_2=0\);
row 0 then contradicts \(m_0=1\). This is a contradiction.
Thus the five-plus-three layout cannot occur in this chart.

## 4. Uniform consequence and exact budget limit

Suppose \(p\ge11\) and \(s\le p\). The established saturated
common-diagonal theorem gives \(s\ge p\), hence \(s=p\).
Zero diagonal is excluded by the established ERK rectangle
equality test, and nonzero diagonal has \(L\ne0\) from the
earlier no-cancellation theorem. The nondegenerate rectangle
chart already has globally arithmetic clocks, excluded by
the seven-clock local theorem. In the degenerate chart the
sealed literal factorization gives either an arithmetic
prefix through \(s-2\), or two literal equal-step, nonzero-step
arithmetic runs with two intervening boundary clocks and
run lengths summing to \(s-2\). The prefix with length \(s-2\)
is too long by the seven-clock result. For two runs, if one
has length at least seven use that same result. Otherwise
each length is at most six and their sum is at least nine,
so one has length at least five and the other at least three.
Sections 1--3 exclude that layout. This proves \(s\ge p+1\).

The marks above require total rooted order \(s\). At \(s=p+1\)
they are not paid. Using one fewer total mark on the same
number of holes allows an extra unlocated omission in the
surviving allocation, so the isolation proof does not carry
over; the cyclic top value would also be unpaid. No next
surplus-stage lower bound or coverage of any unresolved
shorter-run layout is inferred.

Frozen dependencies are the literal rectangle proof
(CYCLIC-PAID-RECTANGLE.md, SHA-256
b9ee35a0ac94c1ad346a2b3b0b451ebd525aa2e353bfc2d2193e30aac044711d),
the arithmetic core (PAID-ARITHMETIC-GAP-EXCLUSION.md, SHA-256
0ec9a1ff481ec6b8c7946e86d7afe79c3ea9991e88c4aba1315a8ef6285b12ed),
and the prior exact dependency join in LOCAL-SEVEN-CLOCK-FLOOR.md,
SHA-256 123d15da36ceb3da6f2890eb2e7c0574f26d1e70e792293660ca1f6e312e41ce.
