# The degree-five path obstruction in the reflected four-carrier branch

Continue the
[half-clock two-ended exact branch](ERK11-ONE-SPARE-WEIGHTED-TRANSPOSE.md).
The strictly explicit 17-row method has maximal rank-two aliases,
all ordinary weights nonzero, and both half-clock tail carriers at
rows 13 and 16. The two-end dense cutoff and the four-carrier count
are assumed here. The local deductions below need only a field
paying \(11!\) after those premises. No new unconditional stage
bound is being asserted.

**New exclusion.** The second early carrier cannot be physical row 6.
The four carrier positions are exactly \(2,5,13,16\), with no
relabeling needed. If \(\theta\) is their common physical clock,
the early clocks at 3 and 4 are \(\theta/2,\theta\); row 6 is clean
at a clock different from \(0,\theta/2,\theta\). Every consecutive
edge in the first six slots is live, as is already known for the
last six. The degree-five forward and reverse taps mask all four
carriers. Both opposing-weight pairs and four-distinct carrier
states are still open.

## Normalized front algebra

Let \(s\) be the physical indicator of the carrier rows and let
\(r=As\) in ordinary coordinates. All carriers have
\(\delta=Ac-c^2/2=-\theta^2/2\) and noncarriers have zero
quadratic defect. In particular \(\theta\ne0\).
The already proved pure spaces in ordinary coordinates are
\[
 F_3=\langle s,r\rangle,\quad
 F_4=\langle s,r,Cr\rangle,\quad
 F_5=\langle s,s\odot r,r,Cr,C^2r\rangle.
\]
The same spaces apply with \(r\) multiplied by any nonzero
scalar and \(C\) scaled accordingly.
Normalize the front by \(A\mapsto A/\theta\),
\(c\mapsto c/\theta\). In this section write \(f=As\)
using this scaled matrix. Then \(\delta=-s/2\);
the first carrier is at 2. By the previous literal
fourth-carrier check, rows 3 and 4 are both clean.
Put \(N=c_3,\ T=c_4\), both in these scaled units.
Neither is zero, and \(T\ne N\): at \(T=0,N\)
the first two clock moments make row 4 a raw duplicate
of, respectively, row 1 or row 3. Such equalities are
impossible on a full literal first-eleven \(E_5\).

The exact grade-three relation determined on rows 2 and 3 is
\[
 Ac^2-c^3/3=(2/3)\delta+(1-2N/3)f,
 \qquad f_3=N^2/2 .
\]
The two first moments on row 4 yield
\(f_4=T^2(3N-2T)/(2N)\) and \(A_{43}=T^2(T-N)/N^2\).
When \(D_0=3N-2T\ne0\), the three pure vectors
\(\delta,f,Cf\) are already independent on the first
four, and exact grade four gives
\[
 Af=\alpha(C-N)f,\qquad
 Ac^3-c^4/4=\delta/2+
      [1-N^2/2-\alpha(T-N)(C-N)/2]f,\qquad
               \alpha=N/D_0.
\]
When \(D_0=0\), the spanning vectors instead are
\(\delta,f,g\) for \(g=Af\);
\(Cf=Nf\) and
\(Ac^3-c^4/4=\delta/2+(1-N^2/2)f-(N/4)g\).
These are only grade-four identities. They require
the first four actual heads just described and
\(\dim F_4=3\), not a global single-carrier assumption.

### Row 5 cannot be clean

If row 5 is clean, it reads only the origin, the
one carrier at 2, and the two clean rows at \(N,T\).
The exact fifth-row calculation in
[the four-row seed analysis](erk-single-quadratic-defect/SINGLE-SECOND-ROW-DEFECT-SIX-LOWER-BOUND.md),
Cases 1 and 2, applies to this row: its only reads of
\(f=As\) through row 5 use the sole available carrier
column 2. Its cited equations (2)–(3) and the \(D_0=0\)
alternative are the preceding grade-four identities,
plus the actual clock hull on the first four donors.
They use no rank or root test through grade five.
The \(D_0=0\) case makes the proposed clean row a duplicate.
For \(D_0\ne0\), it is likewise a duplicate except
possibly for \(c_5=T=2N\), \(f_5\ne f_4\), with row 5
clean at the same nonzero clock as row 4.

That last alternative is impossible by the **actual
degree-five unary column** \(A^5\mathbf1\).
Its exact model is \(c^5/120\), and its pure correction
belongs to the displayed \(F_5\). On any clean row its
numerical value is therefore \(c^5/120+P_2(c)f\) for one
polynomial \(P_2\) of degree at most two (the terms
supported on carriers drop out).
Strictness makes \(A^5\mathbf1\) zero at both rows
4 and 5. At equal clock \(T\ne0\) but distinct \(f\),
these equalities force \(P_2(T)=0\) and then \(T^5=0\),
contradiction. Thus **row 5 is the second early carrier**.
This is stronger than interchanging rows 5 and 6:
physical row 6 cannot be the carrier in any literal
ordering satisfying these premises.

### Calibrating the actual fifth carrier

Let \(a=A_{52}=f_5\).
If \(a=0\), the first two moments on the new carrier
give zero pooled reads of the two distinct nonzero
clocks \(N,T\), so it duplicates row 2.
Thus \(a\ne0\). The alternative \(D_0=0\) is also
impossible: \(Cf=Nf\) at clock 1 and \(a\ne0\)
requires \(N=1,\ T=3/2\). The first two moments give
\(A_{54}=4a/9,\ A_{53}=-5a/3\), so \(g_5=-5a/6\).
The actual cubic donor relation gives \(Ac^3=5a/6\),
whereas the \(D_0=0\) pure formula gives
\(Ac^3=a/2-g_5/4=17a/24\).
This forces \(a=0\), contradiction.

In the remaining \(D_0\ne0\) case, the two first
clock moments give
\[
 A_{53}=\frac{T-2N/3}{N(N-T)}a,\qquad
 A_{54}=\frac{N}{3T(T-N)}a .
\]
Insert these in the exact \(Af\) relation and the
cubic-clock relation at the carrier c=1. Dividing by
the live \(a,N,T,N-T,D_0\) and paid constants gives
\[
                     NT+3N-2T^2=0,\qquad
                5NT-3N-4T^2+3T=0 .
\]
Subtract twice the first from the second to get
\(T(N+1)=3N\); hence \(N+1\ne0\).
The first polynomial times \((N+1)^2\) gives
\(3N(2N-1)(N-1)=0\).
The root \(N=1\) gives \(T=3/2\), contrary to \(D_0\ne0\).
Thus \(N=1/2,\ T=1\).
In particular \(f_4=-1/2,\ f_3=1/8\), and the
normalized raw front coefficients are
\[
        A_{21}=1,\quad A_{32}=1/8,\quad A_{43}=2,\quad
        A_{52}=a,\quad A_{53}=-8a/3,\quad A_{54}=a/3 .
\]
All adjacent edges through row 5 are nonzero.

## The sixth edge is live by a unique path

Row 6 is clean by the exact four-carrier count.
Write \(z=c_6,\ F=f_6,\ v=A_{65}\) in normalized
coordinates. On the already accumulated donor clocks
\(0,1/2,1\), the scalar cubic satisfies
\(c^3=(3/2)c^2-(1/2)c\).
The actual grade-four pure formula now has
\(Ac^3-c^4/4=\delta/2+(3/4+C/4)f\), and
\(Af=(1/2-C)f\).
At row 6 the first three clock moments and the \(Af\)
moment give
\[
       (z-1)(F-z^2(1-z))=0,\qquad
       2av=(1-z)(2F-z^2).                                \tag{1}
\]
For the second formula, solve the first two clock
moments for
\(A_{63}=2z^2-4z^3/3-8F/3\),
\(A_{64}=-z^2/2+2z^3/3+F/3\), since
\(A_{62}+A_{65}=F\).
Then \(Af=A_{63}/8-A_{64}/2+v a\) gives (1).

If \(v=0\), (1) forces \(z=0,1/2,1\).
At \(z=0,1/2\) the same actual expressions and the
row sum give the raw duplicates of the origin or
row 3. At \(z=1\), \(F=-1/2\) would duplicate row 4;
otherwise it is a distinct clean state at clock 1
from that row, with different \(f\).

But the *literal* degree-five chain on row 6 has only
one strict length-five path in its chronological
prefix:
\[
                    (A^5\mathbf1)_6
                  = A_{65}A_{54}A_{43}A_{32}A_{21}.
\]
Every off-path term would require a strict path of
length five without visiting all first six sites,
which is impossible. Thus \(v=0\) forces zero on row
6. On the two clean unit-clock rows 4 and 6 the same
pure formula \(c^5/120+P_2(c)f\), together with
\((A^5\mathbf1)_4=0\), forces nonzero at 6 because
their \(f\) values differ and \(1/120\ne0\).
This excludes the last \(v=0\) possibility.
Consequently \(v\ne0\); (1) now gives
\[
                    z\notin\{0,1/2,1\},\qquad
        f_6=z^2(1-z),\qquad
               aA_{65}=z^2(1-z)(1/2-z).
\]
All five front adjacent edges are live. These uses
of \(A^5\mathbf1\) pay grade exactly five, not a
higher-order output or a hypothesized dense width.

## Literal third through fifth carrier taps at the two ends

Return to ordinary scaling and put \(\beta=1-\theta\ne0\),
\(\bar r=A^\star s\). The exact low reverse chart at
original rows 17,16,15,14,13 has normalized clocks
\(0,1,1/2,1,1\) when scaled by \(\beta\).
It has the same grade-three/four formula just derived,
with carrier indicator \(s\) unchanged and \(f\)
replaced by the normalized \(\bar r\).
At any carrier,
\[
   ((A^\star)^2\mathbf1)_i=0,\quad
   ((A^\star)^3\mathbf1)_i=-\beta^2\bar r_i/6,\quad
   ((A^\star)^4\mathbf1)_i=\beta^3\bar r_i/12 .
\]
In fact \((A^\star)^2\mathbf1=Y^2/2-\beta^2s/2\);
the third formula follows on applying \(A^\star\)
and the cubic residual \(A^\star Y^2-Y^3/3\).
For the fourth use \(A^\star Y^3-Y^4/4\) and
\(A^\star\bar r=(\beta/2-Y)\bar r\).
Equivalently because \(bA^m=b\odot(A^\star)^m\mathbf1\),
\[
                     (bA^3)_i=-\frac{\beta^2}{6}b_i\bar r_i,
        \qquad         (bA^4)_i=\frac{\beta^3}{12}b_i\bar r_i
                 \quad\text{on carriers}.
\]
The same identities hold with the two directions
interchanged and \(\theta,r\) replacing \(\beta,\bar r\).
The grade-five common field \(E_5=\bar E_5\) restricts
to carrier values affine in \(r_i\).
Hence \((A^\star)^5\mathbf1\) vanishes on all
carriers: strictness gives its zeros at the two latest
carriers 13 and 16, where \(r\) is distinct.
By symmetry \(A^5\mathbf1\) also vanishes on all
carriers (use zeros at 2 and 5, with \(r_2=0,\ r_5\ne0\)).
Thus both actual fifth taps avoid all four carriers
and have live terminal edges at their twelfth slot.

These third/fourth tap identities do not exclude
either remaining \(r\)-value pattern by themselves:
testing the carrier-supported shift-three row against
\(E_5\) pays an affine carrier test, not a quadratic
one, and hence uses only the already compulsory
zeroth, first, and second scalar moments of \(r\) on
the carrier group. The next moment from a putative
\(s\odot r^{\odot2}\) input consumes grade \(2+6\),
which after shift three would need order twelve.

ERK11FourCarrierTapGate.lean checks the actual
six-slot chain, clean-plateau charge, and paid scalar
carrier eliminations. The rooted and support bridges
are the mathematical part above. This excludes the
original slot-six carrier subcase but not the full
four-carrier family.
