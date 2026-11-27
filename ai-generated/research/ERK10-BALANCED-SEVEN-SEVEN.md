# The literal 7|7 split of the balanced four-pair ERK10 branch

Continue the [fourteen-row equality analysis](ERK10-FOURTEEN-STAGE-EQUALITY.md).
Assume the actual all-live, independent \(d,Cd\), balanced fork.
There are four distinct dirty clocks, with two opposite-weight rows
at each, and six distinct clean Lobatto rows. The clean-stage
chronology is \(0,u,w,y,v,1\), with \(u,w,y,v\) a permutation
of the four internal Lobatto clocks, not assumed numerically sorted.
The all-live weighted transpose has full order ten and the same
numerical \(E_j\). The common \(F_4=d\mathcal P_{\le2}(c)\)
vanishes at all six clean sites. On dirty sites,
\(d=G(c)\) for the genuine quadratic \(G\).

**Results.** Every one of the four dirty pairs has one representative
in each of the physical seven-row halves. The literal middle
physical rows 7 and 8 are clean. The internal clean chronology is
therefore rows \(5\) or \(6\), \(7\), \(8\), \(9\) or \(10\).
There is also a new paid mixed primitive condition between the
two literal halves. This does not finish the balanced branch and
does not address the independent unbalanced nine/five charts.

All deductions below hold over characteristic zero. For paid fields
with \(10!\ne0\) the same argument uses the extra nonzero constants
19, 29, 31, 1213, including those already used in the balanced
branch. No sign, algebraic closedness or real assumption is used.

## Pair differences and exact clean-contact tests

Taking \(E_5=F_4^{\perp_B}\), orient a dirty pair \(i^-,i^+\)
arbitrarily for the moment, put \(\xi_i=c_{i^-}=c_{i^+}\), and
let \(\omega_i=b_{i^+}=-b_{i^-}\).
For any \(f\in E_5\) its four pair differences satisfy
\[
  \sum_i\omega_i G(\xi_i)\xi_i^k
                     (f_{i^+}-f_{i^-})=0,\qquad k=0,1,2.
\]
The Vandermonde row kernel is a line and its nonzero vectors
have no zero component. Moreover this line really occurs:
if all differences were always zero then \(E_5\) would be
contained in a space of dimension \(14-4=10\), contradiction.
In particular **each pair differs at grade five**, although
its two rows are identical on \(E_4=\mathcal P_{\le4}(c)+F_4\).

We need \(G\) nonzero at the clean sites. Its endpoint values
are already nonzero by the two primitive arguments in the prior
packet. For the finite interior test center the clock by
\(Z=2X-1\), let \(U=2u-1,V=2v-1\); both satisfy
\(J_4(Z)=21Z^4-14Z^2+1=0\). The four roots of \(J_4\) have
two distinct squared values, of sum \(2/3\) and product \(1/21\).
Normalize the centered \(G\) to be monic, with root sum \(S\)
and product \(P\). The two genuine primitive tests become
\[
 \begin{split}
 3U^2-(2+4S)U+1+2S+6P&=0,\\
 3V^2+(2-4S)V+1-2S+6P&=0.
 \end{split}                                                 \tag{1}
\]
The normalization is harmless because these tests are homogeneous
in \(G\), and both physical endpoint factors used in clearing
are nonzero.

If \(G(u)=0\), the first primitive says that the other physical
root is \(u/2\) (counting multiplicity). In centered units this
gives \(S=(3U-1)/2,\ P=U(U-1)/2\).
The reverse gate reduces to
\(3V^2+(4-6U)V+3U^2-6U+2=0\).
If \(V=-U\), this is \(2(3U-1)(2U-1)=0\); neither \(1/3\)
nor \(1/2\) is a root of \(J_4\).
Otherwise \(V^2=2/3-U^2\) gives \((4-6U)(1+V)=0\),
also impossible because \(V\ne-1\) and \(2/3\) is not
a root of \(J_4\). Reflection gives \(G(v)\ne0\).

For completeness the other two clean sites are not roots either.
If \(V=-U\), subtraction of (1) gives \(S=0\), since
\(2U\ne1\) by the previous numerical test. A hit at either
other Lobatto root would give \(P=U^2-2/3\) and hence
\(9U^2-2U-3=0\), excluded by the earlier Bézout constant 248.
If \(V\ne-U\), the two other Lobatto sites are \(-U,-V\).
By reflection it suffices to test a possible centered root
\(-U\). Write \(T\) for the other root of \(G\) in centered
coordinates, so \(S=T-U,\ P=-UT\). From (1) and
\(3V^2+3U^2=2\),
\[
 \begin{split}
 7U^2-4U+1+(2-10U)T&=0,\\
 3V^2+(2+4U)V+1+2U-(4V+2+6U)T&=0 .
 \end{split}
\]
Eliminating \(T\) gives \(r_0(U)+r_1(U)V=0\) with
\(r_0=18U^3-9U^2-7U+2,\ r_1=-3U^2-7U+2\).
Squaring and reducing by \(J_4(U)=0\) gives
\(483U^3-327U^2-43U+27=0\), with Bézout constant \(19408=16\cdot1213\)
against \(J_4\). This proves all the clean noncontacts.
The scalar companion checks these finite calculations; the
opposite-root Bézout is in the preceding packet.

## Why every pair crosses the physical halfway cut

Before the third clean stage there are only two clean labels
\(0,u\). The actual \(E_3=\mathcal P_{\le3}(c)+d\mathcal P_{\le1}(c)\)
can interpolate arbitrary values on those and on any of the four
dirty tagged states. To see this, first fit the dirty states
with a cubic (four distinct clocks or fewer), then add
\(\ell_1(c)(G(c)-d)\). This term vanishes on all dirty states
and can correct both clean coordinates, since \(G(0)G(u)\ne0\).
This reasoning also handles a numerical clock common to a
dirty and a clean tag.

If a physical dirty pair were repeated before the third clean
stage, then every grade-four vector on the literal prefix of
the later of those dirty rows could be matched by a grade-three
vector: both profiles are constant on equal tagged states.
Those pair rows already agree on \(E_4\), so their incoming
reads agree on \(E_3\) (applying \(A\) raises one grade).
By strictness they then agree on \(E_4\) inputs as well.
All other grade-five products preserve equality at the pair:
the nontrivial factors have grades at most four.
The pair would be equal on \(E_5\), contradiction.
Thus at most four dirty rows occur before the third clean row;
that third clean row is physical position at most 7.
Reflection puts the fourth clean row at position at least 8.
The first seven and last seven hence each contain exactly three
clean and four dirty rows.

Suppose there were a repeated dirty pair wholly in the first
seven. The first nonzero clean row \(u\) gives order four on
its predecessors after dividing its row and the preceding
matrix by \(u\). (Unary application to any grade at most three
is point exact at that row.) Thus at least four predecessors
are needed, so at least three dirty rows precede \(u\).
They are distinct by the earlier exclusion.
A repeat in the first half must be after the third clean row,
and only four dirty rows are available in that half. Its
complete chronology would have to be: clean origin, three
distinct dirty rows, clean \(u\), clean \(w\), repeated dirty
state at position 7.

If \(E_3\) is full on the first six tagged states of this
chronology, the same equality argument prevents the pair
from differing on \(E_5\). Otherwise its rank is five,
since it is full on the first five states as just proved.
Let \(K_D\) be the monic cubic of the three dirty nodes.
Choose the unique linear \(\ell\) with
\(\ell(0)=K_D(0)/G(0)\), \(\ell(u)=K_D(u)/G(u)\).
The genuine grade-three vector
\(K_D(c)-\ell(c)(G(c)-d)\) vanishes at the first five rows,
and would also vanish at the sixth by this rank assumption.
Its model \(K_D-G\ell\) is nonzero since \(G\) cannot divide
the monic product of three dirty clocks where \(G\) is nonzero.
Its three clean roots therefore give the model
\(\rho X(X-u)(X-w)\), \(\rho\ne0\).
Point-exact unary steps at \(u,w\), with zero actual inputs
before them, require simultaneously
\[
 0=\rho u^3(2w-u)/12=\rho w^3(2u-w)/12.
\]
As \(u,w\ne0\), the two requirements are incompatible.
There is therefore no intra-half dirty pair on the left,
and reflection excludes one on the right. This proves the
literal crossing claim.

## The two half aliases, clean seam and the paid mixed primitive

Let \(D(X)=\prod_{i=1}^4(X-\xi_i)\) be the monic hull of the four
dirty clocks. Each seven-row half sees all four dirty tags and
its own three clean tags. On either half, \(E_4\) restricts onto
all seven coordinates: first use a cubic to match the dirty
values, then use \(q_2(c)(G(c)-d)\) and the independent three
clean values to adjust the clean row data.
Consequently the two half-zero subspaces in \(E_4\) are lines.
In fact the literal left-zero vector is
\[
      V_L=D(c)-Q_L(c)(G(c)-d),
      \qquad P_L=D-GQ_L,
\]
where \(Q_L\) is the quadratic interpolant of \(D/G\) at
the three left clean clocks; \(P_L\) is its model.
The same formula gives \(V_R,P_R\) for the right half.
Both \(V_L,V_R\) are zero at **all** dirty rows, hence
supported on the three opposite clean sites. Their
nonzero models are anchored on their three own clean sites
and have the same nonzero remainder \(D\bmod G\).

Grade five contains the entire space of vectors supported on
the six clean coordinates, and models them by ordinary
degree-five interpolation at the six clean clocks. For any
individual six clean values, let \(P\) be their interpolant,
then choose a cubic \(Q\) canceling \(P(c)\) by \(d Q(c)\)
on the four dirty clocks; this exhibits the actual numerical
vector with that model. Separation proves model uniqueness.
In fact the subspace of \(E_5\) having equal values on each
dirty pair is exactly \(\mathcal P_{\le5}(c)+d\mathcal P_{\le3}(c)\)
by the same interpolation; both orientation model maps agree
there. This is an explicit kernel, not just a count.

The genuine unary \(A V_L\in E_5\) is zero on the left half.
If any of its right dirty coordinates were zero, all its pair
differences would vanish by the Vandermonde line, so it would
be supported entirely on clean rows. Its degree-five model
\(J P_L\) would then be zero at the three left clean clocks
by the just-proved interpolation. Its derivative \(P_L\) is
already zero there, giving six zeros with multiplicity despite
degree at most five. Thus \(A V_L\) has nonzero values on all
four right dirty rows. By strictness \(A V_L\) is zero at row 8
(the first physical row after the left half); row 8 must
therefore be clean. Reflecting this proof forces row 7 clean.
The order-four predecessor bound then gives \(u\) at row
5 or 6, and \(v\) at row 9 or 10. For example if \(v\) is row
10, row 9 is dirty and its nonzero unary read must be the
literal tap \(A_{9,8}V_L(8)\ne0\).

Finally \(V_R\) is supported on the left, whereas \(A V_L\)
is supported on the right. Their paid rooted product of
grades 4 and 5 gives the nontrivial scalar condition
\[
                     \int_0^1 (J P_L)(X)P_R(X)\,dX=0.       \tag{2}
\]
Write \(T_L(X)=X(X-u)(X-w)\) and
\(T_R(X)=(X-1)(X-y)(X-v)\).
The pair \(P_L,P_R\) is uniquely determined by its
common residue \(D\bmod G\): each is a linear multiple of its
respective \(T_L,T_R\), and those are units modulo \(G\) by
the noncontact test. Thus (2) is an explicit binary quadratic
test on a nonzero residue, for each finite chronological
ordering \(u,w,y,v\). This reduction does not assume the
unknown dirty hull is arbitrary, nor claim (2) is sufficient
for a tableau. The unbalanced case is separate.

The arithmetic companion `ERK10BalancedHalfGate.lean` checks
the contact identities and the two primitive scalar contradiction.
The actual profile spaces, strict reads and rooted mixed product
are justified above mathematically, not as a complete native
Lean lower theorem.
