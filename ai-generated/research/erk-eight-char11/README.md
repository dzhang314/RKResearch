# ERK order eight: exclusion in the exceptional characteristic 11

**Theorem (mathematical proof).** Over every field of characteristic 11,
including arbitrary extensions, a strictly explicit method of order at
least eight requires at least eleven stages. Combined with the
[outside-11 proof](../erk-eight-finite/README.md), stage padding, and
coefficient specialization, eleven is the minimum over **every nontrivial
commutative ring in which \(8!\) is a unit**. A nontrivial ring without
that unit admits no order-eight method. The separate eleven-stage
factorial-localized tableau is a native, exact-order upper certificate.

**Native boundary.** ERK8CharElevenCensus checks the unconditional
one-/four-/five-/seven-off split from literal HasOrder. Its two nontrivial
clean counts are included. ERK8CharElevenScalar checks the final scalar
contradictions over an arbitrary field with \(11=0\). The preceding
paid packet verifies the raw four-off physical bridge. The
finite-chart reductions and the full one-off proof are mathematical
source proofs, not an end-to-end native lower theorem. The old
conditional finite-field searches are not used in this proof.

## 1. Paid census and the degenerate head

Work at width ten over \(K\) with \(11=0\). Write \(A\) for the strict
lower tableau, \(\boldsymbol b\) for the signed weights,
\(\boldsymbol c=A\boldsymbol 1\) for the clocks, and
\(\boldsymbol g=A\boldsymbol c-\boldsymbol c^2/2\). Vector powers are
componentwise. The graded tree and defect spaces are \(E_j,F_j\).
A clean tag has \(g_i=0\), an off tag has \(g_i\ne0\); different tags
at one clock remain separate. An off or clean *clock count* below
counts the distinct clocks in the indicated branch, not the physical
rows.

The actual horizon gives \(F_3,F_4\) dimensions 2,3, \(E_4\) dimension
8, \(E_5\) dimension at most 9, and a live terminal coordinate at clock
1. These are paid field facts. The native count excludes 0,2,3 off
using the actual seed and the paid outgoing and incoming Hermite gains.
Whenever there are at least four off, their amplitudes fit a nonzero
polynomial \(P\) of degree at most two, and
\[
 F_3=\boldsymbol g\,\mathbb P_1(\boldsymbol c),\qquad
 F_4=\boldsymbol g\,\mathbb P_2(\boldsymbol c).
\]
If the off count is at most six, the off weights cancel in each tag
using the six degree-\(0,\ldots,5\) weighted probes as needed. In
that event there are exactly five clean tags (anchored Cauchy and
tag-rank argument). Hence six off are impossible by width.

If there are at least seven off, width leaves at most three clean
tags. A clean count at most two would make
\(P\cdot\operatorname{hull}(\mathrm{clean})\) a nonzero polynomial of
degree at most four, zero at the origin, with four zero paid probes
\(k=0,1,2,3\). Indeed its evaluation equals
\(\boldsymbol g\operatorname{hull}(\mathrm{clean})(\boldsymbol c)\),
of defect grade \(2+\#\mathrm{clean}\); the probe cost is
\(k+\#\mathrm{clean}+3\le8\). The paid anchored Cauchy test excludes
it. Thus there are exactly seven off and three clean in this case.
There is no alternative from a smaller rank or a zero fitted
amplitude: the actual low ranks already force this fitted nonzero
\(P\). In summary the native literal width-ten split is
\[
 1\text{ off}\quad\text{or}\quad
 (4,5),\ (5,5),\ (7,3)
 \text{ for the (off,clean) counts}.
\]
The one-off proof and its paid guard audit are in the outside-11
packet, §2. Its proof uses only the paid primes \(2,3,5,7\), not 11.

Set \(h=6=1/2\), \(q(X)=X^2-X+8\), and
\(L(X)=(X-h)q(X)\), the paid Lobatto cubic. In the five-off and
seven-off cases there are ten tags, so each has exactly one physical
representative. The five-off terminal coordinate is clean: otherwise
it would be off with nonzero weight, contrary to cancellation in its
singleton tag. Since the clean endpoints are 0 and 1, the paid beta
decoder forces the clean hull \(X(X-1)L\) in this case. The actual
terminal-coordinate profile then has clean part proportional to
\(XL\), and its off polynomial \(Q+P R_2\), of degree at most four,
vanishes at five distinct off clocks. Hence \(P\) divides \(XL\) and
has degree exactly two. The first nonzero clean row tests
\(P,XP\): if \(P(0)=0\), these two equations give \(P=0\) by the
paid elimination. Thus \(P\) divides \(L\).

In the seven-off case the terminal must also be clean: were it off,
its endpoint profile would have off polynomial of degree at most four
vanishing at all six other off clocks and nonzero at the terminal,
impossible. The three clean clocks are \(0,u,1\). The weighted
probes of \(P X(X-1)(X-u)\) at \(k=0,1,2\) vanish since this
physical input is \(\boldsymbol g\) times the three-clean hull.
The budget \(k+3+3\le8\) is paid. The beta decoder gives
\((X-u)P\) a nonzero multiple of \(L\), again with \(P\) quadratic.

In both cases the omitted linear factor is \(X-u\). At the first
physical clean \(u\)-row, all earlier clean clocks are either zero
or roots of \(P\); 1 is the unique terminal. Therefore the off
input \(\boldsymbol c\,\boldsymbol g\) agrees with \(XP(\boldsymbol c)\)
on the physical prefix, and its \(A\)-image vanishes there in \(F_4\).
The paid primitive of \(XP\) evaluated at \(u\) is zero. The
omitted-factor equations from the paid census, *before* the use of
\(11\ne0\), are
\[
 14u^3-21u^2+9u-1=0,\qquad 91u^2-105u+27=0.
\]
In characteristic 11 the second factors as \((u-6)(3u+1)\).
At the other possible root \(u=7\) the first evaluates to 7.
Thus in both branches \(u=h\) and \(P=\Theta q\), \(\Theta\ne0\).
The five-off clean grid has \(0,h,x,z,1\), with \(x,z\) the two
roots of \(q\); the seven-off clean grid has \(0,h,1\).

For the four-off branch the paid native physical bridge gives the
five clean clocks \(0,h_{\rm first},x_{\rm late},z_{\rm late},1\),
with the three interior roots of \(L\) and a unique repeated tag
last appearing at physical row 8. If the first nonzero clean clock
is a quadratic root rather than \(h\), the ordinary four-off scalar
closure from the outside-11 proof remains valid: replay.py checks all
four such orientations in \(\mathbb F_{11}[X]/q\), with every
required clean inversion, quadratic leading coefficient and
determinant nonzero. The values in every extension are the images
of these same roots and scalars. If the first clean clock is \(h\),
the raw shape equation has \(E=0\) in that orientation, giving
\(\kappa(x/3-h/4)=0\), where \(x\) is one of the two quadratic roots.
But \(q\) is irreducible over the prime field, so \(x/3-h/4\ne0\).
Thus \(\kappa=0\), and the raw head is \(P=\Theta q\), \(\Theta\ne0\).
Here and below \(x,z\), if present, denote the chronological
quadratic clean pair and obey \(x+z=1,\ xz=8\).

## 2. Common strict early prefixes when the head is \(\Theta q\)

All paid fields here have \(2,3,4,5,7,8\) as units. On any clean
receiver the degree-\(\le3\) pure primitives are exact because
their defects lie in \(F_4\). More generally the clean-sender
action on \(XP\) there equals \(I(XP)\), where \(I\) is the
zero-constant primitive: the off-sender input is
\(\boldsymbol c\,\boldsymbol g\) and its image is in \(F_4\).
If \(x\) or \(z\) were the first nonzero clean clock in the five-off
case, the prior clean inputs would have only clock zero, so
\(I(XP)\) would vanish there. Yet \(I(Xq)\equiv 3+9X\pmod q\),
nonzero at either root of the irreducible quadratic. Thus \(h\)
is the first nonzero clean in all three degenerate branches.
The first such row requires three preceding off clocks: with
at most two, the two vanishing inputs \(\boldsymbol g\) and
\(\boldsymbol c\,\boldsymbol g\) would force all off taps zero by
Vandermonde, contradicting \(A\boldsymbol c\) at \(h\).
The only prior clean is the origin.

For consecutive early off clocks \(a,b,d,e\), write \(N_j\) for the
hull of their first \(j\). For a monic hull \(D\) of \(m\) off clocks
define
\[
 {\cal L}_D(G)=\sum_{o:D(o)=0}\frac{G(o)}{q(o)D'(o)} .
\]
This is the coefficient of degree \(m-1\) in the interpolant \(U\)
of \(G/q\) at its nodes. For \(\deg G\le m\),
\(qU-G=D V\) with \(\deg V\le1\). Indeed \(qU-G\) has degree at most
\(m+1\); coefficient \(m+1\) is the coefficient of degree \(m-1\)
in \(U\). Reducing modulo \(q\) gives the exact identity
\[
 {\cal L}_D(G)=-[X]\bigl(D^{-1}G\bmod q\bigr).
 \tag{1}
\]
Here \(D\) is a unit in \(K[X]/q\) since every off node has
\(q(o)\ne0\). This quotient need not be a field. Divided differences
for \(G/P\) instead have the common scale \(1/\Theta\), which
cancels from all the following residue comparisons.

### Four initial off clocks before any nonzero clean: impossible

Indeed suppose \(a,b,d,e\) all occur before \(h\), so only origin
and earlier off clocks can enter those rows. The normalized
off-only map of a polynomial \(f\) is \(A(\boldsymbol g
f(\boldsymbol c))/\boldsymbol g\) on the off rows. By the two
paid bands for \(A\boldsymbol g\) and
\(A(\boldsymbol c\,\boldsymbol g)\), and by strict causality,
it sends \(N_0\) to \(\beta N_1\), \(N_1\) to \(\gamma N_2\),
\(N_2\) to \(\delta N_3\), and \(N_3\) to zero on these
four clocks. No nonvanishing of these three scalars is assumed.
Put \(L_r={\cal L}_{N_4}(X^r)\). The paid pure primitive
corrections have degree at most \(r-2\) after division by
\(\boldsymbol g\), for the input power \(r-1\), \(r=2,3,4\).
Their top cubic contribution is zero. Comparison of that
top coefficient gives
\[
 \delta(L_r-eL_{r-1})=L_r/r,\qquad r=2,3,4.       \tag{2}
\]
The three-node coefficient \(L_r-eL_{r-1}\) arises by deleting
the final off summand, since \(N_4=N_3(X-e)\).

The \(3\times3\) augmented determinant of (2), multiplied by
12, factors as
\((L_1L_3-L_2^2)(L_4-16L_2)\), by the recurrence
\(8L_j-L_{j+1}+L_{j+2}=0\) for \(j=0,1,2\), obtained by
multiplying the input by \(q\) and taking top cubic coefficients.
The first factor is nonzero: by (1) its two-by-two matrix is the
pairing extracting the linear coefficient of \(X N_4^{-1}\)
times a product in \(K[X]/q\), in basis \(1,X\), up to an
irrelevant sign. That linear-coefficient pairing is nondegenerate
(multiply a nonzero linear term by 1, or a nonzero constant by
\(X\)); \(X N_4^{-1}\) is a unit since \(X(1-X)=8\) modulo \(q\).
Consequently \(L_4=5L_2\) in this field, and the recurrence gives
\[
 (L_0,L_1,L_2,L_3,L_4)=(10,4,1,2,5)L_2,\qquad L_2\ne0.
\]
The first two equations of (2) now give
\(\delta=-1\) and \(e=-1\). Moreover (1) for \(L_0,L_1\) gives
\(N_4^{-1}\propto X+6\) modulo \(q\), so \(N_4\propto7-X\)
there, and \(N_3\propto X+2\) after removing \(X+1\).

Already at the third off row the exact \(N_2\) coefficients of
\(A\boldsymbol c\) and \(A\boldsymbol c^2\) give
\[
 \gamma{\cal L}_{N_2}(X)={\cal L}_{N_3}(X^2)/2,\qquad
 \gamma{\cal L}_{N_2}(X^2)={\cal L}_{N_3}(X^3)/3 .
\]
The remainder \(N_3^{-1}\propto X-3\) gives
\({\cal L}_{N_3}(X^2)={\cal L}_{N_3}(1)\ne0\),
\({\cal L}_{N_3}(X^3)=6{\cal L}_{N_3}(1)\).
So \({\cal L}_{N_2}(X^2)=4{\cal L}_{N_2}(X)\).
With two nodes \(a,b\) this is the equality of
\((X^2-4X)/q(X)\) at \(a,b\); clearing and cancelling \(a-b\)
gives \(3ab+8(a+b)+1=0\). In particular \(ab=a+b+7\).
Now put \(s=a+b,p=ab\). Expansion of
\(N_3\propto X+2\bmod q\) gives
\[
 -5+10s-2p+d(10-p-2s)=0,
\]
which becomes \(3(1-s)(1+d)=0\).
Since \(d\ne e=-1\), this forces \(s=1,p=8\).
Thus \(N_2=q\), contradicting \(q(a)\ne0\).
This is the native scalar impossible_first_clean_five_prefix.
In particular \(h\) is exactly physical row 4 in the remaining
degenerate branches.

### With \(h\) at row 4, the fourth off clock is 2

The clean \(h\)-row taps into the first three offs (and origin).
They annihilate \(\boldsymbol g,\boldsymbol c\,\boldsymbol g\).
The two-by-three Vandermonde kernel on the corresponding
\(A_{h,o}g(o)\) has coefficients proportional to \(1/N_3'(o)\).
The three pure targets are \(h^2/2,h^3/3,h^4/4=(7,6,5)\).
So \({\cal L}_{N_3}(X),{\cal L}_{N_3}(X^2),
{\cal L}_{N_3}(X^3)\) are a nonzero common multiple of
\((7,6,5)\). The recurrence at \(j=0\) makes
\({\cal L}_{N_3}(1)={\cal L}_{N_3}(X)\ne0\).
By (1), \(N_3^{-1}\propto X\), so \(N_3\propto1-X\bmod q\).

Use the sentinel
\[
 C(X)=X(X-h)(X+8),\qquad C\bmod q=9(1-X),\qquad
 I C\bmod q=10+7X .
\]
Choose \(\mu\ne0\) so \(C\equiv\mu N_3\bmod q\), and put
\(S=(\mu N_3-C)/P\), of degree at most one.
The actual input \(\boldsymbol v=C(\boldsymbol c)+
\boldsymbol g S(\boldsymbol c)\) vanishes on the origin, the
three early offs and the clean \(h\). If a clean quadratic
clock were next, strictness would give \(A\boldsymbol v=0\)
there, contradicting the actual clean primitive \(I C\) (its
linear remainder cannot vanish at a quadratic root outside
the prime field). Thus the next nonzero slot is the fourth
off \(e\). On all off rows \(A\boldsymbol v\) has a polynomial
profile \(I C+P T_2\), with \(\deg T_2\le2\), from the same paid
bands and primitive columns. On the first four off rows it
vanishes by strictness. Its degree is at most four and
its remainder \(10+7X\) nonzero, so it is a nonzero scalar
multiple of \(N_3(X-e)\). Since
\[
 (1-X)(X-e)\equiv (8-e)+eX \pmod q ,
\]
remainder comparison gives \(7(8-e)=10e\), or \(e=2\).
We will use the resulting identity
\[
 N_4\bmod q\ \propto\ 6+2X .
 \tag{3}
\]

## 3. Four-off: the repeated-row late reverse ratio

Here the paid physical structure has clean \(x,z\) respectively
at physical rows 6 and 7, terminal at 9, and unique repeated
tag \(i,8\). Define \(\boldsymbol r=\boldsymbol e_8-
\boldsymbol e_i\), \(\eta=1-c_8\), and
\(\boldsymbol\Delta=A^{\mathsf T}\boldsymbol r\).
The paid repeat structure gives \(b_8\eta\ne0\), the first
reflected row \(J_1=-b_8\eta^2\boldsymbol r\), and
\[
 E_4^\perp=K\boldsymbol r+K\boldsymbol\Delta,\qquad
 J_2-\eta J_1=\xi\boldsymbol\Delta .
\]
The latter follows also by taking the value at row 8: strictness
makes \(\Delta_8=0\). The four off tag aggregates of
\(\boldsymbol\Delta\) are all nonzero as established in the paid
repeat bridge.

The vectors \(P(\boldsymbol c)\boldsymbol c^j\) and the off
defects \(\boldsymbol g\,\boldsymbol c^j\), \(j=0,1,2\), are in
\(E_4\). Subtracting their pairings with \(\boldsymbol\Delta\)
gives the three weighted clean equations; since \(P(x)=P(z)=0\)
and \(P(0),P(h),P(1)\ne0\), they force the three exceptional
clean tag aggregates at \(0,h,1\) to vanish. Thus the projected
difference on the six distinct remaining clocks (four off and
\(x,z\)) kills the pure powers through four. It is a nonzero
multiple of the reciprocal derivatives of \(N_4 q\) there;
this is the one-dimensional Vandermonde kernel. In particular
\[
 \overline\Delta_x/\overline\Delta_z=-N_4(z)/N_4(x).
 \tag{4}
\]

For clarity, the actual late reverse calculation also works
if the earlier repeat is itself clean. Set \(y_u=1-u\).
For each physical sender tag, sum its \(J_1,J_2\) coordinates.
Decompose the physical weighted receiver sum into the weighted
first occurrences (weights equal to tag aggregates) and the
extra term \(b_8\eta^k\overline{\boldsymbol\Delta}\) for the \(k\)-th
reflected row. This holds because the two repeated receivers have
the same clock. Thus no column is removed or merged. All off
aggregate weights are zero and the terminal has \(y=0\). Write
\(W_x,W_z\) for the clean masses; they equal 4 at both nodes by
the paid five-node scalar quadrature. For sender \(z\), the two
literal equations are
\[
 b_8\eta\,\overline\Delta_z=W_z y_z^2/2,\qquad
 (b_8\eta^2-\xi/3)\overline\Delta_z=W_z y_z^3/3.
\]
Hence \(b_8\eta^2-\xi/3=(2/3)b_8\eta y_z\).
For sender \(x\), the only later nonterminal first-occurrence
receiver with nonzero aggregate weight is \(z\). Calling its
aggregated tap \(a\), the two equations are
\[
 W_z y_z a + b_8\eta\,\overline\Delta_x = W_x y_x^2/2,\qquad
 W_z y_z^2 a + (2/3)b_8\eta y_z\,\overline\Delta_x = W_x y_x^3/3 .
\]
Eliminating \(a\) and using \(y_x=z,y_z=x,W_x=W_z\) gives
\(\overline\Delta_x/\overline\Delta_z=z^2(3x-2z)/x^3\).
Together with (3) and (4), this would give
\[
 (6+2z)x^3+(6+2x)z^2(3x-2z)=0.                \tag{5}
\]
The two products \((6+2x)z^2=(6+2z)x^2=7\) are exact in this
quadratic algebra, so (5) reduces to \(14(2x-z)=0\).
This is impossible: \(z=2x\) would give \(x=1/3=4\), not a
root of \(q\). This is the native scalar impossible_four_late.

## 4. A common seven-clock tail payment

In the five-off and seven-off branches let \(B\) be the ordered list
of seven physical stages outside the exceptional clean stages
\(0,h,1\). In five-off it comprises the five off and \(x,z\); in
seven-off it is all the off. Its clocks \(t_1,\ldots,t_7\) are
distinct: neither root of \(q\) can be an off clock. The pure
polynomial vector \(P(\boldsymbol c)-\boldsymbol g\) is supported
exactly on the three exceptional clean stages. Multiplying by
\(1,\boldsymbol c,\boldsymbol c^2\) gives all their coordinate
vectors by a three-site Vandermonde with nonzero \(P(0),P(h),P(1)\).
These coordinates belong to \(E_4\). Thus \(E_4\) contains arbitrary
values on the exceptions and degree-at-most-four polynomials on
\(B\); this has dimension \(3+5=8\), so it is exactly \(E_4\).
Likewise \(E_5\) is arbitrary on the exceptions and degree at most
five on \(B\), by the dimension \(3+6=9\) and the reverse cap.

Let \(D_B\) be the hull of the seven \(B\) clocks and put
\(r_i=1/D_B'(t_i)\) on \(B\), zero on the exceptions. It spans
\(E_5^\perp\); \(E_4^\perp\) is spanned by
\(\boldsymbol r,\boldsymbol c\,\boldsymbol r\).
In particular \(J_1=\rho\boldsymbol r\) and \(J_2/r_i\) is affine
in \(t_i\) on \(B\). The scalar \(\rho\ne0\): the reflected
first moment is \(1/2\), so there is a last physical stage with
\(b_i(1-c_i)\ne0\), at which the defining \(J_1\) has nonzero
value \(-b_i(1-c_i)^2\).

By §2, the first four \(B\) clocks are the four initial off
clocks. The polynomial \(N_4\) of (3) vanishes at all four.
Take the actual vector \(\boldsymbol v\) equal to \(N_4(t_i)\)
on \(B\) and zero on the exceptions. It belongs to \(E_4\).
Its \(A\)-image vanishes before or at the first five \(B\) rows
and at the clean 0 and \(h\), by strictness. The terminal row,
if nonzero, has no reflected contribution and has \(r=0\).
Since \(A\boldsymbol v\in E_5\), write its last two \(B\)-entries as
\(r_6 (A\boldsymbol v)_6=u_0\),
\(r_7 (A\boldsymbol v)_7=-u_0\),
where the indexes here refer to positions in \(B\).

Set \(y_i=1-t_i\), \(m_i=b_i/r_i\) on \(B\),
and \(F(X)=\prod_{i=5}^7(X-t_i)\). The reflected
payments \(J_1,J_2\in E_4^\perp\), paired with
\(\boldsymbol v\), give the two equations
\[
\begin{split}
 2u_0(m_6y_6-m_7y_7)&=\mathcal B_2,\\
 3u_0(m_6y_6^2-m_7y_7^2)&=\mathcal B_3,\qquad
 \mathcal B_k=\sum_{i=5}^7 \frac{m_i y_i^k}{F'(t_i)} .
\end{split} 
\]
The \(N_4\) in the right side is cancelled against the identical
factor in \(D_B'(t_i)\), and all reflected powers of the physical
terminal vanish. Eliminating \(u_0\) without dividing by either
parenthesis gives the common tail test
\[
 3(m_6 y_6^2-m_7y_7^2)\mathcal B_2
 -2(m_6y_6-m_7y_7)\mathcal B_3=0 .
 \tag{6}
\]

## 5. Five-off: both possible late placements are impossible

All five off weights vanish because their tags are singleton.
The clean weights on \(0,h,x,z,1\) respectively are
\(5,5,4,4,5\), either by the actual five distinct moment equations
or by substituting these weights (replay.py checks orders 0–7).
Both \(x,z\) occur after \(h\). Name the later one \(z\).
Since \(J_1\) is nonzero at every \(B\) coordinate, no \(B\) row
can follow \(z\): such a later off row would have zero weight
and no later nonterminal receiver with nonzero output weight.
Thus \(z=t_7\).

At an off row strictly between \(x,z\), the only nonterminal
receiver appearing in \(J_1,J_2\) is \(z\); the off weight is
zero. Hence \(J_2/r_i=(3/2)y_z\rho\) at every such off clock.
At \(z\) it instead equals \(y_z\rho\), nonzero and different.
The affine profile of \(J_2/r\) allows at most one such off
clock. Therefore \(x=t_5\) or \(x=t_6\).

If \(x=t_5\), the sixth \(B\) weight is zero and the seventh is
nonzero. Equation (6) becomes \(3y_z\mathcal B_2-2\mathcal B_3=0\).
Only \(x,z\) contribute to these moments, and their equal weights
give (5) again, with the same \(N_4\) remainder (3). Impossible.

If \(x=t_6\), let \(f=t_5\) be the fifth off. Write
\(D_x=6+2x,D_z=6+2z\) for the scaled \(N_4\) values, and
\(U=D_xz^2,V=D_zx^2\). Both \(U,V\) equal 7.
Since
\[
 m_x=4N_4(x)(x-f)(x-z),\quad
 m_z=4N_4(z)(z-f)(z-x),\quad
 \mathcal B_k=4\{N_4(x)z^k+N_4(z)x^k\},
\]
the common nonzero scale and the factor \(x-z\) cancel in (6).
It is exactly
\[
 3[U(x-f)+V(z-f)](U+V)
 -2[D_x z(x-f)+D_z x(z-f)](Uz+Vx)=0 .
\]
Using \(D_x z=5x,D_z x=5z\), \(x^2+z^2=7\), this equals
\(2-f=0\). The fifth off clock would repeat the fourth off \(2\),
contradicting distinctness. This is the native scalar fifth_off_eq_two.

## 6. Seven-off: the paid weighted tail also repeats 2

Here \(D_B=D_7\) is the hull of all the off clocks. The six
paid probes of \(\boldsymbol g\,\boldsymbol c^j\), \(j=0,\ldots,5\),
give
\[
 b_i q(t_i)=\lambda/D_7'(t_i) \quad(i\in B)
\]
by the \(6\times7\) Vandermonde kernel. The cost is exactly
\(j+3\le8\), and \(q(t_i)\ne0\) at all off sites. If \(\lambda=0\)
all the off weights vanish (not merely some); then the whole
quadrature is supported at \(0,h,1\). But the literal order-eight
moment of \(X\,L_0(X)\), \(L_0=X(X-h)(X-1)\), would vanish
at these clocks, while its formal integral is
\(-1/120=1\) in characteristic 11. This contradiction proves
\(\lambda\ne0\) and in particular all seven off weights nonzero.

The ordinary paid quadrature of \(L_0\) itself has value zero.
Its clean contribution is zero, so
\({\cal L}_{D_7}(L_0)=0\) by the weight law and nonzero \(\lambda\).
The \(m=7,\deg L_0=3\) instance of (1) shows
\(D_7^{-1}L_0\bmod q\) is constant. It is nonzero since \(D_7\)
and \(L_0\) are units modulo \(q\); \(q\) vanishes at none of
\(0,h,1\). Thus
\[
 D_7\bmod q\propto L_0\bmod q=4+3X,\qquad
 F\bmod q\propto1+7X ,
\]
the second by \(D_7=N_4F\), (3) and
\((6+2X)(1+7X)\equiv4+3X\bmod q\).
Moreover \(F^{-1}\) is proportional to \(X+2\), since
\((1+7X)(X+2)\equiv1\). These identities do not assume \(q\)
splits in \(K\).

In (6), \(m_i=\lambda/q(t_i)\). Thus
\(\mathcal B_k=\lambda\,{\cal L}_F((1-X)^k)\) for \(k=2,3\).
Both are paid literal tail expressions, evaluated by the
\(m=3,\deg(1-X)^k\le3\) instance of (1), i.e. from coefficient
4 of the polynomial division. The quadratic residues
\(-[X]((X+2)(1-X)^k\bmod q)\) for \(k=0,1,2,3\) are
\(10,2,10,5\). Hence \(\mathcal B_2\ne0\) and
\(\mathcal B_3/\mathcal B_2=1/2\). Writing \(u=t_6,v=t_7\),
(6) therefore implies
\[
 \frac{3(1-u)^2-(1-u)}{q(u)}=
 \frac{3(1-v)^2-(1-v)}{q(v)} .
\]
Cross multiplication and cancellation of \(u-v\ne0\) and
the unit 2 give \(uv=8\) (native scalar high_tail_product).
Their sum \(s=u+v\) cannot equal 1: otherwise \(u,v\) would be
roots of \(q\). For \(f=t_5\), the last-three hull now satisfies
\[
 F=(X-f)(X^2-sX+8)
 \equiv (1-s)((1-f)X-8)\pmod q .
\]
Since \(F\bmod q\) is proportional to \(1+7X\), comparison gives
\((1-f)/(-8)=7\), hence \(f=2\) (native high_fifth_eq_two).
Again this repeats the fourth off clock 2, contradiction.

## 7. Conclusion, ring domain and verification

The surviving count split has no admissible branch in
characteristic 11. No narrower-field assumption was used.
Actual zero padding excludes width below ten as well.
The outside-11 paper proof covers every other paid field.
For any nontrivial commutative ring \(R\), its maximal residue field
preserves the reviewed polynomial order conditions and strictness
under the unital map; if a method exists the bush conditions make
\(8!\) invertible in \(R\) and in the residue field. The field
exclusion therefore rules out ten or fewer stages over \(R\).
The exact eleven-stage factorial-localized tableau then gives
the claimed minimum on the entire admissible ring domain.

With Lean 4.36.0 and matching mathlib, compile
ERK8CharElevenScalar then ERK8CharElevenCensus, using the earlier
ERK8PaidLobatto and ERK8PaidCensus modules. The printed proofs use
only standard axioms; the complete mathematical theorem above is not
a native endpoint. Run the exact arithmetic replay with:

    python3 replay.py
