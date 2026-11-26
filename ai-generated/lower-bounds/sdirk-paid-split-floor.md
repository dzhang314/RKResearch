# The split-run stage floor over every paid characteristic

**Theorem.** Let \(R\) be a nontrivial commutative ring, and let a
triangular RK tableau with \(s\) physical stages and a common
diagonal \(\gamma\in R\) satisfy the literal denominator-cleared
rooted order conditions through \(p\), where \(p\ge11\).
Then \(s\ge p+1\).

There is no Schur, resultant, diagonal-unit, sign, or reality
hypothesis. This is a lower bound, not attainment or a statement
about differing diagonals. In particular it does not treat the
surplus-stage branch \(s=p+1\).

The order-\(d\) bush gives
\[
 (d:R)\bigl(\mathbf b\cdot\mathbf c^{\odot(d-1)}\bigr)=1
                    \qquad (1\le d\le p).
\]
All these integer casts are units; coefficient mapping to any
maximal residue field preserves the literal order conditions
and the stage count. It is enough to prove the theorem over
fields having the paid integer units. Use throughout the
bounded clock model and the integral tall recurrence from the
characteristic-transfer note. In particular, all polynomials
in the model have the degree budget required by the word under
test, not unrestricted antiderivatives in positive characteristic.

Write \(B=A-\gamma I\), \(\mathbf c=A\mathbf 1\), and
\(\lambda_j=\mathbf b\cdot(B^j\mathbf 1)\) when \(j+1\le p\).
The zero-diagonal equality rectangle already gives \(s\ge p+1\)
for \(p\ge5\). Now suppose \(\gamma\ne0\) and \(s\le p\).
Strict nilpotence and the paid consecutive-zero tall recurrence
leave only \(s=p-1\) or \(s=p\).
Write \(L=\lambda_{s-1}\).

## Paid scalar and clock tools

In a cyclic case \(L\ne0\), use effective size \(m=s\) and top
value \(L_*=L\) below. We will also use \(m=s-1\) and
\(L_*=\lambda_{s-2}\) in an explicitly identified noncyclic case.
For an arithmetic step \(\delta\) set
\[
 t=\delta/\gamma,\qquad
 m_j=\gamma^j\lambda_{m-1-j}/L_*,\quad (0\le j\le m-1),
 \qquad \mu(y^j)=m_j,\qquad \xi=\gamma^{-1}.
\]
The formal internal gap marks of counts 1, 2, and 3 have the
polynomials \(F_1,F_2,F_3\) of the sealed split-run proof, with
\[
 F_1=1+(2-t)y+y^2,\qquad
 F_2=(1+y)^3-\tfrac32 t y(1+y)^2+t^2 y^2 .
\]
The fixed-quadratic recurrence obstruction used below is the following:
\(g=F_1-\mu(F_1)\) cannot satisfy
\(\mu(gy^k)=0\) for \(0\le k\le3\). Such equations would make the
monic quadratic \(g\) give a constant recurrence through \(m_5\),
contradicting the four paid rows
\[
 (m-k)m_k=(\xi-2(m-1-k))m_{k+1}-(m-2-k)m_{k+2},
                                \qquad 0\le k\le3.
\]
For the characteristic check, factor the constant quadratic after
extension to an algebraic closure. A geometric mode \(r^k\) has
residual \(r^k\) times an affine polynomial in \(k\) with slope
\(-(1+r)^2\) and value \(\xi\ne0\) at \(r=-1\).
For two distinct nonzero roots the residual has a monic order-four
recurrence and its first four zeros kill both independent
exponential-affine components. For a repeated nonzero root the
divided residual is quadratic in \(k\); its first three zeros
and the same slope/value calculation kill the two coefficients.
A zero root leaves at most one geometric mode from \(k=1\) on;
rows 1 and 2 kill it, or row 1 kills \(m_1\) if both roots vanish.
Row 0 then contradicts \(m_0=1\). This uses only field pivots,
the distinct indices \(0,1,2\), and paid \(m,m-1\).

In the cyclic degenerate rectangle, using its literal clock slope
\(\delta=-E/D\), the identities \(D\ne0\) and \(\Delta=0\)
give
\[
 {\cal D}\coloneqq m_2-m_1^2\ne0,\qquad
 {\cal U}\coloneqq m_1m_2-m_3=(2-t){\cal D},\qquad
 m_4-m_2^2=(2-t){\cal U}.
\]
Thus \(\mu(g)=\mu(gy)=\mu(gy^2)=0\).
At \(t\ne2/3\), any valid calibration of the product \(F_1F_2\)
adds \(\mu(gy^3)=0\), since its cubic probe \(F_2\) has
coefficient \(1-3t/2\). One run of six suffices for that calibration
by the ordinary consecutive marks of counts 1 and 2.

## 1. Saturation: \(s=p-1\)

Here \(s\ge10\), \(\lambda_s=0\) and \(L\ne0\) by the paid
consecutive-zero recurrence. Run the cyclic rectangle with order
only through \(s\). Its nondegenerate case forces global arithmetic
clocks. The degenerate case gives either a single arithmetic
prefix through stage \(s-2\), or an arithmetic prefix and tail of
the same nonzero step whose lengths sum to \(s-2\). The geometric
comparison in the rectangle only divides by paid index differences
and explicit nonzero field pivots. A run of seven is excluded by
the characteristic-safe local mark proof. Hence it remains to
consider two runs of length at most six. Their total length is at
least eight, so each has at least two clocks. In particular,
\(\delta=c_2-\gamma\).

The paid branching calculation before the Schur step, at order
\(s+1\), gives
\[
 C_s(t)=0,\qquad C_s(t)\coloneqq(s+1)t^3-4s t^2+2(s-3)t+4.
\]
Since \(C_s(2/3)=4(2-s)/27\ne0\), this is the generic slope
\(t\ne2/3\). If the longer run has six clocks, the preceding
internal \(F_1F_2\) test suffices. Otherwise each run has at least
three clocks and one has at least four. An anchored endpoint test
supplies the same probe in this case, including two four-clock runs.

### Exact payment for the anchored endpoint test

The prefix starts at \(c_1=\gamma\), and the affine tail necessarily
ends at \(c_s=1-\gamma\). The latter is an algebraic consequence
of the same rectangle: put \(n=s-2\), \(z=\xi-2\),
\(k_0=1+2m_1+m_2\), and \(l_0=m_1+2m_2+m_3\).
The first two reverse tall rows give
\(n k_0=z m_1-2\) and \((n-1)l_0=z m_2-2m_1\).
With \(e_0=m_1 k_0-l_0=\gamma E/L^2\) and
\(h_0=m_1 k_0=\gamma H/L^2\), this gives
\((n-1)e_0+h_0=-z{\cal D}\).
Since \(e_0/{\cal D}=-t\), the tail formula
\(c_s-\gamma=(s-3)\delta-H/D\) yields \(c_s=1-\gamma\).

Pick \((j,k)=(3,2)\) or \((2,3)\), with at least \(j+1\) prefix
clocks and \(k+1\) tail clocks. On paths omitting \(j+k\) stages,
multiply at the first and last occupied slots by
\[
 \prod_{a=0}^{j-1}(c-\gamma-a\delta),
 \qquad
 \prod_{a=0}^{k-1}(1-\gamma-c-a\delta),
\]
respectively. If fewer than \(j\) omissions are leading, the first
mark vanishes. If fewer than \(k\) are trailing, the second
vanishes. This is checked within the corresponding local run
whenever a deficit occurs and makes no assertion about clocks
at overrun positions. The only possible surviving allocation
has exactly \(j\) leading and \(k\) trailing holes. Its weight is
the product of those two particular normalized boundary deletions
times \(L\), because they remove disjoint edge blocks of the
full chain. Separate one-sided tests calibrate each deletion,
with the exact surviving mark values \(\delta^j j!\) and
\(\delta^k k!\). No intermediate clock assumption is used.

For formal \(T=J-\gamma I\), the action of the leading mark on
\(1\) is \(j! T^j H_j(\gamma/T)1\), where
\[
 H_2=(1+F_1)/2,\qquad H_3=(1+3F_1+2F_2)/6.
\]
These follow from \(X^a1=a!J^a1\); the notation does not invert
\(T\). On the degree budget used here, \(J\) under the scalar
polynomial pairing \(\ell(fg)\) has adjoint \(J^\ast=\ell-J\),
where \(\ell\) in the operator expression returns a constant.
Indeed on \(x^u,x^v\) the equality is
\[
 \frac{1}{(u+1)(u+v+2)}
   =\frac{1}{v+1}\left(\frac{1}{u+1}-\frac{1}{u+v+2}\right)
 \qquad (u+v+2\le s).
\]
Reflection \(f(x)\mapsto f(1-x)\) conjugates \(J\) to \(J^\ast\)
in this budget, by the polynomial derivative and the endpoint
value at \(1\); the derivative is injective modulo constants
in degrees less than the field characteristic. Reflection also
conjugates diagonal clock multiplication to \(1-X\).
Thus the trailing mark on \(1\) is the same polynomial
\(k!(T^\ast)^k H_k(\gamma/T^\ast)1\).
Moving its adjoint gives formal output
\(j!k! L\,\mu(H_jH_k)\), since the two mark orders \(j+k\)
and the remaining strict hops sum to \(s-1\).
All scalar pairings and adjunctions are within that combined
degree, with denominators at most \(s\); nothing is asserted
about adjoints on an unbounded polynomial space. Comparing with
the separate endpoint calibrations gives
\(\mu(H_2H_3)=\mu(H_2)\mu(H_3)\).
Since \(H_2=(1+F_1)/2\), this says \(\mu(gH_3)=0\).
The cubic coefficient of \(H_3\) is \((1-3t/2)/3\ne0\), so this
adds the missing fourth annihilation and excludes saturation.

## 2. Equality \(s=p\) with \(L\ne0\)

The nondegenerate and long-prefix charts are covered by seven
consecutive arithmetic clocks. Otherwise there are two runs of
at most six clocks, with sum \(s-2\ge9\); hence one has at least
five and the other at least three. The exact existing five-plus-three
placements give multiplicativity for
\(F_1^2,F_1F_2,F_1F_3,F_1^3\). They only use counts of holes,
clock differences \(\delta\) times paid integers, nonzero adjacent
products, and the paid factorials. Reflection in their placement is
only an order reversal of index lists and not a reversal of the
tableau.

At \(t\ne2/3\) use \(F_1F_2\) as above. At \(t=2/3\), in
\(u=y+1-t/2\), the cubic coefficient of the odd part of \(F_3\)
is \(4/81\), while \(F_1^2\) is even and monic quartic.
Subtracting a multiple of \(F_1^2\) from \(F_3\) thus gives a
cubic with nonzero cubic coefficient. The three-factor
\(F_1^3\) and two-factor \(F_1F_3\) tests imply its
orthogonality to \(g\), as in the exact split proof. This
again adds \(\mu(gy^3)=0\). No integer denominator other than
a paid unit enters this replay.

## 3. Equality \(s=p\) with \(L=0\)

Put \(m=s-1\), \(n=s-2=m-1\), and
\(M=\lambda_{s-2}\ne0\), so \(L_* = M\) and \(\lambda_m=0\).
If \(b_s=0\), deleting the final stage preserves every rooted
output: preceding triangular rows never use its column, and
componentwise rooted recursion preserves their stage values. This
would be the already excluded saturation case. Thus \(b_s\ne0\),
and because \(L=b_s\prod_{i=2}^s B_{i,i-1}=0\) there is a
broken adjacent edge \(B_{i,i-1}=0\).

Every nonzero strict path omits at least one of \(\{i-1,i\}\).
The one-hole law and the total weight \(M\) give the two
outer ladders with step \(\delta=(1-2\gamma)/(s-2)\):
\[
 c_j-\gamma=(j-1)\delta\quad(j\le i-2),\qquad
 c_j-\gamma=(j-2)\delta\quad(j\ge i+1).
\]
No assertion is made about the two clocks on the broken pair.
On any nonzero path, identify both physical pair indices with the
single virtual site \(i-1\), leave earlier indices unchanged, and
subtract one from later indices. The retained image is an increasing
list in \(m=s-1\) positions. A path with \(h+1\) physical holes
has \(h\) virtual holes. The two outer virtual runs now both
have \(c_u-\gamma=(u-1)\delta\); the clock at the virtual pair site
may depend on its retained representative. This is not a tableau
quotient or an averaging of the two middle clocks.

### A two-node test at either end supplies the generic slope

On paths with two physical holes, the virtual list has one hole.
In occupied slot \(k\), the virtual site is \(k\) or \(k+1\).
If \(i\ge5\) use \(k=2\), where both sites belong to the prefix.
If \(i\le4\) use \(k=s-3\), where both belong to the tail.
With \(a=k-1\), the two shifted clock values are
\(a\delta,(a+1)\delta\).
For \(j=0,1,2\) write \(E_j\) for the paid moment of the
\(j\)-th power of the shifted clock at this slot, with
\(n-1=s-3\) strict hops. The support identity is
\[
 E_2-(2a+1)\delta E_1+a(a+1)\delta^2 E_0=0.
\]
It pays exactly order \(s\) at the squared clock.

For the pre-Schur scalar calculation write \(v=m_1,Q=m_2,R=m_3\)
and \(K=v^3-2vQ+R\). The top paid row with \(\lambda_m=0\)
gives \(t=\delta/\gamma=v+2\). The next rows give
\[
 (n-1)Q=nv^2+2v-n-1,\qquad
 (n-2)R=(nv+4)Q-nv .
\]
For clarity the paid one-clock and same-slot square formulas give
\[
 \frac{\gamma E_0}{M}=v,\qquad
 \frac{E_1}{M}=1+a(1+2v+Q),\qquad
 \frac{E_2}{\gamma M}=t+a(10+8v+2Q)+a(a-1)(4+6v+4Q+R).
\]
Substituting in the support identity gives, after division by
\(\gamma M\), the polynomial \(a(a-(n-1))K\). The same two paid
rows give \((n-1)(n-2)K=C_m(t)\). For the two choices of \(k\)
above, \(a=1\) or \(a=n-2\), so \(a\) and \(a-(n-1)\) are
signed paid units. Thus \(K=0\), and \(C_m(t)=0\) gives both
\(t\ne0\) and \(t\ne2/3\): its evaluations there are \(4\) and
\(4(2-m)/27\). In particular the actual step is nonzero.
Moreover \(2-t=-v\) and
\[
             g=y^2-vy-(Q-v^2),\qquad \mu(gy)=K=0.
\]

### Calibrating short virtual windows in actual path weights

The two outer runs have total length \(s-2\ge9\); thus at least
one has five clocks. The count-\((1,1)\) test for \(F_1^2\)
fits within this five-run. If there is a six-run, the consecutive
count-\((1,2)\) test for \(F_1F_2\) fits inside it. Otherwise
the longest is five and the other has at least four. Use the
split count-\((2,1)\) placement on five earlier and three later
virtual clocks, or reflect only the index lists if the five-run
is later. Explicitly for \([u,u+4]\) earlier and \([w,w+2]\)
later, put the two marks at virtual occupied links starting
at \(u\) and \(w-2\), with three virtual holes. The first
endpoints cannot leave the five-run. A surviving first mark has
used at least two holes, so both endpoints of the second lie in
\([w,w+2]\). The second requires one further hole. Neither
placement tests a virtual pair clock with an unknown value.

In every selected placement, a surviving list has all \(h\)
virtual holes in the marked gaps, so it retains the virtual
middle site. The surviving physical lists therefore come
from the two possible one-hole base lists by the same disjoint
internal skip replacements, with exactly one physical pair
index omitted. Lists omitting both pair indices have a missing
virtual middle and are killed, not double counted. At least one
base list has nonzero weight since their weights sum to \(M\).
Both base lists retain all outer-run stages, so all adjacent
factors within these runs are nonzero. For each selected gap,
divide its actual skip entry only by its own adjacent block in
its run, defining its normalized skip. The total actual marked
weight is \(M\) times the product of these normalized skips and
their scalar mark values. This equality allows one zero base
weight or any zero skip. Separate single marks at the
corresponding virtual donor slots calibrate exactly the same
skips: with \(d\) virtual holes, the endpoints of a single
marked link lie in its selected interval of width \(d+2\),
and survival uses all \(d\) holes in that link.

A virtual test with \(h\) holes has \(m-1-h\) strict hops and
total mark degree \(h\). Its formal payment is precisely order
\(m=s-1\), as for a cyclic list of effective size \(m\), and
normalizes by \(M\), not \(L\). For each count \(d\), its
formal mark polynomial is \(d!T^{d+1}F_d(\gamma/T)\), so the
combined formal output evaluates the product of the same
\(F_d\)'s. Comparing with the actual calibrated weights proves
\[
  \mu(F_1^2)=\mu(F_1)^2,\qquad
  \mu(F_1F_2)=\mu(F_1)\mu(F_2).
\]
The first identity gives \(\mu(g^2)=0\); since
\(\mu(g)=\mu(gy)=0\) and \(g\) is monic quadratic, this is
\(\mu(gy^2)=0\). The second and \(t\ne2/3\) give
\(\mu(gy^3)=0\). The four paid reverse rows give the
contradiction.

All cases \(s\le p\) are excluded. The maximal-field reduction
at the start proves the theorem over the original ring,
including nonunit and nilpotent common diagonals. No code or
compilation is asserted for this mathematical argument.

For shorter arguments in two branches, see [the fully marked saturation path](../research/strict-sdirk-dependency-depth/DECORATED-SATURATION.md) and [the four-clock test when the longest paid path vanishes](../research/strict-sdirk-dependency-depth/FOUR-CLOCK-VANISHING.md). The cyclic equality branch still uses the split-run argument above. This extends the proof to all nonzero commutative rings; it does not replace the larger stage numbers already known in the main table through order 20.
