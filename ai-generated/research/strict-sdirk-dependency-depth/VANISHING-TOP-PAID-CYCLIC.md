# The vanishing-top paid chart at s=p+1 is physically cyclic for p>=8

Mathematical proof, not kernel-checked. Let \(A=\gamma I+B\) be
triangular over any characteristic-zero field, with common actual
diagonal, \(B\) strictly lower triangular, \(s=p+1\) physical stages,
and all rooted order conditions through \(p\). Put \(e=1\), \(c=Ae\),
and let \(\lambda_j=b^TB^je\) for the paid indices \(0\le j\le p-1\).
If \(p\ge8\) and \(\lambda_{p-1}=0\), then \(b_s\) and every actual
adjacent strict entry \(B_{i,i-1}\) are nonzero. In particular the
zero paid scalar in this chart is a cancellation of actual
one-hole paths, not their absence. We never use, equate, or
prescribe the unpaid \(\lambda_p\). No stage exclusion for all
\(s=p+1\) methods is asserted.

Together with the separately proved nonvanishing-top theorem,
the same physical cyclicity holds for every common-diagonal
\(s=p+1\) method in the range \(p\ge18\), without either paid
top coefficient assumption. This is a support conclusion.

## 1. Paid scalars and two explicit forbidden lower-path tests

Set \(n=p-2=s-3\) and \(M=\lambda_n\). The tall rooted conditions
give the explicit binomial polynomials
\[
 \lambda_j=\sum_{u=0}^j\binom ju\frac{(-\gamma)^{j-u}}{(u+1)!},
 \qquad
 (j+2)\lambda_{j+1}=(1-2(j+1)\gamma)\lambda_j-j\gamma^2\lambda_{j-1}.
 \tag{1}
\]
Only indices through \(n+1=p-1\) are needed. The recurrence
follows, for example, by differentiating the formal generating
function \(z\sum_{j\ge0}\lambda_j z^j=\exp(z/(1+\gamma z))-1\).
Here \(\gamma\ne0\) since the unshifted tall coefficient never
vanishes; \(M\ne0\) since consecutive zeros would propagate
backwards to \(\lambda_0=0\) by (1).
Also \(b_s\ne0\) already for \(p\ge7\). Dropping a zero-output
last row and column would preserve every rooted output and the
common diagonal, and give \(p\) stages of order \(p\) with the
same vanishing paid \(\lambda_{p-1}\). The previously proved
equality no-cancellation theorem rules this out.

Let \(J\) be formal integration from zero, \(T=J-\gamma I\),
\(X\) multiplication by the variable, and \(\ell\) formal
integration from 0 to 1. The exact clock model sends \(B,C\)
to \(T,X\), where \(C=\operatorname{diag}(c)\), by the rooted
stage polynomial \((|t|/\rho(t))x^{|t|-1}\) for a tree \(t\)
and its factorial \(\rho(t)\). A scalar word with \(d\) strict
hops and \(j\) marks pays only tree orders through \(d+j+1\).
Put
\[
       \epsilon=\frac{1-2\gamma}{n},
       \qquad \xi=\frac1\gamma,\qquad
       t=\frac{\epsilon}{\gamma}=\frac{\xi-2}{n}.
\]
No proof below divides by \(\epsilon\). The case of zero
step would still give vanishing actual link marks.

Physical two-hole paths have \(n+1\) retained stages, \(n\)
strict edges, and total weight \(M\). Their first paid clock
at occupied slot \(k\), counted from the earliest retained
stage, is exactly
\[
       \langle c_{\mathrm{slot}\ k}\rangle
                         =M\big(\gamma+(k-1)\epsilon\big).
 \tag{2}
\]
Indeed its formal model is
\(J T^n1+(k-1) J^2T^{n-1}1\) by \([X,T]=J^2\).
The constant integral is \(\gamma M\), since
\(\lambda_{n+1}=0\). The coefficient of \(k-1\) is
\(2\gamma M+\gamma^2\lambda_{n-1}=\epsilon M\) by (1).
This pays \(n+2=p\) tree vertices.

Physical three-hole paths have \(n\) retained stages and
\(n-1\) strict edges. At a marked occupied link let \(d\)
denote the actual receiver clock minus donor clock.
An entrywise \(d^jB\) at that link is
\(\mathrm{ad}_C^j(B)\). Its exact model is \(j!J^{j+1}\)
for \(j\ge1\), and \(T\) for \(j=0\).
Thus a link mark \(d-\epsilon\) has model
\(Q_1=J^2-\epsilon T\) and
\((d-\epsilon)(d-2\epsilon)\) has model
\(Q_2=2J^3-3\epsilon J^2+2\epsilon^2T\).
Whichever occupied links are chosen, the following two
degree-two tests are paid exactly at \(p\):
\[
 \begin{array}{c|c|c}
 \text{actual mark} & \text{formal target} &
             \text{value}\\ \hline
 (d-\epsilon)(d-2\epsilon)\text{ on one link}
   & \ell(T^{n-2}Q_2\,1)
   & -\gamma M\,C_{n+1}(t)/(n-1)\\
 (d_1-\epsilon)(d_2-\epsilon)\text{ on distinct links}
   & \ell(T^{n-3}Q_1^2\,1)
   & \gamma M\,C_{n+1}(t)/((n-1)(n-2)).
 \end{array}                                                \tag{3}
\]
Here \(C_m(t)=(m+1)t^3-4m t^2+2(m-3)t+4\), the cubic of the
earlier scalar-saturation calculation. Unmarked \(T\)'s and
the \(Q_i\)'s commute, so the formal targets do not depend
on the positions chosen. The maximum formal powers of \(T\)
are \(n+1=p-1\), not \(p\).

To verify the table, set
\(v=\gamma\lambda_{n-1}/M,\ Q=\gamma^2\lambda_{n-2}/M,\
R=\gamma^3\lambda_{n-3}/M\).
Equation (1) gives
\[
 t=v+2,\quad (n-1)Q=nv^2+2v-n-1,\quad
                       (n-2)R=(nv+4)Q-nv.
\]
Expand \(J=T+\gamma\) and divide the first target in (3)
by \(\gamma M\). It is
\[
 6+6v+2Q-3t(1+2v+Q)+2t^2 v
             =2v^3+2v^2-v-(3v+4)Q
             =-\frac{C_{n+1}(v+2)}{n-1}.
\]
For the second target the same normalization gives
\[
 4+6v+4Q+R-2t(1+2v+Q)+t^2v
            =v^3-2vQ+R
            =\frac{C_{n+1}(v+2)}{(n-1)(n-2)} .
\]
For the last polynomial simplification, the numerator expands
to \((n+2)v^3+2(n+4)v^2+(4-2n)v-4(n+1)\).
These are exact identities in the paid coefficients.

Both targets in (3) are nonzero. Indeed \(\lambda_{n+1}=0\)
puts \(\xi=1/\gamma\) at the alpha-one Laguerre zero of degree
\(n+1=p-1\), while \(t=(\xi-2)/n\).
The earlier saturation proof checks the exact exclusion
\(C_{n+1}(t)\ne0\) for \(n+1\ge4\), either by Schur's
irreducibility of the literal \(L_{n+1}^{(1)}\) over the
rational prime subfield or by the standalone degree-at-most-three
factor exclusion in its appendix. This is a restriction on the
paid scalar \(\lambda_{p-1}\) only.

## 2. Two disjoint broken links: two actual forced vacancies

A broken adjacent strict link is an actual zero \(B_{i+1,i}\).
If a strictly increasing physical path keeps both endpoints
\(i,i+1\), they are consecutive on the path and its weight
is zero. Suppose there are two broken links with disjoint
endpoint pairs \(F_1,F_2\). Each nonzero path must omit at least
one stage from each pair. Each nonzero physical two-hole path
therefore omits exactly one in each pair and none elsewhere.
Outside the two pairs, every literal physical stage is then
retained at a deterministic occupied position. By (2) and
\(M\ne0\), their actual clocks form arithmetic runs of step
\(\epsilon\) on each of the at most three exterior intervals
before, between, and after the pairs.

For a nonzero three-hole path, compact the stage list by
deleting one omitted index per pair. One may choose arbitrarily
when both in a pair are omitted. This leaves a grid with
\(s-2=n+1\) indices and precisely one freely omitted index.
Grid indices of physical stages outside the two pairs are
independent of which representatives were removed, since
one per pair has been removed. In particular every exterior
run is literal on this grid and has the same arithmetic step.
An occupied slot \(k\) on such a path has compact index
\(k\) or \(k+1\). Once this shift of one has occurred it cannot
decrease at a later slot.

* If an exterior run has three consecutive clocks, take its
  starting compact index \(i\) and mark occupied link
  \(i\) to \(i+1\) in the three-hole band. The compact endpoints
  always stay inside \([i,i+2]\); their actual difference is
  \(\epsilon\) or \(2\epsilon\). The single-link mark in (3)
  is therefore zero on every nonzero path, a contradiction.
* If two distinct exterior runs each have at least two clocks,
  take ordered compact pairs \([i,i+1]\), \([j,j+1]\) in them.
  Mark links \(i\) and \(j-1\) (start indices) by \(d-\epsilon\).
  They are distinct because \(j\ge i+2\).
  If the first receiver is \(i+1\) on the compact grid,
  the first mark is zero. Its only other possible receiver is
  \(i+2\), which means the free hole has already passed.
  Then the later link is exactly the compact adjacent pair
  \(j,j+1\) and the second mark is zero. This argument does not
  need the outlying clock at the first link. The paid
  distinct-link test in (3) gives the contradiction.
  The occupied slots exist since \(j+1\le n+1\) and the
  three-hole band has \(n\) retained stages.

There are \(s-4=p-3\) clocks outside the two pairs, in at most
three runs. If no run has length three and at most one has
length two, they total at most four clocks. At \(p\ge8\)
their total is at least five, so one of the two tests always
applies. No assumption on any other broken link or skip is
needed in this case.

## 3. If no two breaks are disjoint: a signed virtual vacancy

Suppose at least one adjacent link is broken, but no two
broken links have disjoint endpoint sets. Fix one broken pair
\(F=\{a,a+1\}\). Every broken adjacent edge meets this pair,
so all adjacent physical entries with both endpoints outside
\(F\) are nonzero. Collapse the two endpoints to one virtual
site \(a\), with all other physical indices in inherited
order, on a grid of size \(p=s-1\).
As in the earlier two-mode transducer, a nonzero physical
path retains at most one representative of \(F\). Each
virtual retained list keeping \(a\) has the two possible
representatives, and one omitting \(a\) has the single
physical realization with both endpoints deleted.
Aggregate the physical weights for each virtual list once;
zero-weight paths retaining both endpoints are omitted.

Set \(N(a)=\{a-1,a,a+1\}\cap\{1,\ldots,p\}\).
The crucial signed support identity is:
\[
     \overline w_H=0\quad\text{for every virtual hole set }H
                                            \text{ disjoint from }N(a).
 \tag{4}
\]
To prove it, the virtual no-hole list has the two actual
one-hole weights \(\omega_a,\omega_{a+1}\), whose sum is
exactly the paid \(\lambda_{p-1}=0\).
Deleting a virtual hole interval outside \(N(a)\) changes
only a physical segment lying completely outside \(F\);
its normalized skip ratio is identical for the two
representatives. Several disjoint hole intervals change
disjoint edge blocks, so those common ratios multiply.
The denominators are adjacent physical edges outside \(F\)
and are nonzero. An initial interval just drops leading
adjacent edges. A terminal interval uses \(b_s\ne0\) and
changes the terminal weight by the same ratio in both paths;
if \(F\) includes the physical last site, an interval disjoint
from \(N(a)\) cannot touch that virtual endpoint at all.
The resulting exact product equality holds even if both base
one-hole weights vanish, since no zero on the unresolved
part is changed by these replacements. Thus the aggregate
factor for every \(H\) disjoint from \(N(a)\) multiplies
the zero total \(\omega_a+\omega_{a+1}\). This proves (4)
without dividing by a base weight or by their sum.

Clocks at virtual index \(a\) may differ for its two
representatives. Accordingly (4) is used only in words
whose marked occupied slots avoid \(a\) for **all** candidate
paths in that band, before cancellation. In such a word
the mark values depend only on the virtual indices and
common safe clocks; hence zero aggregate weights can
legitimately be discarded. The remaining virtual paths
have at least one virtual hole in \(N(a)\). This is a
signed support conclusion, not a claim that every physical
path had two structurally forced omissions.

For the top two-hole band there is exactly one virtual hole.
At occupied slot \(k\le a-2\) the possible virtual indices
\(k,k+1\) avoid \(a\); since the nonzero aggregate hole is
in \(N(a)\) it lies strictly after \(k\), and the clock at
this slot is the virtual clock \(k\).
At occupied slot \(k\ge a+1\), the indices again avoid \(a\);
the surviving virtual hole lies at or before \(k\), so
this clock is the virtual clock \(k+1\).
Applying the paid first moment (2) and \(M\ne0\) now fixes
literal arithmetic runs of step \(\epsilon\) on
\[
                 1,\ldots,a-2
               \quad\text{and}\quad
                 a+2,\ldots,p
\]
in virtual indices, translating by a constant on each side
to the original physical indices. Empty intervals are
ignored. Their lengths total at least \(p-3\).
Thus at \(p\ge8\) one side has three consecutive safe
arithmetic clocks.

For the next, three-hole band there are two virtual holes.
Place the single-link degree-two mark as follows, so that
even before (4) is invoked the marked endpoints stay safe.

* A left run of three occupies virtual \(i,i+1,i+2\le a-2\).
  Mark the occupied link with start slot \(i\). Before
  cancellation the full possible window is \([i,i+3]\)
  and \(i+3\le a-1\), so it avoids the ambiguous \(a\).
  After (4), at least one of the two virtual holes lies
  in \(N(a)\), hence is at least \(a-1\). The receiver
  cannot then be \(i+3\le a-1\): that would use both holes
  before the receiver, contrary to the compulsory signed
  core hole, and a retained receiver cannot itself be a hole.
  Both endpoints therefore stay in \([i,i+2]\).
* A right run of three occupies virtual \(i,i+1,i+2\ge a+2\).
  Mark the occupied link starting at \(i-1\); its full window
  \([i-1,i+2]\) avoids \(a\).
  After (4), one virtual hole is in \(N(a)\), at most \(a+1\).
  The donor cannot be \(i-1\ge a+1\), since that would have
  passed zero virtual holes and a retained donor cannot be
  the core hole itself. Hence the endpoints stay within
  \([i,i+2]\).

The indicated occupied slots exist because the three-hole
band has \(p-2\) retained stages, and the right run ends
at \(i+2\le p\) (the analogous left bound is stronger).
Inside either run, actual clock differences are exactly
\(\epsilon\) or \(2\epsilon\), since the virtual-to-physical
translation on one side is constant. Therefore the single-link
mark in (3) again vanishes on all remaining contributions,
contradicting its nonzero paid target.

This handles every broken-link topology with matching
number one; it includes cancellation of nonzero modes and
the case where both one-hole modes vanished. It does not
replace a statement about the physical support by a false
independent-clock assertion at the ambiguous site.

## 4. Cyclic conclusion and a nonadjacent weight constraint

Every nonempty set of broken adjacent links either has two
with disjoint endpoint sets or has matching number one.
Sections 2 and 3 rule out both, for \(p\ge8\).
Together with \(b_s\ne0\), this proves the stated conditional
full physical cyclicity.

To see the actual cancellation in the remaining chart, put
\(a_i=B_{i,i-1}\) and \(L_{\rm full}=b_s\prod_{i=2}^s a_i\ne0\).
This is a physical product; it has not been assigned a scalar
value by order. The actual one-hole path omitting the first
stage has nonzero weight \(L_{\rm full}/a_2\).
The zero paid sum of all one-hole paths therefore gives the
exact support-sensitive relation
\[
       \frac1{a_2}
       +\sum_{j=2}^{s-1}\frac{B_{j+1,j-1}}{a_j a_{j+1}}
       +\frac{b_{s-1}}{b_s a_s}=0 .
\]
In particular at least one second-subdiagonal entry or
\(b_{s-1}\) is nonzero, and there is actual signed cancellation
over an ordered field. This is not a numerical lower bound
beyond \(s=p+1\).

Frozen dependencies: alpha-one/cubic exclusion in
COMMON-DIAGONAL-PAID-NONLINEAR.md, SHA-256
0d7890b60dcf139637a7f9dc148d12b75a854f47f0005c74b6fd1ed1ebaea86b;
the \(s=p\) no-cancellation theorem in
COMMON-DIAGONAL-ONE-SLACK.md, SHA-256
2e0cc583dfcd15df4c491539198a06457054c5825c6ba9d81976d7171ca59936;
the companion nonvanishing-top chart in
FORCED-VACANCY-TRANSDUCER.md, SHA-256
21860a583e5c8eacfdb8bf7e8d6de73579ed78089d3b1fc9784571238987a155.

The [nonzero-top case](FORCED-VACANCY-TRANSDUCER.md) is separate. Neither proof assigns a value to an unpaid full-chain coefficient.
