# Near-saturation with one forced vacancy: a paid two-mode transducer

Mathematical proof, not kernel-checked. Here \(A=\gamma I+B\) is
triangular over a characteristic-zero field with common actual
diagonal, \(B\) strictly lower triangular, and \(s=p+1\) physical
stages passing every rooted condition through \(p\). Put \(e=1\)
and \(c=Ae\). Define the paid moments
\[
        \lambda_j=b^TB^je
          =\sum_{u=0}^j\binom ju\frac{(-\gamma)^{j-u}}{(u+1)!}
          \quad(0\le j\le p-1),\qquad L_*=\lambda_{p-1}.
\]
The original full physical product \(b^TB^{s-1}e\) is **not** paid.

**Conditional topology theorem.** If \(p\ge18\) and \(L_*\ne0\),
then every actual adjacent strict entry of \(B\) is nonzero, for
every common \(\gamma\). For \(\gamma=0\) the same conclusion
follows already for \(p\ge9\) by the test below. In those respective
ranges \(b_s\ne0\) also follows by deleting an inactive last stage
and applying the previously established equality exclusions.
Thus \(L_*\ne0\) at \(s=p+1,\ p\ge18\) forces full physical cyclicity,
even though the full original product was not paid.
No conclusion is claimed for \(L_*=0\) with nonzero \(\gamma\),
and no unconditional improvement of the stage count is asserted.

The key reusable identity is an equality-case paid rectangle on
a virtual \(p\)-stage path grid with one ambiguous site. It is not
an assertion that there is a compressed ordinary \(p\)-stage RK
tableau or that any physical clocks have changed.

## 1. The physical vacancy and the virtual path weights

Suppose an actual adjacent strict link from physical \(a\) to
\(a+1\) is zero, with \(1\le a\le p\). Let \(F=\{a,a+1\}\).
Any strict path of nonzero weighted product omits at least one
of \(F\): if it retained both adjacent indices, it would traverse
the broken edge. Collapse both of these indices to virtual index
\(a\), and map other physical indices in their inherited order
to the remaining indices in \(\{1,\ldots,p\}\).
For a path with at most one representative in \(F\), its virtual
retained list is strictly increasing. A virtual list retaining
\(a\) has two physical realizations (its representative may be
\(a\) or \(a+1\)), while a list omitting \(a\) has exactly one
physical realization (both representatives deleted).
We sum each such physical weight once, including zero-valued
ones. The omitted physical paths that retain both of \(F\) have
weight zero and do not matter.

For a virtual hole set \(H\) with a nonempty retained list, let
\(\overline w_H\) be this aggregated physical path weight.
Thus free virtual holes \(h=|H|\) correspond to \(h+1\) physical
holes and \(p-h\) physical retained stages.
In particular \(\overline w_\varnothing=L_*\), because paths
with \(p-1\) strict edges have exactly one physical hole.
At least one of the two possible full virtual paths has nonzero
weight. Consequently every adjacent physical entry along a
part of the grid that avoids \(F\) is nonzero, since both
full virtual paths contain those edges.

For \(j\ne a\) let \(c_j^\circ\) be the actual clock of the
unique physical representative at virtual index \(j\).
The virtual clock at \(a\) is undefined; it is not presumed
equal for the two representatives. If an occupied position has
all its possible virtual indices different from \(a\), a clock
mark there is well-defined on aggregated virtual paths.

An isolated one-hole modification at virtual \(j\) with
\(|j-a|\ge2\) has a **common physical ratio** \(g_j\).
At an interior \(j\) take its actual bypass entry divided by
the two actual adjacent entries it replaces. Both are on the
same side of \(F\), so the ratio is independent of the
representative. At a safe initial \(j=1\), take the reciprocal
of the first adjacent entry. At a safe terminal \(j=p\),
take \(b_{s-1}/(b_s B_{s,s-1})\): the full virtual path of
nonzero weight ends at physical \(s\) in this case, so its
denominator is nonzero. Numerators may freely vanish.

More generally, if \(j\notin H\) is safe and no hole in \(H\)
is adjacent to \(j\), the corresponding factor \(g_j\)
is unchanged on the paths with holes \(H\). Inserting the hole
\(j\) does not alter the list of representative choices and
changes exactly the same fragment in each physical path.
Thus
\[
               \overline w_{H\cup\{j\}}=g_j\overline w_H.
\]
Writing \(\omega_j=\overline w_{\{j\}}\),
\(\Omega_{jk}=\overline w_{\{j,k\}}\), this proves
\[
              L_*\Omega_{jk}=\omega_j\omega_k
                 \quad(k-j\ge2)
 \tag{1}
\]
except possibly \(j=a-1,k=a+1\), the only separated pair for
which neither hole is safe. There is no need to assume
(1) on the exceptional pair or a nonzero individual mode.

## 2. The exact paid rectangle on safe occupied positions

For the virtual hole grade \(h\), a strictly increasing retained
list has occupied slot \(i\) at virtual index in \([i,i+h]\).
In particular a one-hole mark at slot \(k\) is safe when
\([k,k+1]\) avoids \(a\). A two-hole position \(i\) is safe
when \([i,i+2]\) avoids \(a\).
One free hole makes \(p-2\) strict edges, and one mark pays
exactly \(p\) with the leaf. Two free holes make \(p-3\)
strict edges, and two marks also pay exactly \(p\).
Nothing uses \(\lambda_p\).

Write \(x_j=c_j^\circ-\gamma\), \(M_*=\lambda_{p-2}\),
\(K_*=\lambda_{p-3}\), \(R_*=\lambda_{p-4}\),
\(S_*=\lambda_{p-5}\), and
\[
 \begin{aligned}
 \kappa&=L_*+2\gamma M_*+\gamma^2 K_*,
 & \eta&=M_*+2\gamma K_*+\gamma^2R_*,\\
 V_3&=L_*+3\gamma M_*+3\gamma^2K_*+\gamma^3R_*,
 & V_4&=L_*+4\gamma M_*+6\gamma^2K_*+4\gamma^3R_*+\gamma^4S_* .
 \end{aligned}
\]
The one-hole total is \(M_*\). At a safe one-hole slot \(k\)
the shifted clock has index \(k\) or \(k+1\) according as the
hole lies after \(k\) or not. The paid first moment gives
\[
    M_* x_k+T'_k(x_{k+1}-x_k)=A'_k,\qquad
    T'_k=\sum_{j\le k}\omega_j,\quad A'_k=L_*+(k-1)\kappa.
 \tag{2}
\]
This is the same one-mark formal identity as for a full \(p\)-stage
chain, with the paid aggregate as top.

Take \(i\le\ell\) both safe two-hole positions. On each two-hole
path let \(Z_h\) be the shifted actual clock at safe slot \(h\).
The product \((Z_i-x_i)(Z_\ell-x_{\ell+2})\) is supported on
the rectangle of hole pairs \(j\le i\), \(k>\ell+1\),
and equals \(-(x_{i+1}-x_i)(x_{\ell+2}-x_{\ell+1})\)
there. If \(i\) is to the left of the ambiguous window then
\(i\le a-3\), so the first hole is safe for (1). Otherwise
\(i\ge a+1\) and \(\ell\ge i\); the second hole \(k>\ell+1\)
is safe. In particular the possibly nonfactorable pair never
contributes. Thus (1) and (2) give the division-free identity
in the clock differences
\[
 L_*\langle(Z_i-x_i)(Z_\ell-x_{\ell+2})\rangle
             =(A'_i-M_*x_i)(A'_{\ell+1}-M_*x_{\ell+2}).
 \tag{3}
\]
Here the brackets sum weighted physical paths.
The proof is valid with arbitrary repetitions of safe clocks.

For completeness, the formal clock word model sends \(B,C\)
to \(T=J-\gamma I,X\), where \(J\) is integration from 0
and \(X\) is multiplication by the variable. The output
is the formal integral from 0 to 1.
Indeed the exact stage clock polynomial for a rooted tree
\(t\) is \((|t|/\rho(t))x^{|t|-1}\).
Expanding \(B\) as \(A-\gamma I\) only uses unary lifts and
adding leaves to a root. The commutator \([X,J]=J^2\)
gives, for \(i-1=\nu,\ell-1=\omega\), the shifted one-mark
two-hole moments \(M_*+\nu\eta\) and \(M_*+\omega\eta\)
and the shifted two-mark moment
\[
          L_*+(\omega+1)\kappa+
                 \nu(2V_3+\kappa-V_4)+\nu\omega V_4.
\]
For example the unshifted two-mark polynomial is
\(2J^2T^{p-3}+(\omega+3\nu)J^3T^{p-4}
+\nu(\omega-1)J^4T^{p-5}\) applied to 1; shift both clocks
by \(\gamma\) to get the displayed moment.
Define the scalar coefficients
\[
 \begin{aligned}
 D&=L_*K_*-M_*^2,\quad E=M_*\kappa-L_*\eta,\quad
 F_0=L_*V_4-\kappa^2,\\
 H_0&=M_*\kappa,\qquad G=L_*(2V_3-V_4)-\kappa^2,\qquad
 \Delta=D F_0-E^2 .
 \end{aligned}
\]
Expanding (3) and dividing by the positive integer \(\nu\)
gives the original full-chain rectangle recurrence, now
valid on the safe source and target positions only:
\[
 (D u_\nu+E)x_{\omega+3}
      +(E u_\nu+F_0)\omega+H_0u_\nu+G=0,\qquad
 u_\nu=x_{\nu+1}/\nu .                                      \tag{4}
\]
Its domain is \(\nu\le\omega\) in the positive safe set
\[
           {\cal S}=[1,a-4]\ \cup\ [a,p-3] .
\]
An interval with upper endpoint below its lower is empty.
All symbols in (4) concern physical clocks outside \(F\);
it leaves the middle site unresolved.

## 3. Local multiplicativity also transfers to the virtual grid

The same \(L_*\) replaces the full product in all local gap
tests. Consider one seven-clock virtual arithmetic run wholly
on either side of \(a\), or the two-run placements of the
split-run proof with each run wholly on a side (the runs may
lie on opposite sides). The physical clocks in each such run
are literal, since the map is a fixed index translation there.
Choose occupied links in the virtual ordering as in those
proofs. For any possible nonzero physical path the virtual
endpoints are bounded using the number \(h\) of free holes.
When a marked link stays in one of the designated runs,
its physical difference is exactly \(\delta(1+g)\), with
\(g\) its virtual omitted count and \(\delta\) the actual
step of that run. In the split proof the only possible
uncontrolled endpoint is an overrun by one; it already
uses all free holes, so a later valid mark still kills the path.
Reflection is only a choice of occupied slots, not a
reversal of the actual matrix.

Use the usual mark \(P_d(w)=\prod_{j=1}^d(w-j\delta)\).
Let \(d_1,\ldots,d_q\) be the selected gap counts and take
\(h=\sum d_j\) free holes, that is \(h+1\) physically.
The surviving allocation exhausts every free hole in the
selected intervals, all of which are internal and wholly
outside the ambiguous index. Thus virtual index \(a\)
is retained, and either representative mode may contribute.
The normalized physical ratio for each of these longer
skips has nonzero denominator from the adjacent entries
on that side. The ratios are the same in both modes;
the actual surviving path sum is \(L_*\) times their product,
including a possible zero skip.
For each such particular skip, separate one-mark calibration
at its actual virtual donor slot and \(d\) free holes
uses only its local arithmetic window and the same two-mode
normalization. Therefore, for \(\gamma\ne0\), the tuple of
marks gives exactly
\[
      \mu\Big(\prod_j F_{d_j}\Big)=\prod_j\mu(F_{d_j}),\qquad
      \mu(y^i)=\gamma^i\lambda_{p-1-i}/L_* ,
 \tag{5}
\]
for every placed tuple, with precisely the same \(F_d\) as
in the earlier arithmetic proofs. Indeed \(p-h-1\) strict
edges and \(h\) marks pay order \(p\); the formal rearranged
power is \(T^{p-1}\), not \(T^{s-1}\).
There is no global Toeplitz or equal skip-weight premise.
The earlier grade-six arithmetic contradiction now applies
with the scalar recurrence parameter \(p\) instead of \(s\).
In the degenerate chart it also applies to the placed products
of a length-five plus length-three pair of equal-step runs,
using the same normalized radical argument.
In particular any single seven-clock nonzero-step run entirely
on one side is already impossible, without using (4).

At \(\gamma=0\), the single-hole gap polynomial is simply
\(F_1(z)=1-\delta z\) in the formal variable \(z=1/T\).
A local five-clock run places its square test (two marks,
two free holes). With \(\mu(z^i)=\lambda_{p-1-i}/L_*\),
the normalized values are \(\mu(z)=p\), \(\mu(z^2)=p(p-1)\).
Multiplicativity of \(F_1^2\) would give
\(-p\delta^2=0\), impossible. The following ERK cut argument
does not require any local arithmetic a priori.

## 4. Nonzero gamma: a broken link is impossible for p>=18

Write the lengths of the two literal sides of the ambiguous
site as \(l=a-1,\ r=p-a\). Their sum is \(p-1\).

If \(\Delta\ne0\), take either safe side with a long interval.
For every source \(\nu\) except the last on that interval,
there are at least two available target positions on the
same side. Hence \(Du_\nu+E\ne0\) by (4) and the nonzero
determinant. Each such source gives an affine clock tail;
on the overlap the slopes agree. The fractional slope
\((Eu+F_0)/(Du+E)\) is injective under \(\Delta\ne0\), so
these source slopes \(u_\nu\) all coincide.
On the left, the resulting prefix goes through physical
virtual index \(l-3\) and the affine tail starts at 4;
if \(l\ge8\) they overlap at two indices.
On the right, the prefix is \(a+1,\ldots,p-3\)
and the tail is \(a+3,\ldots,p\); if \(r\ge7\)
they overlap at two indices. Thus in either indicated case
the entire side is arithmetic. A zero step would make
\(x_j=0\) on the side: the corresponding prefix is
\(x_j=(j-1)u\) and its slope would be zero.
Two adjacent equal pairs in (2) would force
\(\kappa=0\) and then \(L_*=0\), impossible.
For \(p\ge15\) either \(l\ge8\) or \(r\ge7\),
so there is a forbidden local seven-clock run by (5).

Suppose \(\Delta=0\). As in the exact rectangle proof, \(D=0\)
would imply \(E=0\) and then four consecutive tall values
geometric, contrary to their paid recurrence when
\(\gamma\ne0,L_*\ne0\). Indeed
\(E=-2\gamma D+\gamma^2(M_*K_*-L_*R_*)\);
if the intermediate value is zero the top recurrence already
fails, otherwise the geometric ratio would have to be
\(-\gamma\) by subtracting the two recurrence rows, which
upon substitution forces \(\gamma=0\).
Hence \(D\ne0\) and \(F_0=E^2/D\).

If \(DG-H_0E\ne0\), every safe \(u_\nu\) avoids \(-E/D\),
else (4) has a nonzero constant left. All tails have slope
\(-E/D\), and at the last common safe target the fractional
intercept \((H_0u+G)/(Du+E)\) is injective. Thus all safe
source slopes agree. On the left the prefix now reaches
\(l-2\), and on the right it reaches \(p-2\).
These overlap the corresponding affine tail at two places
whenever \(l\ge7\) or \(r\ge6\) respectively. At \(p\ge18\)
at least one such overlap exists. Its slopes force the
excluded \(u_\nu=-E/D\). Therefore \(DG-H_0E=0\),
and with \(\delta=-E/D\) the exact factorization is
\[
             (Du_\nu+E)(x_{\omega+3}-\delta\omega+H_0/D)=0.
 \tag{6}
\]

Here \(\delta\ne0\). If \(E=0\), then \(F_0=G=0\).
If \(l\ge6\), the safe \(u_1=x_2=B_{21}\ne0\)
forces constant left tail \(x_4,\ldots,x_l=-H_0/D\).
Two adjacent equal pairs in (2) force \(\kappa=0\),
then \(H_0=0\) and \(L_*=0\). If \(l\le5\), then \(r\ge12\)
for the claimed range. The first three safe source slopes
on the right, at \(a,a+1,a+2\), cannot all be zero:
their three consecutive zero clocks in (2) would force the
same contradiction. A nonzero slope among those three gives
a constant right tail by (6), with at least \(r-4\)
clocks, so two equal pairs give the contradiction again.

Consequently (6) partitions the known safe coordinates
into at most three literal arithmetic runs, all with
step \(\delta\ne0\). Here is the exact indexing and count.
If all safe \(u_\nu=\delta\), use the left prefix through
\(l-2\) and the right interval \(a+1,\ldots,p-2\);
small sides contribute only the nonnegative length
\(\max(l-2,0)\) or \(\max(r-2,0)\).
If the first deviant \(\nu_0\) is on the left, split the left
into \(1,\ldots,\nu_0\) and \(\nu_0+3,\ldots,l\),
and use the whole forced right tail \(a+3,\ldots,p\).
If the first deviant lies on the right, keep the left prefix
and split the right into \(a+1,\ldots,\nu_0\) and
\(\nu_0+3,\ldots,p\).
Empty ranges contribute zero. A one-clock run has the stated
step vacuously. In each case at most two clocks per side
were lost, so the runs cover at least
\(l+r-4=p-5\) virtual indices outside \(a\), and thus the
same number of literal physical clocks in these same runs.

At \(p\ge18\) the total is at least 13.
For at most three runs, either one has length at least seven
or there is a pair of lengths at least five and three:
otherwise all lengths are at most four (sum at most 12),
or one has length five or six with every other length
at most two (sum at most 10).
Both outcomes are ruled out by (5) and the earlier
local or split-run arithmetic exclusion.
The split-run radical identity applies verbatim because its
only scalar inputs are \(D\ne0,\Delta=0,\delta=-E/D\)
and the paid reverse moments; all were checked on this
virtual chart. This finishes the conditional theorem for
nonzero \(\gamma\).

## 5. Zero gamma: safe rectangle alone suffices

For \(\gamma=0\) the same paid coefficients have
\(M_*=pL_*,\,\kappa=L_*,\,D=-M_*^2/p,\,H_0=M_*^2/p\)
and \(E=F_0=G=0\). In (4), any nonzero safe source clock
at \(u_\nu\) makes all corresponding tail clocks
\(x_{\omega+3}=1\).
An adjacent pair of safe clocks both 1 is impossible in
(2), since it would require \(M_*=j L_*\) at a virtual
index \(j<p\), whereas \(M_*=pL_*\).
If \(l\ge5\), the safe \(u_1=x_2=B_{21}\ne0\) makes the
left clocks \(4,\ldots,l\) equal to 1.
If \(r\ge5\), the first two right safe source clocks
cannot both be zero by (2); a nonzero choice makes at
least two consecutive right tail clocks equal to 1.
And if both \(l,r\ge4\), the safe nonzero left \(u_1\)
makes the right tail clocks \(a+3,\ldots,p\) equal to 1,
at least two clocks. For \(p\ge9\), \(l+r\ge8\)
forces one of these three conditions, so the broken
link is impossible.

Finally at any of the asserted ranges, if \(b_s=0\),
dropping the unused last row and column keeps every paid
order condition at \(s-1=p\) stages. In the zero-diagonal
case the established \(s=p\ge5\) ERK exclusion applies,
and in the other case the established common-diagonal
\(s\ge p+1\) for \(p\ge11\) applies. Thus \(b_s\) is
also nonzero. This is a topology inference, not a
claim of nonexistence of \(s=p+1\) methods.

The frozen prior inputs are the literal cyclic identity and ERK
equality test in CYCLIC-PAID-RECTANGLE.md (SHA-256
b9ee35a0ac94c1ad346a2b3b0b451ebd525aa2e353bfc2d2193e30aac044711d);
the grade-six algebra in PAID-ARITHMETIC-GAP-EXCLUSION.md
(SHA-256 0ec9a1ff481ec6b8c7946e86d7afe79c3ea9991e88c4aba1315a8ef6285b12ed);
the local placement in LOCAL-SEVEN-CLOCK-FLOOR.md
(SHA-256 123d15da36ceb3da6f2890eb2e7c0574f26d1e70e792293660ca1f6e312e41ce);
and the split placements/degenerate radical in
SPLIT-ARITHMETIC-RUNS-FLOOR.md (SHA-256
f07bbac5c2006f3b3029d6dd653f87410a3a0307e1000cd67ed5109f59f64b0a).

The [vanishing-top companion](VANISHING-TOP-PAID-CYCLIC.md) covers the complementary paid value. Together, the proofs force a nonzero physical adjacent subdiagonal and last output weight at s=p+1 for p≥18 in characteristic zero. This is a topology constraint, not a new stage-count lower bound.
