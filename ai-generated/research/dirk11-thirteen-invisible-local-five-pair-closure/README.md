# The normalized five-marked-pair DIRK11/13 allocation is impossible

**Result.** For a normalized characteristic-zero thirteen-stage DIRK
tableau of rooted order at least eleven, consider the invisible one
numerical cubic-dirty clock \(r=0,d=1\), with zero grouped fourth head,
nonzero grouped fourth-head square, and a multi-label genuine reflected
cubic \(G\). The exact previous square census leaves one physical dirty
row and two possible allocations; this proof eliminates the **five
marked pairs with no silent slack** allocation. With the
[four-pair plus slack closure](../dirk11-thirteen-invisible-local-four-pair-closure/README.md)
it eliminates this entire grouped-square/multi-label \(G\) slice.
One-label \(G\), zero grouped square, nonzero grouped fourth head,
and other support or normalized ranks remain separate. The unrestricted
real stage interval is still **13–14**. No positivity of weights or
ordering of clocks is used.

## 1. Actual no-slack ranks, companion, and stage chronology

Use the signed normalization and the
[grouped-square census](../dirk11-thirteen-invisible-local-square/README.md).
Write \(g=Ac^2-c^3/3,\ h=(A-\xi/2)g\).
Here \(E_j,F_j\) are the actual rooted stage spaces and their zero-profile
subspaces. The ranks used are \(\dim E_5=9,\dim E_6=11,\dim E_7=12\),
\(e_T\in E_6\setminus E_5\), and \(F_4=\langle g,h\rangle\), with both
defects zero at the actual endpoints. Thus
\(E_4=\mathcal P_4(c)\oplus\langle g,h\rangle\): the continuous rooted
profiles have degree at most four, all pure clock columns are present,
and a pure polynomial in \(F_4\) is zero by the paid fixed rational
Gram moments. The actual \(C(2)\), reflected \(D(1),D(2)\), and the
zero terminal column are the same normalization hypotheses as in
the signed census.

The ordinary numerical support consists of the true endpoints and five
distinct nonendpoint labels. Each nonendpoint is one marked pair, with
two live individual weights, live ordinary sum \(\mu_s\), and opposite
nonzero \(b_i h_i\). This leaves exactly the one invisible cubic row
\(j\) of weight zero besides those ten physical pair rows and actual
\(O,T\). The first nonzero forward clock has \(g_i=c_i^3/6\ne0\) by
\(C(2)\), so that row is \(j\); the dirty \(\xi\) may numerically coincide
with an ordinary clock. Since the other ten nonendpoint clocks are
nonzero forward, literal **reverse** order is \(T\), the ten marked
rows, \(j\), \(O\). There is no possible intervening silent, dirty, or
endpoint row among the ten marked rows.

Use literal reverse \(N=A^{\mathsf T}\) and \(Y=1-c\).
Write \(W(U)=b_{\rm wt}U(Y)\), with physical weights, and
\(G=NW(Y^2)-W(Y^3/3)\). The tree orders give \(G\in E_7^\perp\),
\(YG\in E_6^\perp\) and \(\beta h\in E_6^\perp\); hence
\(U_0=E_6^\perp=G\mathcal P_1(Y)\), since two distinct live \(G\)
labels are assumed. Thus \(\beta h=\ell_h(Y)G\) with a nonzero affine
\(\ell_h\), possibly constant. Grouped \(\beta h=0\) implies all class
sums of \(G\) are zero away from the possible unique root of \(\ell_h\);
the true \(G1=0\) kills the possible last class sum there as well.
At \(j\) separately, \(Gg=0\) gives \(G_j=0\), even for numerical
overlap with a marked label. \(G_T=0\) is literal at reverse origin
\(Y=0\), and \(G_O=0\) follows from the class sum. At each marked pair,
\(\ell_h(s)\ne0\) because both \(b_i h_i\) are live, so both \(G_i\)
are live, opposite and nowhere supported by the dirty row.
The two normalized values differ:
\[
 k_{\rm first}-k_{\rm second}
   =\frac{G_{\rm first}(b_{\rm first}+b_{\rm second})}
           {b_{\rm first} b_{\rm second}}\ne0,\qquad k_i=G_i/b_i .
\]
In particular there are exactly five live numerical \(G\) labels.

It follows that
\[
 Z_5=E_5^\perp\cap\{T=0\}=G\mathcal P_2(Y),\qquad
 Z_6=E_4^\perp\cap\{T=0\}=G\mathcal P_3(Y)+K H .
\]
Indeed these spaces have dimensions three and five, respectively;
the pure \(G\) marks have the indicated annihilator grades. The genuine
companion \(H\) can be constructed afresh here, with no zero-weight
silent row. Let \(D_6(Y)=(Y-1)S_5(Y)\), where \(S_5\) is the monic
hull of the five nonendpoint labels. Put barycentric mass
\(\kappa/D_6'(s)\) at each of the six nonterminal numerical labels,
\(\kappa=-1/13860\). For each nonendpoint label, split this mass by
\(b_i/\mu_s\) on the two actual physical members; put the \(Y=1\)
mass at actual \(O\) itself. Set \(H_T=H_j=0\).
Its pure moments through degree four vanish by taking leading
coefficients in interpolation on those six distinct labels.
The \(g\) test is zero, and the \(h\) test uses the grouped fourth-head
zeros and \(h_O=0\). Thus \(H\in Z_6\); its nonzero numerical
class sums are independent of the \(G\) marks, which have class sums
zero.

In this gauge \(H_i/b_i=sJ_4(s)\) at any of the five nonendpoint
labels, where \(J_4(Y)=42Y^4-84Y^3+56Y^2-14Y+1\). To check it
directly let \(\mathcal L(Y)=Y D_6(Y)\) be the anchored degree-seven
hull. On the degree-six cardinal of \(s\) times \(J_4\), the true
ordinary degree-ten rule gives
\[
 \mu_s J_4(s)\mathcal L'(s)
 =\int_0^1 Y(Y-1)\frac{S_5(Y)}{Y-s}J_4(Y)\,dY
 =-1/13860=\kappa .
\]
The quotient \(S_5/(Y-s)\) is monic quartic; \(J_4\) kills the lower
terms for the \(Y(1-Y)\) moments. This proves both the explicit
companion and \(J_4(s)\ne0\) on every actual nonendpoint. It does
not assume anything about the physical output weight at \(O\).
Only the lift \(H\) uses class masses; all primitive and
commutator inputs retain the original literal weights.

For the ordinary projections the same degree-ten rule gives
\(S_5=(J_5+\alpha J_4)/132\), where
\(J_5=(2Y-1)(66Y^4-132Y^3+84Y^2-18Y+1)\).
Indeed \(\mathcal L\) times degrees \(0,\dots,3\) vanishes on
every weighted label, imposing the four fixed \(Y(1-Y)\)
orthogonality tests for \(S_5\). Their rank is four; \(J_4,J_5\)
give the degree-four and degree-five independent answers.
This checks all ordinary clock ingress for the exact resultants
below, not just the dimensions of the flag.

## 2. Pre-third and pre-fourth cuts with two weighted physical mates

Call the first five distinct weighted nonendpoint debuts
\(v_1,v_2,v_3,V,B\), in **physical** reverse order. Before the
third, no marked pair can complete. In fact, with
\(Q=Y(Y-v_1)(Y-v_2)\), the true inputs \(W(Q),W(YQ)\) vanish
on the inclusive slice up to any such completion. Their primitive
errors are in \(U_0,Z_5\). Comparing the two normalized weighted
rows at the repeated clock gives \(IQ=I(YQ)=0\) there. At
\(v_1\ne0\) these are \(v_1^3(2v_2-v_1)/12\) and
\(v_1^4(5v_2-3v_1)/60\), incompatible in characteristic zero.
The swapped formula treats \(v_2\) even if any other clock
intervenes. This is the
[paid two-clock cut](../dirk11-thirteen-invisible-local-slack-chronology/README.md#2-two-genuine-weighted-debuts-and-the-conditional-early-macro)
using its marked-pair proof only.

Define \(R=\prod_{i=1}^3(Y-v_i)\), \(P_0=YR\), and \(P\) of
degree at most three with zero constant and \(P(v_i)=k_i\) at each
first mate. \(P(v_i)\ne0\). Put \(D_0=G-W(P)\),
\(\mathcal C=YN-NY-N^2\). The paid flag equations in the
[pre-fourth completion proof](../dirk11-thirteen-invisible-local-late-early-completion/README.md)
and the [genuine folded fits](../dirk11-thirteen-invisible-local-slack-fourth-twin/README.md#1-actual-reversed-prefix-and-graded-rows)
are
\[
\begin{aligned}
 ND_0&=G\ell-W(IP),&
 N(YD_0)&=G(Y\ell-\rho)-W(I(YP)),\\
 NW(P_0)&=W(IP_0)-G W_0,& \mathcal C D_0&=0 .
\end{aligned}
\]
Here \(I\) is zero-constant primitive; \(\ell\) is affine and
\(\rho,W_0\) have degree at most two. For precision, \(NG\in U_0\),
\(N(YG)\in Z_5\), and the true degree-three and four primitive
errors respectively lie in \(U_0,Z_5\). The commutator on \(D_0\)
lies in \(Z_5\): the weighted charge is \(3+7+1=11\), using
\((CA-AC-A^2)E_5\subset F_7\), and the cubic mark uses
\(G\in E_7^\perp\) and one clock. Its old prefix is zero by triangularity,
so the three distinct live \(G\)'s kill the whole quadratic multiplier.
Consequently \(N^2D_0=G\rho-W(I^2P)\), and the three actual
zero-prefix reads give \(\ell=IP/P,\ \rho=I^2P/P,\ W_0=IP_0/P\)
at the old clocks. No claimed silence is used by these payments.

There is one genuinely different ingress in the no-slack chart.
The polynomial \(IP-\ell P\) vanishes at \(0\) and all three old
clocks, and so equals a scalar multiple of \(P_0\), possibly zero
at first. If zero, the valuation at zero and coefficient comparison
force \(P=\gamma Y^n\), \(1\le n\le3\), \(\ell=Y/(n+1)\).
The earlier silent chart found an unweighted live \(G\) to make
\(D_0\ne0\); here **any marked pair** makes \(D_0\ne0\), since the
two \(k_i\)'s differ and \(P\) has just one value on that clock.
The very first nonzero \(D_0\) is at a nonzero reverse clock:
\(T\) and \(j\) have \(D_0=0\), independently of the dirty clock.
At that first support the real scalar read
\((\mathcal C D_0)_i=-d_i^2 D_{0,i}\) gives \(d_i=0\);
the simultaneous \(ND_0=\ell D_0\) then gives
\(\ell(Y_i)D_{0,i}=0\), impossible. Thus \(IP-\ell P\ne0\).
Its degree-four term forces the actual degree of \(P\) to be
three. Scale both \(P,G\) by the inverse of that live leading
coefficient, giving the common monic gauge
\(IP=\ell P+\delta P_0,\ \delta=1/4-\lambda\ne0\),
where \(\lambda\) is the slope of \(\ell\).

Two completed marked pairs before \(V\) are impossible: the input
\(W(P_0)\) is zero on the literal prefix before \(V\) and each
completed old pair would force \(IP_0=0\) there by comparing its two
weights. Since \(P_0\) vanishes there and at zero, this would give
three distinct double roots of the nonzero degree-five \(IP_0\).
If exactly one pair completes before \(V\), the literal prefix must
therefore be \(T,v_1,v_2,v_3,i,V\), where \(i\) is the second
weighted mate of \(a\in\{v_1,v_2,v_3\}\). It is the first \(D_0\)
support; its diagonal is zero by \(\mathcal C D_0=0\).
Both \(D_0\)-primitives read zero on the two mates at \(a\);
the \(P_0\) input also reads zero on the complete prefix.
Their normalized head contrasts force
\[
 \ell(a)=\rho(a)=W_0(a)=IP(a)=I^2P(a)=IP_0(a)=0.
\]
These are exactly the actual two-weight ingress of the
[pre-fourth completion proof, §§1–2](../dirk11-thirteen-invisible-local-late-early-completion/README.md#1-an-actual-marked-repeat-supplies-the-old-contact).
The old-contact polynomial tower depends only on these three
primitive zeros and the five distinct ordinary hull labels, not the
existence of silent \(G\). It retains both assignments of \(V,B\).

There are now only the following true next rows after \(V\).
An old completion \(x\ne a\) or a fourth completion \(x=V\)
is excluded by the two repeat hinges in the rank-96 and
rank-48 old-contact algebras. The mixed commutator loses its
companion coefficient by comparing the **two weighted** old
mates at \(a\), since \(H_i/b_i=aJ_4(a)\ne0\) and the \(k_i\)
differ. If the next row is the distinct fifth \(B\), the
nonzero-diagonal matched quartics and the zero-diagonal
actual quintic alternative both apply. In the latter the paid
\(P_5=(Y-V)P_0\) has zero input through \(B\); its genuine error
\(GQ_5+\theta H\) fixes \(Q_5(a)=0\) by comparing the two
old weighted mates, and \(\theta=IP_5(a)/(aJ_4(a))\) from either.
This explicitly replaces the silent read of the
[earlier arithmetic](../dirk11-thirteen-invisible-local-slack-old-twin/README.md#3-actual-fifth-split-and-two-distinct-quadratics).
The checked fixed quadratic determinants exclude both \(B\)
diagonal branches without a leader assumption. There is no
silent continuation to test. Thus **no marked pair completes
before the fourth debut**.

## 3. Post-fourth and post-fifth transfer ledger

We have literal prefix \(T,v_1,v_2,v_3,V\).
If \(D_{0,V}=0\), the paid \(ND_0\) there would give
\(IP(V)=\ell(V)P(V)\), contrary to \(\delta P_0(V)\ne0\).
So \(V\) is a true mismatch and \(d_V=0\) by the first-support
commutator. Therefore the actual fourth reads are
\(k_V\ell(V)=IP(V),\ k_V\rho(V)=I^2P(V),\
k_VW_0(V)=IP_0(V)\), with \(e=\ell(V)\ne0\).
Both fourth and fifth \(G\) are live intrinsically in this
chart; no absent-head exclusion is needed.

* **Immediate fourth repeat.** The
  [same-fourth proof](../dirk11-thirteen-invisible-local-fourth-return/README.md)
  divides by the actual mate contrast
  \(G_i-b_i k_V\ne0\), not by a silent \(G\). Its two same-clock
  zero-diagonal rows separate the cubic and the \(H\) coefficient
  exactly by the weighted/weighted comparison. Nothing requires
  a later silent row: the next stage is an old completion or
  distinct \(B\), both covered by the nonminus and minus-one
  proofs, including both fifth-diagonal alternatives. In the
  nonminus quintic step the two actual fourth weights again
  replace the optional silent read, giving \(Q_5(1)=0\) and the
  one true \(\theta\). No rank or clock ordering assumption is
  imported from a silent slot.
* **Immediate old repeat.** The
  [old-event proof](../dirk11-thirteen-invisible-local-live-fourth-old-event/README.md)
  derives its normalized rank-one match on this marked member
  by comparing two actual weighted reads at the old root. Its
  degree-276 projection has no silent restriction. The very
  next row is a different old/fourth completion (the first
  old pair is already complete), or \(B\). The previous
  \(L\) unit tests on the fourth and both remaining old roots
  cover the completion cases. The degree-four matched read
  if \(d_B\ne0\) and degree-five error if \(d_B=0\) apply
  without change as their old normalization is paid by both
  weighted mates. No later physical stage is skipped.
* **Consecutive distinct fifth.** The
  [universal fourth/fifth pin](../dirk11-thirteen-invisible-local-late-fourth-pin/README.md)
  uses only the four live first \(G\)'s and then the literal
  fifth, so it applies exactly. In particular \(d_B\ne0\).
  The companion coefficient \(\theta\) and the actual mismatch
  \(f=k_B-\widehat P(b)\), in \(X=Y/V\) coordinates, are
  simultaneously zero or simultaneously live.
  If \(f=0\), the
  [matched-fifth proof](../dirk11-thirteen-invisible-local-late-matched-fifth/README.md)
  gives the exact degree-156 clock algebra. The next marked
  completion occurs at one of all five numeric labels and
  its nonzero paired \(\widehat D\) pays \(K_0=0\). The units
  over all three old clocks and fourth/fifth exclude these,
  omitting only the unnecessary silent-origin alternative.
  If \(f\ne0\), the
  [normalized consecutive fifth and fourth/fifth return proof](../dirk11-thirteen-invisible-local-mismatched-fifth-zero-head/README.md#2-the-next-literal-row-and-the-fourthfifth-returns)
  excludes both fourth and fifth returns using the actual
  two-weight comparison. Its zero fifth-head calculation is
  unnecessary. A remaining immediate old completion satisfies
  exactly the
  [degree-420 old-clock proof](../dirk11-thirteen-invisible-local-four-pair-closure/README.md#2-first-old-next-read-including-a-possible-matched-anchor).
  There the anchor possibility \(x=a\) is retained until the
  exact unit check, and the independent companion commutator
  uses only the earlier weighted mate and the same \(H/G\)
  line fixed by the four live first debuts. The entire residual
  clock algebra contradicts the paid commutator at this next
  old row. No assertion about an origin-clock silence or an
  unweighted twin is used in this transfer.

All rows following each certified prefix are present among the
ten marked actual rows. Thus these cuts exhaust the no-slack
chronology (before/at the first completion relevant to each proof),
and no pair folds, altered weights, or assumptions of identical
paired diagonals are used.

## 4. Exact reproduction and boundaries

**python3 verify.py** gives an independent exact check of Jacobi
orthogonality, the companion cardinal scalar, both initial
two-clock primitives, and the exhaustive physical pair-word
chronology. The words label clocks by order of first appearance
rather than numeric order; there are 945 such ten-row words,
partitioned into the 11 nonempty leaves printed by the checker.
The algebraic split \(f=0\) or \(f\ne0\) at B subdivides those
last word types and is proved by actual commutator reads, not
by the combinatorial script.

**bash replay.sh PATH/TO/RKResearch/ai-generated/research**
reruns only the relevant arithmetic source dependencies in
serial with SymPy and python-flint. The reused residue units
are interpreted in the reconstructed entire monic clock algebras;
the checked primes impose no restriction on the actual
characteristic-zero tableau or its coefficients. The symbolic
and chronological ingress is the written proof above. Existing
Lean scalar adapters for the predecessor cuts are separate;
this packet does not add a full Lean HasOrder theorem.

In the original grouped-square census the two-physical-dirty
case was already impossible, while three or more violate its
slot count. Consequently within this **normalized**
invisible one numerical cubic-dirty clock, grouped
\(\beta h=0\), grouped \(\beta h^2\not\equiv0\) and multi-label
\(G\) slice, neither one-physical-dirty allocation survives.
This does not exclude the one-label \(G\) slice or promote the
calculation to an unrestricted lower bound.
