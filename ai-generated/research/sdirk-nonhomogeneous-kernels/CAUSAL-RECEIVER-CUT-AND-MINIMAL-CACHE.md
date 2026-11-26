# Exact causal receiver criterion and the next-row obstruction of the minimum cache

This note uses the elementary stage derivative convention, polynomial model \(g_t\), and exact dense rank of `DENSE-POLYNOMIAL-DONOR-MINIMUM.md`, and the first-excess bound of `PAID-DONOR-BAND-MINIMUM.md`. Put \(P_n=K[X]_{<n}\). When asking for grade \(n+1\), take a field in which all casts of \(1,\ldots,n\) are nonzero. No real ordering is needed except where explicitly stated. Old stages may have arbitrary chronological rows; there is no assumption they are individually exact, or that their clocks are distinct.

## Exact row-by-row gate

Let \(E_n, G_n\) be the two linear maps on formal combinations of trees of grades at most \(n\), taking a tree to the old actual elementary column \(\Phi_t\) and to the exact polynomial \(g_t\), respectively. Define the relation space seen in the exact model by
\[
 U_n=G_n(\ker E_n)\subseteq P_n.
\]
Take a new prescribed diagonal \(\gamma\ne0\), and \(T=\mathcal I-\gamma\). A new stage with clock \(\xi\) and arbitrary strict coefficients on the old rows is individually exact, \(\Phi_{\text{new},t}=g_t(\xi)\) through grade \(n+1\), **if and only if**
\[
                 (T U_n)(\xi)=0. \tag{1}
\]
Necessity follows from the unary tree with child \(t\): the strict input functional on \(E_n(t)\) must give \((Tg_t)(\xi)\) for every paid child. For sufficiency, (1) makes that scalar functional well-defined on \(\operatorname{im}E_n\); extend it linearly to the whole old stage-coordinate vector space and use it as the strict row. Its row sum is \((T1)(\xi)=\xi-\gamma\), so the actual clock is \(\xi\). Induct on tree grade: each state factor for a paid child is \((Tg_t)(\xi)+\gamma g_t(\xi)=\mathcal I g_t(\xi)\); then take products. Thus the gate inserts an actual row, not just scalar or tall tests. A solution may be chosen over the field of the input entries and \(\xi,\gamma\), by linear elimination.

The operation \(T\) is injective (it raises the degree of a nonzero polynomial), and the admissible clocks are precisely field roots of the gcd of \(T U_n\) unless \(U_n=0\), in which case all clocks are allowed. If \(\dim U_n=d>0\), the gcd has degree at most \(n+1-d\), because its multiples of degree at most \(n\) form a space of dimension at most \(n+1-\deg\gcd\). Adding an individually exact row updates \(U_n\) exactly to \(U_n\cap\ker\operatorname{ev}_\xi\), since the new actual map has the additional coordinate \((G_n(t))(\xi)\). In particular, if every admissible clock also kills \(U_n\), repeating this type of exact receiver cannot reduce the obstruction; if the gcd has no field root one cannot start this type of receiver at all. This is a chronological criterion, not a general obstruction to inserting stages of a lower individual accuracy.

## Rank cost for independently fed anchors

Suppose the old diagonal entries are all nonzero, and \(r\) distinct new individually exact grade-\((m+1)\) receivers with common diagonal \(\gamma\) are to use those same old rows, with no edges among the new receivers. The strict rows must decode the target \(\lambda(P)=((TP)(\xi_i))_{i=1}^r\) through grade \(m\). The signed stage bound of the dense-decoder note applies directly: the required number of old rows is at least \(\sum_{j\ge0:\ n=m-2j>0} \operatorname{rank}(\lambda|_{P_n})\).

The ranks here can be evaluated exactly. Define \(\Lambda_\gamma(X^a)=a!\gamma^a\) through degree \(m\), and let \(H=\prod_i(X-\xi_i)\). The image of \(T:P_n\to P_{n+1}\) is the codimension-one kernel of \(\Lambda_\gamma\): inclusion follows on monomials and dimensions are equal. If \(r>n\), distinct evaluations are injective on this image, and the rank is \(n\). If \(r\le n\), the polynomial kernel on the image is \(H P_{n+1-r}\cap\ker\Lambda_\gamma\); hence the rank is exactly \(r\) unless \(\Lambda_\gamma(H P_{n+1-r})=0\), in which case it is exactly \(r-1\). This classifies possible loss, including all degenerate families; it does not posit general-position sites. Over the reals with \(\gamma\ne0\), \(\Lambda_\gamma(P)=\int_0^\infty P(\gamma x)e^{-x}\,dx\). Consequently if \(n\ge2r\), testing \(H^2\) rules out the loss. A Laguerre hull \(H=W_r\) does exhibit the loss for \(r\le n\le2r-1\). There is no asserted attainment for all prescribed anchors.

## No direct grade-\((q+2)\) receiver after the exact minimum-width cap-\(q\) cache

Now take characteristic zero and common diagonal \(\gamma\ne0\). Use the cached Laguerre construction at cap \(q\) in the companion note, with any allowed choices of selected roots at all layers. The construction has \(L(q)\) actual rows, so its tree columns through grade \(q\) span the entire stage vector space: the \(L(q)\) independence witnesses in that lower bound lie in their span. If \(D\) is its reconstructed chart, for grade \(q+1\) this implies
\[
 U_{q+1}=\operatorname{span}\{g_t-D\Phi_t:|t|=q+1\}. \tag{2}
\]
Indeed, subtract from each new tree a combination of paid old trees representing its actual column; the exact polynomial of that difference is the error displayed in (2). Conversely apply \(D\) to a relation to see that its exact polynomial is an error combination. The first-excess lower bound gives \(\dim U_{q+1}\ge\lfloor q/2\rfloor+1\).

For the matching upper bound, let \(F_k\) be the full nominal chart and \(\widehat F_k\) the actual cache chart at layer \(k\). At the one off-cap grade \(q+1\), all children in a stage formula have paid grades through \(q\), so the actual and full nominal samples at every selected site still agree. Thus \(R_k=F_k-\widehat F_k\) vanishes at those sites. Put \(L_k=\max(0,2k-1-q)\), the number of cached low coefficients. Let \(J_k\) be the linear lift of these low coefficients to a degree-\(<k\) polynomial vanishing at the selected sites, unique by high-mode interpolation. If \(L_k=0\), \(R_k=0\). Otherwise the only possibly missing new low coefficient of \(F_k-F_{k-1}\) is that of \(W_{L_k-1}\), because the full band at grade \(q+1\) begins at \(2k-2-q\) for this difference. Thus, tree by tree at grade \(q+1\),
\[
 R_k=J_k\operatorname{low}_k R_{k-1}+\eta_{k,t}J_k W_{L_k-1}. \tag{3}
\]
There is one new fixed polynomial direction for each of the \(\lfloor q/2\rfloor\) caching layers. The full model error at the last layer is a multiple of \(W_q\) by its nominal band. Therefore (2) is contained in the span of \(W_q\) and these \(\lfloor q/2\rfloor\) lifted directions, propagated by (3). The lower bound forces equality with that span and its full dimension. In particular, for \(q\ge2\), it contains \(W_q\) and the last-layer direction
\[
 Q=W_{q-2}-\frac{W_{q-2}(x_*)}{W_{q-1}(x_*)}W_{q-1},\qquad W_q(x_*)=0,
\]
where \(x_*\) is the only selected last-layer root. This reasoning does not require finding any individual tree that isolates the indicated directions.

If a new row of the **same** diagonal were individually exact through \(q+2\), then (1) forces \(W_{q+1}(\xi)=0\) from \(TW_q\), and \((TQ)(\xi)=0\). The three-term recurrence at \(W_q(x_*)=0\) and at \(W_{q+1}(\xi)=0\) gives
\[
 \frac{W_{q-2}(x_*)}{W_{q-1}(x_*)}=
 \frac{x_*-(2q-1)\gamma}{\gamma^2(q-1)^2},\qquad
 \frac{W_{q-1}(\xi)}{W_q(\xi)}=
 \frac{\xi-(2q+1)\gamma}{\gamma^2q^2}.
\]
Adjacent modes have no common roots. Substituting into \(TQ=W_{q-1}/(q-1)-(W_{q-2}(x_*)/W_{q-1}(x_*))W_q/q\) forces
\[
                 \frac{\xi}{\gamma}=\frac{q(x_*/\gamma)-1}{q-1}. \tag{4}
\]
Thus any candidate clock, in any coefficient extension, must satisfy the two elementary conditions (4) and \(W_{q+1}(\xi)=0\). The row factorization criterion (1) and this shared-root filter do not require an irreducibility input.

### Ordinary Laguerre irreducibility corollary (characteristic zero)

The precise arithmetic input is Schur’s theorem for the ordinary Laguerre polynomial \(L_n\) (parameter exactly zero): the monic polynomial \((-1)^n n! L_n(X)=\sum_{j=0}^n(-1)^{n-j}\binom nj n!/j!\,X^j\) is irreducible over \(\mathbb Q\) for every \(n\ge1\). See I. Schur, *Einige Sätze über Primzahlen mit Anwendungen auf Irreduzibilitätsfragen, I*, Sitzungsber. Preuß. Akad. Wiss. Berlin, Phys.-Math. Kl. (1929), 125–136 (ordinary case); the valuation argument with Sylvester’s theorem is given below. No generalized Laguerre claim is used.

Now (4) is impossible: the normalized root \(x_*/\gamma\) has algebraic degree at most \(q\) over the prime field \(\mathbb Q\), hence so would \(\xi/\gamma\); yet the latter is a root of ordinary \(L_{q+1}\) and has degree \(q+1\). This is a statement about the particular normalized algebraic numbers over \(\mathbb Q\), so extending the old coefficient field or adjoining further Laguerre roots cannot change it. The normalization works for any nonzero \(\gamma\), even if it is not algebraic over \(\mathbb Q\).

For an arithmetic verification of the irreducibility input using Sylvester's prime-divisor theorem, write the monic ordinary Laguerre coefficients as \(a_j=(-1)^{n-j}\binom nj n!/j!\). If a monic rational factor had degree \(1\le k\le n/2\), use Sylvester's theorem on the last \(k\) integers through \(n\) to choose a prime \(p>k\) dividing their product. The residue \(r=n\bmod p\) is then below \(k\). The first coefficient not divisible by \(p\) is \(a_{n-r}\): lower ones have \(p\mid n!/j!\), and the binomial coefficient at \(j=n-r\) is a unit. Thus there are only \(r\) roots of valuation zero, counting multiplicity, by reducing a monic factorization over an algebraic closure of the \(p\)-adic field. All roots are integral and every positive valuation is strictly below \(1/k\): for \(j>0\), \(v_p(a_0)-v_p(a_j)\le v_p(j!)<j/(p-1)\le j/k\), so at valuation at least \(1/k\) the constant term would be uniquely minimal. The proposed factor must contain a positive-valuation root but its constant term valuation is then strictly between zero and one, impossible for a nonzero rational number. This is the classical argument in the ordinary Laguerre case.

**Conclusion.** One cannot take the exact minimum-width cap-\(q\) cache, for \(q\ge2\), and append any single same-diagonal row that is individually exact through \(q+2\), regardless of its old-row coefficients or where its clock is chosen. At \(q=1\), the extra obstruction is absent and roots of \(W_2\) work. If the prep is instead paid through cap \(q+1\), the cached band makes the first excess a single \(W_q\) direction, and any root of \(W_{q+1}\) works via \(TF_q\). This is an all-rooted, individual-row gate and a precise extra-cap benefit; it does not claim a lower bound for an ordinary fixed-output method that is permitted to use inexact intermediate stages.
