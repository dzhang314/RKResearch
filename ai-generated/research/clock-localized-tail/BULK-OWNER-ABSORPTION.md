# Bulk absorption of scalar owners in reflected strict SDIRK

The construction deletes contributing scalar owners, rather than only their negative reference rows. It gives an asymptotically sharp stage bound for strict SDIRK at every fixed nonzero real-algebraic diagonal. The unrestricted stage table through order twenty is unchanged.

## 1. Actual setup

Work over a characteristic-zero field, with literal common diagonal \(\gamma\), and put \(J_\gamma=I_0-\gamma I\) and \(J_\gamma^*=I_1-\gamma I\). Here \(I_0\) and \(I_1\) are the lower and upper polynomial primitives. Work first with the shifted strict matrix; edge contraction transfers all paid equations back to ordinary RKOC. Denote the exact shifted profile by \(G_t\). For grade \(|t|\), it has degree at most \(|t|-1\). Let \(p=m+r\) with \(r\le m\). A genuine old closed forward donor with numerical columns \(\mathbf e(t)\) has a linear decoder \(D_F\) exact through size \(m-1\). Its pure scalar rows at the logical clocks \(x_a\) have strict feed \(E_{x_a}J_\gamma D_F\), where \(E_xP=P(x)\). Thus their shifted entries are evaluations of the single polynomial
\[
 V_t(X)\coloneqq\prod_{u\text{ child of }t}J_\gamma D_F\mathbf e(u)(X).
\]
It has degree at most \(|t|-1\) even beyond exact dense order, provided \(D_F\) has output degree at most \(m-1\). The degree statement uses exact lower profiles and the high codomain cap. It is a statement about the **true pure row**, not equality with \(G_t\) above its paid grade. In particular every pure row is locally exact through size \(m\). Set \(\mathbf V(t)\coloneqq(V_t(x_a))_a\) and \(\mathbf V_{-1}(t)\coloneqq (D_F\mathbf e(t))(x_a)_a\). All these actual pure rows follow the closed forward donor and precede each physical plus row. They have no edges among themselves.

Take an actual reverse donor with shifted strict matrix \(B_R\), actual clocks \(y_i\), and a linear decoder \(D_R\). For the minimum cached Laguerre chart, every actual reverse row has a distinct clock. Choose the \(q\) logical scalar owners to include all its reflected sites \(x_i=1-y_i\). Use a scalar rule \(\mathbf b\) of precision \(p-1\) on the owners. Initially use **the pure row** at each reflected clock as the minus reference for its corresponding plus. In the reversed chronological order put \(T=\operatorname{rev}(B_R^{\mathsf T})\), which is strictly lower triangular, and write \(C_+\) for the plus clock diagonal. Use the fixed reflected source matrix, with indices in the physical plus order,
\[
 S_{i,a}\coloneqq b_a\bigl(J_\gamma^*\mathcal R D_R\mathbf e_i\bigr)(x_a),
 \qquad \mathcal R P(X)\coloneqq P(1-X).
\]
The unit initial plus weights are denoted by \(\mathbf w=\mathbf1\); the same weights are subtracted at their older pure minus rows. If the reverse chart is exact through size \(r\), this architecture has exact rooted order through \(p\) by the reflected paired proof, summarized in §5. If only a shorter reverse chart is used, **assume the missing paid pairings have independently been restored** (for example by the one-short first-excess Gram and physical head-probe tests). The compression below takes such a verified exact-order baseline; it does not prove those head tests merely from a nominal cap.

For a paid tree with unique active child \(u\) of size at least \(m\), write \(P\) for the product of its other exact shifted primitive factors. The actual contrast \(\boldsymbol\delta\), the plus column minus its corresponding pure column, satisfies
\[
 \boldsymbol\delta(t)=P(C_+)\bigl(S(\mathbf V-\mathbf V_{-1})(u)+T\boldsymbol\delta(u)\bigr).
 \tag{1}
\]
Without such a child the contrast is zero. This holds because \(p\le2m\), the pure and plus rows have the same real clock, and the smaller child factors are exact. The whole shifted output is \(\mathbf b\cdot\mathbf V+\mathbf w\cdot\boldsymbol\delta\).

## 2. Literal absorption theorem

Let \(A_0\) be a set of owner clocks to be deleted; each must be a distinct reflected reverse clock with nonzero scalar weight \(b_a\). Let \(i(a)\) be the unique corresponding actual plus row. For each \(a\in A_0\), choose an old numerical predictor \(\pi_a(t)\) of \(V_t(x_a)\), using a fixed linear read of the closed forward donor and the **retained** pure owner rows only. Require agreement through some grade \(g_a\ge m-1\); no earlier same-clock forward stage is required. The prediction is optional when the corresponding column defect below is identically zero.

First reweight the actual plus rows so that \(w'_{i(a)}=b_a\) for every deleted site, with unit weights elsewhere. Define the diagonal invertible matrix \(C_s\) by \((C_s)_{ii}=w_i/w'_i\), and replace the literal contrast taps by
\[
                        S'=C_sS,\qquad T'=C_sTC_s^{-1}.
\]
The actual contrast becomes \(C_s\boldsymbol\delta\) on all paid trees by (1), since clock multiplication commutes with the row scaling. This is a change to the strict taps only; it is not a similarity scaling of the physical full \(A\) or its diagonal. Copy the same old pure baselines as before. Their small factors and genuine clocks do not change. Output \(\mathbf w'\cdot C_s\boldsymbol\delta=\mathbf w\cdot\boldsymbol\delta\), so paid order is unchanged.

Now write the strict taps of each plus in terms of its **absolute** plus-stage input, rather than a named contrast. The pure row at \(a\) has net output weight \(b_a-w'_{i(a)}=0\). All its remaining strict outgoing coefficients form exactly the column
\[
           h'_a\coloneqq S'_{:,a}-T'_{:,i(a)}
                    =C_sh_a,\qquad h_a\coloneqq S_{:,a}-b_a T_{:,i(a)} .
           \tag{2}
\]
The pure row did not feed any other pure owner. Its same-clock plus baseline is the literal old donor row \(E_{x_a}J_\gamma D_F\) and does not use the deleted pure stage. Delete the pure coordinate and replace the strict outgoing tap \(h'_a V_t(x_a)\) by \(h'_a\pi_a(t)\) wherever \(h'_a\ne0\). These new taps are all earlier than every plus row. Row sums remain unchanged, since \(\pi_a(\bullet)=V_\bullet(x_a)=1\) on every live replacement; zero columns require no such prediction. Thus no new stage, diagonal change, or noncausal reference is introduced. The aggregate weight \(b_a\) moves to the retained same-clock plus. This is not counting a minus alias and a scalar deletion twice.

Here is the sufficient moment test. For each \(a\), require that \(h_a\) be killed by the actual reverse word rows of length at most \(p-g_a-2\) from \(\mathbf w\), in the two letters \(T^{\mathsf T}\) and \(C_+\). A negative cap gives no condition; \(h_a=0\) is always sufficient without a predictor. To prove this, compare the retained absolute plus stage columns after the deletion with the rescaled baseline. Each injected input difference is \(\pi_a(u)-V_u(x_a)\), zero through \(g_a\). The true changed plus-column error cannot start before \(\min_a g_a+2\). All paid products have at most one child that can carry these differences, since \(g_a\ge m-1\) and \(p\le2m\). Other sibling factors equal the exact shifted polynomials at the true clocks. The error \(d(t)\) in retained plus columns therefore obeys exactly
\[
 d(t)=P(C_+)\left(T'd(u)+\sum_a h'_a(\pi_a(u)-V_u(x_a))\right).
 \tag{3}
\]
A source at size at least \(g_a+1\) needs one further strict primitive to reach a parent, so any contribution to the paid final scalar tests \(h'_a\) with a reverse word of length at most \(p-g_a-2\). Diagonal scaling intertwines each such retained moment: \(\mathbf w'^{\mathsf T}\) on words in \(T',C_+\) acting on \(h'_a\) gives \(\mathbf w^{\mathsf T}\) on the old word acting on \(h_a\). This proves the sufficient test. A sum of correlated source responses might vanish under weaker conditions; the theorem does not claim each separated moment is necessary.

The measured comparison in the original reverse order is especially simple: \(h_a/b_a\) on any actual reverse word column \(z\) is
\[
                   (E_{y_{i(a)}}J_\gamma D_R-(B_R)_{i(a),*})z .
                   \tag{4}
\]
Thus actual local reverse order at least \(p-g_a\), and a paid reverse decoder through \(p-g_a-1\), suffice. More generally directly test (4) on the actual word span. In the minimum actual reverse chart of cap \(s\), its last row is genuinely local-\((s+1)\), and the paid numerical columns through \(s\) span the entire reverse bank. Hence its (4) vanishes on arbitrary data, **even when \(s=r-1\)**. The separate pure scalar coordinate opposite it can be deleted with no earlier predictor at all. Only the true last-row identity is being invoked. A penultimate row has local order \(s\), enough for a shorter tested band but not in general for arbitrary full data.

There is also a reusable actual-head screen for the predictor itself. At a given cap \(g\), the true functional \(t\mapsto V_t(x_a)\) must kill the kernel of the stacked measurement of the closed old forward and retained pure-owner data at that cap. This is the exact factorization condition; at caps above \(m\) do not substitute \(G_t(x_a)\) without an actual proof. At cap \(m\) a repaired head's quotient read can supply the desired evaluation precisely when its true model kernel is killed by \(E_{x_a}\). A mixed head probe of the form \(E_{x_a}-\mathcal L\) is **not** by itself an individually exact grade-\(m\) stage or a true \(E_{x_a}\) predictor. One must check a numerical lift of the missing \(\mathcal L\) on its actual unary boundary as well. This distinguishes which earlier chart is genuinely available.

## 3. Simultaneous, explicit predictors and count

If \(b_0\) pure owners remain, use their common degree-\(<b_0\) cardinals evaluated at each deleted \(x_a\) as the predictor. This is one literal old read, paid through \(g=b_0\) for **every** deleted owner, because \(V_t\) is always a polynomial in the clock of degree at most \(|t|-1\). Every retained pure row remains unchanged; hence sharing their numeric data does not presume a virtual receiver at the deleted site. This is exact cardinal evaluation at a paid grade, not extrapolation of unverified high columns.

For the minimum cached reverse chart of cap \(s\) (either \(s=r\) or a genuinely completed one-short \(s=r-1\)), a level-\(k\) row is actually local-\((k+1)\). Let
\[
 R_k\coloneqq \sum_{j=k}^{s}\min(j,s+1-j),\qquad 1\le k\le s .
\]
All its literal clocks are distinct. One can choose any \(D_{\mathrm{del}}\) reflected owners from levels at least \(k\) for the bulk interpolation deletion provided
\[
             D_{\mathrm{del}}\le R_k,\qquad
             q-D_{\mathrm{del}}\ge p-k-1 .
             \tag{5}
\]
Indeed set \(g=q-D_{\mathrm{del}}\) (or a smaller paid cap if this exceeds \(p\)). The actual reverse row pays (4) through degree \(p-g-1\le k\), and its decoder is genuinely exact there. Because \(k\le s\le r\), the required grade is at least \(m-1\); if the cap is greater than \(p\), no issue arises. The remaining pure count is \(q-D_{\mathrm{del}}\), not a claimed drop in aggregate contributing quadrature support: each removed weight is carried by a surviving plus at its true clock. Independently the last level can always remove its matched owner via the zero-column gate, even if (5) fails for that one site.

For \(q\ge p+1\), maximizing \(\min(R_k,q-p+k+1)\) near the top removes at least \(s-O(\sqrt{s})\) rows (choose about \(\sqrt{2s}\) top levels whose sizes are \(1,2,\ldots\)). When the required reflected pin count is quadratic and exceeds \(p\), a simpler strategy leaves just \(p-2\) pure owners, retaining any scalar site not reflected. Every reverse row then passes the only remaining zeroth-word condition in (4), which is merely the row-sum identity and the true decoded leaf. The omitted donor effect begins as a child of size \(p-1\), so only a final unary equation can see it. This removes all other reflected pure rows, often quadratically many. It is a range statement, not a hand-tuned one-order row elimination.

For application to a one-short chart, the forward repair and its true missed-word pairing are untouched: choose any old scalar grid including those reflected clocks, apply that paid exactness proof, then apply the present absorption as a separate causal transformation. The transformation uses no auxiliary coincidence between the diagonal that caused the rank loss and a pre-existing forward clock. If a truly local old forward row at a is available, the earlier genuine-owner adoption theorem can alternatively reassign its coefficient there with its own measured gate. Do not count that same scalar row again after absorption. If the existing earlier row is only a mixed observation or an outgoing reference, it is not a new exact stage chart without the kernel test above.

## 4. Exact next order and the unconditional broad family

The scalar aggregate masses and all their clocks are identical after reweighting and deletion, degree by degree. Thus an actual failed degree-\(p\) scalar moment remains the next bush failure, independent of interactions at the first unpaid other roots. In any permitted enlargement of the logical owner grid to \(q\ge p+1\) distinct real-algebraic sites, the affine solutions for degrees \(0,\ldots,p-1\) include choices with every \(b_a\ne0\) and degree-\(p\) failure. Each single coordinate is variable because any \(p\) distinct other sites span the first \(p\) moment rows; the degree-\(p\) row is independent of those moments. Avoid the finitely many forbidden hyperplanes in this affine space by a choice over the same real algebraic field. This works with all specified reflected pins. If the only known previous exactness witness was a non-bush next tree, rescaling the contrasts may change it outside the one-active budget. A separately established shifted tall obstruction survives when the new strict depth is still bounded appropriately, but earlier scalar exactness alone does not establish the next failure.

Take now the **full** cached reverse donor for every \(p\ge6\), with \(m=\lceil p/2\rceil\), \(r=\lfloor p/2\rfloor\), at any prescribed nonzero real-algebraic diagonal. Use the actual minimum forward donor of cap \(m-1\) and reverse donor of cap \(r\). There are \(d=L(r)\) distinct reverse normalized Laguerre clocks, where \(L(j)=\lfloor(j+1)^2/4\rfloor\). Put \(q=\max(p+1,d)\) logical owners including their reflections, with a paid rule and the genuine bush failure above. The number of non-reflected owners is \(q-d\), which is at most \(p-2\) since \(r\ge3\). Therefore one can retain exactly \(p-2\) pure owners while deleting only reflected ones. The previous construction gives an exact order-\(p\) strict SDIRK tableau over the real algebraic numbers with
\[
           L(\lceil p/2\rceil-1)+L(\lfloor p/2\rfloor)+p-2
                  = p^2/8+O(p)
             \tag{6}
\]
actual physical stages. This is unconditional at the prescribed diagonal and does not assume an actual one-short rank loss. It is a leading-asymptotic improvement of the reflected packing, not a replacement for the specialized small-order table.

For comparison, the familiar invertible-commutator lower basis proves the same leading constant. For \(n=p-2j>0\) choose \(\min(n,p-n+1)\) monomials of lowest degrees. The numerical vectors \(\Pi^j C^i\mathbf1\) with \(\Pi=[C,A]-A^2\) are independent: divide any relation by its smallest power of the invertible \(\Pi\) and use the paid polynomial tests \(\mathbf b\cdot Q(C)\) for \(\deg Q\le p-n\). The formal commutator vanishes on all positive powers; the remaining Hilbert minor of \(\ell(Q X^i)\) is invertible. These bounds sum to \(p^2/8+O(p)\). Thus the minimum strict SDIRK stage count at every fixed nonzero real-algebraic diagonal has limiting coefficient \(1/8\) over the reals/real algebraics. This is a statement about algebraic classical order, with no stability or sign constraints. The same literal owner transformation works for ERK if supplied actual exact reverse and forward charts, but the strict commutator lower and this cached sharp rate do not transfer to ERK merely by setting \(\gamma=0\).

## 5. Why the full baseline is exact

Let \(M=E J_\gamma R_q\) on the \(q\) logical scalar owners, with cardinal interpolation \(R_q\). A moment against \(f\) can move one \(M\) to \(J_\gamma^* f\) when the represented input degree plus \(\deg f+1\) is within the true scalar precision. Weighted dense rooted order follows inductively: all small children fit interpolation; if some child is larger than the owner degree budget, it is unique because \(2q\ge p\), and transfer its primitive via the weighted adjoint. The virtual repeated \(M\) layers starting at \(E D_F\) agree with the dense weights after enough extensions. At each correction the unique large child supplies one real source \(\mathbf V-\mathbf V_{-1}\), while all other factors are exact small polynomials; the virtual differences expand as a sum along the actual spine. Every word before its final source has grade ≤r on the reverse bank. Reflection of the shifted primitive, exact reverse decoding through r, and the final \(J_\gamma^*\) in \(S\) give equality term by term. Each adjoint is paid on an input polynomial of degree ≤ its tree size minus one. The physical common diagonal is preserved by literal pure strict feeds and contrast inputs that sum to zero on the leaf. This supplies the exact baseline to which §§2–4 apply. For a genuinely one-short baseline one must independently pay its missing boundary comparison; this note neither assumes a singular line is physically repairable nor alters the earlier durable errata.
