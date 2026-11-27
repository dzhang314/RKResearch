# Eleven stages cannot have a full four-dimensional pure head at order eight over the rationals

For a strictly lower triangular tableau \(A\), write \(\boldsymbol{c}=A\boldsymbol{1}\). For a rooted tree \(t\) of size \(n\), let \(t!\) denote the tree factorial and \(\boldsymbol{\Phi}_t(A)\) the reviewed stage vector. Define
\[
 V_5=\operatorname{span}_{\mathbb Q}\{\boldsymbol{\Phi}_t(A)-(n/t!)\boldsymbol{c}^{n-1}:1\le n=|t|\le5\}.
\]
An eleven-stage rational explicit tableau with order eight **cannot have**
\[
 V_5=H:=\operatorname{span}(\boldsymbol{e}_2,\boldsymbol{e}_3,\boldsymbol{e}_4,\boldsymbol{e}_5).
\]
The first equality is an assumption on the whole actual defect space, not an assumption of dimension four alone. In particular a defect extending into a later stage falls outside this result. No sign, node-distinctness, prescribed reverse taps, quadrature-support size, terminal clock, or coefficient-denominator hypothesis is imposed. The unrestricted eleven-stage rational problem remains open.

## 1. Five rational output sites including zero cannot pay order eight

Suppose an output quadrature integrates degrees \(0,\ldots,7\) on sites contained in \(0,a,b,c,d\) with rational coordinates. The other four sites may include arbitrary extra sites if the support is smaller; a listed site may have weight zero. Let
\[
 Q(x)=(x-a)(x-b)(x-c)(x-d)=x^4-rx^3+s x^2+t x+u .
\]
Since \(xQ(x)\) vanishes at every site and has degree five, the quadrature implies
\[
 \int_0^1 xQ(x)\,dx=\int_0^1 x^2Q(x)\,dx=\int_0^1 x^3Q(x)\,dx=0 .
\]
Solving these three linear equations for \(s,t,u\) gives
\[
 7s=12r-15,\qquad 7t=10-6r,\qquad 70u=8r-15.
\]
Thus
\[
 70Q(x)=70x^4-70rx^3+(120r-150)x^2+(100-60r)x+(8r-15).
\]

Work in the local ring of rationals whose reduced denominators are prime to seven.

* If \(r\) is integral in this local ring, every rational root \(x\) is too. If a root has negative valuation \(v=\nu_7(x)\le-1\), the leading term has valuation \(1+4v\), strictly below the bounds \(1+3v,2v,v,0\) for the other terms. Equivalently, clear the denominators and reduce modulo \(7^2\): if \(7\mid\operatorname{den}(x)\), every term except the leading one is a multiple of \(7^2\), whereas its valuation is one. All four roots would therefore be integral. Then \(s,t\) are integral. The first two displayed coefficient identities reduce to \(12r=15\) and \(6r=10\) modulo seven; subtracting twice the latter gives \(5=0\), a contradiction.
* If \(r\) is not integral in this local ring, divide \(70Q\) by \(r\). Reducing gives \(x^2+3x+1\) modulo seven, with discriminant \(5\), a nonsquare. Consequently no rational root is integral. All four inverse roots then reduce to zero. But the sum of their pair products is \(s/u=(120-150/r)/(8-15/r)\), which reduces to \(1\). This contradicts the zero sum of the products of the inverse roots. The division by \(u\) is legitimate since \(8-15/r\) is a local unit.

This is purely rational arithmetic. The [Lean arithmetic certificate](../../lean/RKCert/ReviewedNative/OrderEightRationalEndpointSupport.lean) formalizes it by integer clearing and reduction modulo seven and proves it directly for the reviewed **HasQuadratureOrder** predicate. No floating-point valuation or search is used. Primary theorem: **RKResearch.Certified.OrderEightRationalEndpointSupport.no_order_eight_on_five_sites**. In ai-generated/lean run:

    lake build RKCert.ReviewedNative.OrderEightRationalEndpointSupport

Lean/Mathlib 4.36 reported only the standard axioms propext, Classical.choice and Quot.sound. Sections 2–4 below are the mathematical tableau proof, not a claimed Lean formalization. Run **python3 check.py** in this directory for the independent exact scalar receipts and the example showing that six rational sites do suffice for the scalar quadrature with endpoint zero.

## 2. All relevant taps are silent on the specified head

Let \(\boldsymbol{b}\) be the output row, and put \(\boldsymbol{B}=\boldsymbol{b}^\top A\), \(\boldsymbol{D}=\boldsymbol{b}^\top CA\) with \(C=\operatorname{diag}(\boldsymbol{c})\). Exact rooted order gives, for each tree \(t\) of size \(n\),
\[
 \begin{aligned}
 \boldsymbol{b}^\top\boldsymbol{\Phi}_t&=1/t!,\\
 \boldsymbol{b}^\top C^k\boldsymbol{\Phi}_t &= n/((n+k)t!)&& (n+k\le8),\\
 \boldsymbol{B}\boldsymbol{\Phi}_t&=1/((n+1)t!)&& (n+1\le8),\\
 \boldsymbol{D}\boldsymbol{\Phi}_t&=1/((n+2)t!)&& (n+2\le8).
 \end{aligned}
\]
These come respectively from \(t\), adding \(k\) leaves to its root, grafting one unary root, and grafting a root with children \(t\) and one leaf. For a bush of size \(n\), the same identities give the corresponding moments on \(\boldsymbol{c}^{n-1}\). Hence \(\boldsymbol{b}^\top,\boldsymbol{B},\boldsymbol{D}\) kill every defect defining \(V_5\). The pure-head hypothesis says they vanish individually on coordinates \(2,3,4,5\).

The seven nominal clock slots on which their coefficients may survive are
\[
 \{1,6,7,8,9,10,11\}.
\]
The first stage has clock zero by explicitness. By Section 1 there are at least six distinct clock values in those seven slots. Thus there is at most one pair of equal clocks, and no triple. This conclusion did not assume the final clock was one, or that each listed slot had a nonzero weight.

## 3. A paired discrepancy forces literal equality of the rows

Consider the two reverse discrepancies
\[
 \boldsymbol{\lambda}_B=\boldsymbol{B}-\boldsymbol{b}^\top(I-C),\qquad
 \boldsymbol{\lambda}_D=\boldsymbol{D}-\boldsymbol{b}^\top(I-C^2)/2 .
\]
The same rooted identities imply \(\boldsymbol{\lambda}_B\boldsymbol{\Phi}_t=0\) for every \(n\le7\), and \(\boldsymbol{\lambda}_D\boldsymbol{\Phi}_t=0\) for every \(n\le6\). In particular these are stronger than the vanishing of bush moments.

First apply this to \(\boldsymbol{\lambda}_B\). Using bush powers through degree six and interpolating on the at most seven nominal clock values shows that the sum of its coefficients on each clock fibre is zero. If it is nonzero, all its support is therefore the single equal-clock pair \(i<j\), with coefficients \(\tau,-\tau\) for \(\tau\ne0\). It follows that stages \(i,j\) agree on every \(\boldsymbol{\Phi}_t\) through size seven. Taking unary grafts says their padded matrix rows agree on all \(\boldsymbol{\Phi}_t\) through size six. They agree on clock powers through degree five, and on \(V_5=H\), since each generator is a combination of \(\boldsymbol{\Phi}_t\) and such a power.

The difference of the two padded rows now has support only on the nominal slots **strictly before \(j\)**: it vanishes at each head slot by agreement on \(H\), and in both rows it vanishes in columns \(j,j+1,\ldots,11\) by explicitness. There are at most six nominal slots before \(j\), and all their clocks are distinct because the *only* repeated pair was \(i,j\) and the later member \(j\) is excluded. In particular **column \(i\)** belongs to the interpolation set: although row \(i\) cannot tap itself, row \(j\) potentially can; interpolation proves the difference at column \(i\) is zero as well. The paid powers through degree five therefore force the entire padded rows to agree. This reasoning works even if \(i=1\) or \(j=11\), or if a head slot shares one of their clocks.

Two literal identical rows in an explicit tableau can be merged at the earlier slot. Keep the earlier row, delete the later one, add each later consumer's coefficient at the deleted slot to its coefficient at the earlier slot, and add the deleted output weight to the earlier weight. No consumer before the deletion used it. No backwards tap is introduced. For every tree, the retained stage values are unchanged, by induction on the tree: each child evaluation sums the same predecessor values after this merge, and identical rows give identical original stage values. The total weighted tree read is unchanged. This would produce a ten-stage order-eight explicit method, excluded over the ordered field \(\mathbb Q\). Thus \(\boldsymbol{\lambda}_B=0\).

Because the last column of a strict matrix is zero, \(B_{11}=0\). If \(b_{11}=0\), the unused terminal stage could be deleted at no cost; hence \(b_{11}\ne0\). The pointwise identity for \(\boldsymbol{B}\) now gives \(c_{11}=1\).

For \(\boldsymbol{\lambda}_D\), its last coefficient is now zero. Hence it has at most six available nominal slots. Its bush powers through degree five again give zero sums on each clock fibre. If nonzero, its unique pair \(i<j\) cannot contain stage 11. Their stage profiles agree through size six, and their padded matrix rows agree on child profiles through size five, including powers through degree four and \(H\). As \(j\le10\), there are at most five nominal predecessor slots, at distinct clocks as before; interpolation again forces literal equality and a forbidden merge. Thus \(\boldsymbol{\lambda}_D=0\).

## 4. Chronology contradicts the two forced pointwise identities

The only later recipient of donor 10 is stage 11 at clock one, so \(D_{10}=B_{10}\). Since both discrepancies vanish,
\[
   0=B_{10}-D_{10}=\tfrac12 b_{10}(1-c_{10})^2 .
\]
If \(b_{10}=0\), then \(B_{10}=b_{11}A_{11,10}=0\), so \(A_{11,10}=0\) and the unused stage can be deleted, again impossible. Hence \(c_{10}=1\). There is at most one repeated pair, so \(c_9\ne1\). Both later receivers of donor 9 have clock one, so \(D_9=B_9\), forcing \(b_9=0\). But then the quadrature is carried by at most five sites including the nominal endpoint zero: two of the seven slots already coincide, and the distinct slot 9 has zero weight. Section 1 rules it out. This completes the obstruction.

## Implications for proposed helper designs

The earlier [four-tap obstruction](../erk-eight-factorial/FOUR-TAP-ELEVEN-OBSTRUCTION.md) imposed pointwise \(\boldsymbol{B}\), head silence, and a final clock at one. Here these are consequences of the full pure-head equality and order, and \(\boldsymbol{E},\boldsymbol{F}\) are not needed. A same-clock signed correction of one pair cannot bypass the result; it must satisfy *all* paid rooted identities, not just the clock moments.

For the Shanks-like sparse head (columns 2,3 cease below rows 3,5 respectively; exact primitives of degrees 2,3,4 from rows 3,4,6 respectively), the hypothesis is generic. The primitive residuals through \(\boldsymbol{r}_4\) and every obstruction obtained by grafting or merging through tree size five stay on the first four nontrivial coordinates, so \(V_5\subseteq H\). Write \(x=c_4,\ y=c_5\). For nonzero \(c_2,c_3,x,y\), the early \(\boldsymbol{r}_2\) and its first \(A\)-image pay \(\boldsymbol{e}_2,\boldsymbol{e}_3\) in \(V_5\). Here \(\boldsymbol{r}_j=A\boldsymbol{c}^{j-1}-\boldsymbol{c}^j/j\). The next two \(V_5\) vectors on coordinates \(4,5\) are \(A\boldsymbol{e}_3\) and \(\boldsymbol{r}_4\), with determinant
\[
          -\frac{3}{16}\,x y^2(x-y)^2.
\]
This follows by solving the three primitive equations for row 5 using \(0,c_3,x\), with \(c_3=2x/3\). At \(y=0\) or \(y=x\), those same equations make row 5 literally identical to row 1 or row 4. If \(c_2=0\), \(c_3=0\) or \(x=0\), the respective sparse row is already identical to row 1, by its strict support and degree-two conditions (or earlier degeneracy). Thus retuning just these sparse head clocks cannot add a live signed helper. A candidate of this style needs a different defect space, for example one not confined to the first four nontrivial head coordinates.
