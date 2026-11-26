# One earlier sampler: literal double-factor sources

Adding one stage to the canonical early block shrinks the actual first-excess source space. This changes the minimum-width boundary conditions but does not construct a full target-order tableau.

## 1. Add one real earlier stage and keep both pure reads literal

Start with the true canonical early cache of cap \(m-1\), exact decoder \(D_F\), common \(\gamma<0\), and actual final clock \(\alpha<0\). The genuine first-excess space is \(K_m=G(\ker\mathbf e\cap{\cal F}_m)\) of dimension \(q=\lceil m/2\rceil\), all vanishing at \(\alpha\). Assume \(q\ge3\). Write \(J=I_0-\gamma I\).

Choose a real-algebraic \(a<0\), distinct from \(\alpha\), and insert one true earlier stage just after the canonical bank with strict taps \(E_a J D_F\), self diagonal \(\gamma\). Its real clock is \(a\) by the leaf, and it is actually locally exact through size \(m\) because each proper child in that cap is already paid by the old decoder. Denote its true numerical column by \(z_a(t)\). The new decoder is
\[
 D'(\mathbf e,z_a)=D_F\mathbf e+
                    q_a(X)\bigl(z_a-E_aD_F\mathbf e\bigr),
 \tag{1}
\]
where the true polynomial \(q_a\) is chosen in \(K_m\) to satisfy
\[
                  q_a(a)=1,\qquad (Jq_a)(\alpha)=(Jq_a)(a)=0 .
 \tag{2}
\]
Such choices exist generically among negative real \(a\), with an exact linear construction. Put \(K_m^0=\ker(E_\alpha J|_{K_m})\). This has dimension \(q-1\ge2\), since the shifted tall profile \(W_{m-1}\) has nonzero \(J\)-value at the Laguerre root \(\alpha\). For independent \(F,G\in K_m^0\), the polynomial \(F JG-G JF=F I_0G-G I_0F\) is not identically zero (otherwise the rational derivative of \(I_0F/I_0G\) vanishes). Off its finitely many roots, choose \(q_a\in\operatorname{span}\{F,G\}\) by the \(2\times2\) evaluation solve \(q_a(a)=1,Jq_a(a)=0\). The remaining condition then holds by membership in \(K_m^0\). This also certifies that the two functionals \(E_\alpha J,E_a J\) are independent on the old \(K_m\).

The new decoder is still exact through size \(m-1\), where its correction coefficient is genuinely zero. Its output degree is at most \(m-1\); this extra degree can first appear only at size \(m\). Consequently its pure polynomial \(V'_t\) still satisfies \(\deg V'_t\le |t|-1\): \(J D'\mathbf e'(u)\) has degree at most \(|u|\) on every child, either by true lower exactness or by that degree cap. The four literal identities on **all** numerical data are
\[
 E_\alpha D'=E_\alpha D_F=e_{\rm last},\qquad E_aD'=z_a,
 \qquad E_\alpha J D'=E_\alpha J D_F,\qquad E_a J D'=E_a J D_F.
 \tag{3}
\]
Here \(e_{\rm last}\) denotes the old actual last coordinate. The last equality retains the added true stage feed, and the third retains the old actual final strict row. Thus all actual new pure values \(V'_t\) coincide with the appropriate true early numerical coordinate at each of \(\alpha,a\), even above the decoder cap. Every genuine residual satisfies
\[
                   F'_t=V'_t-D'\mathbf e'(t)
                       \in (X-\alpha)(X-a)\mathbb P_{\le |t|-3}.
 \tag{4}
\]
Zero polynomials at small sizes are included. No equality of high actual stages with the unshifted exact solution was presumed.

Through size \(m\), \(V'_t=G_t\), and the new coordinate is \(E_aG_t\). Formula (1) therefore subtracts \(q_a E_a F_t\) from the old actual first-excess residual \(F_t\in K_m\). Because \(q_a\in K_m\) and \(q_a(a)=1\), the **actual** new first-excess residual space is exactly
\[
                 K'_m=K_m\cap\ker E_a,\qquad \dim K'_m=q-1.
 \tag{5}
\]
Every element of (5) is realized by true numerical-zero old and new early data through size \(m\), hence by its exact clock evaluations on the new direct late stages. Choosing an arbitrary Hermite polynomial for (2), without \(q_a\in K_m\), would not have proved this dimension reduction.

## 2. Actual source controls above first excess

All actual upper source bands obey (4), and the genuine marked early-null representatives from \(K'_m\) are still exact pointwise on their true late numerical values. For every \(n\ge m\), they yield the known subspace \(K'_m\mathbb P_{\le n-m}\) of the actual residual span. The full double-factor envelope in (4), and the exact space (5) at \(n=m\), therefore give a safe finite sufficient contact test for all rooted order by the unique-spine proof. The following stronger statements identify when that envelope is forced by actual rooted tests.

Write \(V=K_m/(X-\alpha)\subseteq\mathbb P_{\le m-2}\). The one-mark theorem gives \(V+XV=\mathbb P_{\le m-1}\). Set \(V_a=\ker(E_a|_V)\).

* If \(m\) is odd, \(\dim V=(m+1)/2\), and the map \((P,Q)\mapsto P+XQ\) on \(V^2\) has exactly a one-dimensional kernel. In a nonzero relation \(P=-XQ\), the polynomial \(Q\) is nonzero. Choose \(a\) also off its finite root set. Then that map is injective on \(V_a^2\), with dimension \(m-1\), exactly the dimension of \((X-a)\mathbb P_{\le m-2}\). Consequently actual one-mark heads attain the whole double ideal at size \(m+1\), and further marks attain it at every larger size. In this case the double-factor contact test and (5) are necessary as well as sufficient, by the same true-head graft argument used in the one-mark theorem.
* If \(m\) is even, the original two-copy map is injective, so the restricted one-mark space has dimension \(m-2\), exactly one below the envelope at size \(m+1\). Do **not** silently identify the actual marked heads there with the full envelope. A sharp two-mark test uses the relation space
\[
 {\cal R}_2=\ker[V\otimes\mathbb P_{\le2}\longrightarrow\mathbb P_{\le m}]
\]
under polynomial multiplication. With \(\rho_a\) the rank of its evaluation under \(E_a\otimes I\), the image of which is in \((X-a)\mathbb P_{\le1}\), one has
\[
           \dim(V_a\mathbb P_{\le2})=m-2+\rho_a .
\]
This follows by first taking the quotient by the codimension-three subspace \(V_a\otimes\mathbb P_{\le2}\), then taking the image of the relation space in that quotient. Thus two marks attain the whole envelope exactly if this measured rank is two. This is a concrete finite check, not an assumption that all rings of polynomials saturate after a generic evaluation. If it passes all bands from size \(m+2\) onward are forced. The unmarked-numerical sources at size \(m+1\) can be measured separately; the full envelope remains sufficient.

For odd \(m\) the repaired early bank also forces the genuine reverse model read through length \(r-1\) in the same way as before. In fact true early-null model profiles through \(m+1\) fill \(\mathbb P_{\le m}\). The marked space already attains the codimension-two double ideal. The unary extensions of old true numerical-null heads, even if their newly appended coordinate at \(a\) was nonzero, are zero on **all** early data in the shifted strict system: the new coordinate was last and has no strict outgoing edge to any earlier early coordinate. Their model profiles are \(JF\), \(F\in K_m\). Evaluations of these at \(\alpha,a\) have rank two by the choice in (2), supplying the two missing directions. Further marks maintain the full exact model space. When \(m\) is even, this argument still supplies two actual complementary outputs to the smaller marked space; do not infer full model span without the remaining rank test. For that branch one can require the genuine reverse model consistency explicitly as part of the candidate dictionary.

## 3. The minimum late bank acquires one top channel (balanced even target)

Assume \(p=2m,\ r=m,\ d=L(m)\), and consider a literal lower dictionary already paid through \(m-1\) on the stated safe double-factor envelope, with its consistent numerical/model map onto \(\mathbb P_{\le m-1}\) and the actual span \(V\) of full rank \(d\). These requirements must be certified, including in the even-\(m\) early branch. Let \(N\) be its model-zero kernel. It has dimension \(d-m\). By the paid contacts,
\[
       {\cal U}'=E((X-\alpha)(X-a)\mathbb P_{\le m-2})
                  \subset N^\perp,\qquad \dim{\cal U}'=m-1
\]
when enough true distinct late sites differ from the two anchors. Thus \(N^\perp\) has exactly one dimension beyond the true double-factor ideal, unlike the original canonical design.

The exact final contact for any such bank is
\[
  T EF\in N^\perp,\quad
  b\,P(C) T EF=\ell(PJF)\quad (F\in K'_m,\ \deg P\le m-1).
 \tag{6}
\]
These follow from actual last-primitive words and suffice for those words, with prior marked words covering the remaining cases. They determine the top column uniquely once the measured \(N^\perp\) is known, because \(V=N\oplus B\) is the full space. The extra channel is not freely available unless the *actual* lower bank attains the proposed subspace.

A useful target geometry is explicit. Keep the original single-factor projection \(R_F^0=JF-(JF)(\alpha){\cal L}_m/{\cal L}_m(\alpha)\). Pick \(Q_0\in(X-\alpha)\mathbb P_{\le m-1}\) with \(Q_0(a)=1\), and a vector \(\eta\) in the annihilator of the actual pure mark rows \(B\). If the lower dictionary realizes
\[
              N^\perp={\cal U}'+\operatorname{span}\{EQ_0+\eta\},
\]
then the unique top solution of (6) is
\[
                      T EF=ER_F^0+\eta\,R_F^0(a).
 \tag{7}
\]
Indeed \(R_F^0-R_F^0(a)Q_0\) belongs to the double factor ideal, and the pure mark moments of the correction vanish. The pure mark pairing is invertible on this desired space: after forgetting its pure-mark-null \(\eta\), it is the usual single-factor positive Hilbert pairing. Thus the one-extra-mode target is a literal rank condition on real numerical data.

This shape can pay the first physical strict row without the previously excluded canonical anchor law. For instance take its true clock to be \(a\) and choose \(\eta_1=-1\) by Vandermonde on the other nonzero-weight sites, so the first row of (7) vanishes on every true source. This is an **actual same-clock alias**, not a new independent stage at that location: its pure feed equals the inserted earlier sampler's feed by (3), and the two literal rows can be merged with transferred weight. If an independent first clock \(x_1\ne a\) is desired, its necessary/sufficient projected first-row condition is \(R^0_{\cdot}(x_1)\in\operatorname{span}\{R^0_{\cdot}(a)\}\) on \(K'_m\), with the corresponding \(\eta_1\). Subsequent real strict rows still have the earlier-evaluation compatibility and the simultaneous two-sided retap condition of [the late repair proof](LATE.md). This is a feasible prefix and a precise physical specification, not a presumed full-order continuation.

For a balanced **odd target** \(p=2r+1,\ m=r+1\), the same repair removes the old source-dimension mismatch: the double-factor ideal at \(m+1\) has dimension \(m-1=r\), equal to the reverse model dimension. If the lower exact dictionary with that envelope and \(d=L(r)\) is realized, \(N^\perp={\cal U}'\) at the final cap. Then the required pointwise projection of \(JF\) is its unique representative in \((X-\alpha)(X-a)\mathbb P_{\le m-2}\) matching ordinary moments against \(\mathbb P_{\le m-2}\). The Gram matrix with weight \((X-\alpha)(X-a)>0\) on \([0,1]\) is invertible, so this is exact; equivalently subtract a combination of the two highest shifted Legendre modes to impose the two true zeros. It still needs strict physical chronology, not just these scalar equations.

One added earlier stage and \(d=L(m)\) late rows would cost a single stage above the original balanced even floor, with \(q-1=2,3,4\) genuine first-excess directions at \(m=6,8,10\). The construction of the physical sampler and decoder is unconditional. The complete low dictionary and final chronological retaps in the repaired geometry have not been proved; no table endpoint is claimed.
