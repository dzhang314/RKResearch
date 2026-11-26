# Strict zero-through successive marks without diagonal refunds

Source-only companion to Native's sealed SUCCESSIVE-MARKS-AND-SUPPORT paper; it is not part of that manifest or claimed compiled Lean. The independent audit remains in independent_native_successive_mark_rank_audit_20261126.md. No build, solver, numeric replay, repository operation, or held work. No absolute stage bound is asserted.

Work in a field with the needed primitive integers paid by the achieved order. Use the paper's ordinary setup: actual lower triangular rows, true nested \(E_j,F_j\), \(m=H-k\), \(H\le p\), genuine adjustment \(\mathbf a\in F_k\), and \(W=XP\), \(\deg P\le d\), \(d+1\le k\). Let \(S\) cover the support of \(F_H\) and suppose the actual adjustment matches \(W(c)\) on \(S\). Keep the genuine appearance of \(r\) successive marks, supplied for \(1\le r\le m-1\) by the paper's separation condition \(2(k+r-1)+1\le p\). The already verified \(X\)-factor weighted form also works if \(2(k+r-1)\le p\). No assumed endpoint clock or artificial lower tableau is involved.

## 1. Literal zero-through tests

Put \(B_0=1\), \(B_a=\prod_{j\le a}(X-u_j)\), and \(z_a=(B_{a-1}W)(c)-B_{a-1}(C)\mathbf a\). True separation and the simultaneous support match make the first nonzero physical row \(i_a\) exist outside \(S\), as in the source. Its numerical \(u_a\) is nonzero and distinct from the earlier marked clocks because the adjustment is zero there and \(B_{a-1}(u_a)W(u_a)\ne0\). Thus the next \(z_{a+1}=(C-u_a I)z_a\) is genuinely zero **through** \(i_a\), including that row. This is numerical and needs no diagonal refund.

For \(\deg R\le m-a-1\) the true input \(R(C)(C-u_a I)z_a\) has grade at most \(k+a-1+1+(m-a-1)=H-1\) and scalar profile \(R B_aW\). Lower triangularity makes its actual \(A\)-output zero through \(i_a\). The discrepancy belongs to \(F_H\), which the physical reader annihilates. Hence the exact observed primitives are
\[
 J_0(RB_aW)(u_a)=0,\qquad \deg R\le m-a-1 .
\]
The last moment count \(m-a\) is at least one because \(r\le m-1\). No \(D=CA-AC-A^2\) refund is used.

## 2. Backward root count saves all but one degree

Define \(S_a=J_0^{\,m-a}(B_aW)\) also for \(a=0\). These are nonzero and have degree at most \(d+m+1\le H\). For \(a\ge1\), the \(m-a\) moments at \(u_a\) make \(S_a\) divisible by \((X-u_a)^{m-a}\); its integrand already has the \(X-u_a\) factor, so the next derivative vanishes too. Thus this center has multiplicity at least \(m-a+1\). The origin has multiplicity at least \(m-a+1\) as well. All differentiations and Taylor coefficients are paid within \(H\). There is the exact relation
\[
 S_a=(X-u_a)S_{a-1}'-(m-a)S_{a-1}.
\]
Each later step can lose at most one at a previous distinct clock. Therefore \(S_{r-1}\) has origin and each of the \(r-1\) old centers to order at least \(m-r+2\); for \(r=1\) use the same origin fact for \(S_0\).

At the *next* center \(u_r\), expand \(S_{r-1}=\sum_j s_j(X-u_r)^j\). The local coefficient of \(S_r\) is \((j-(m-r))s_j\). Its known center multiplicity is at least \(m-r+1\). For \(0\le j<m-r\) the multiplier is a paid nonzero integer, so \(S_{r-1}\) has an additional zero of order at least \(m-r\) at this distinct next center. (The resonant coefficient \(j=m-r\) cannot be forced.) Now
\[
 d+m+1\ \ge\deg S_{r-1}\ \ge\ r(m-r+2)+(m-r),
 \qquad d\ge r(m+1-r)-1 .
\]
Hence a nonzero \(P\) is excluded if \(d<r(m+1-r)-1\). Relative to the refunded source, dropping **all** own diagonals loses one degree, not \(r\); the saving comes from counting the next center backwards on the penultimate primitive. This does not assert the missing boundary case, or waive the actual primitive reads/support. The same physical rank deductions apply with this adjusted scalar threshold.

## 3. Conditional non-circular gauge certification

Suppose instead \(S\) covers just \(Z=F_H\cap\ker L\), and \(\mathbf a\in F_k\subset Z\) with the same simultaneous match. The appearance and distinct chronology of the marks above still follow, before any primitive read: \(z_a\) is nonzero, zero on \(S\), and at its first off-\(S\) row the actual adjustment is zero. Every selected row annihilates \(Z\), not automatically all \(F_H\).

Set \(w=(C-u_r I)z_r\). It is literally zero through the last selected row. Therefore for \(0\le j\le m-r-2\),
\[
 D(C^j w),\qquad D=CA-AC-A^2,
\]
is a genuine \(F_H\) witness vanishing at every selected row by triangularity, with grade \(k+r+j+2\le H\). This witness argument does not require the last diagonal to vanish. When \(F_{H-1}\subset Z\), this particular trajectory has at most one possible nonzero top gauge image. If the actual endpoint gauge has dimension one and the top image is **actually** verified nonzero, these honest witnesses span \(L(F_H)\) and the source's pure image/kernel lemma pays all the needed primitive reads without a circular diagonal inference. In higher gauge dimension one needs genuinely independent measured witnesses or direct primitive reads. The displayed strict trajectory is empty when \(r=m-1\); then no gauge payment is claimed from it. No automatic nonzero gauge or existence of a specific chart satisfying these verified conditions is asserted.
