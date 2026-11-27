# A dormant triple does not rescue the literal cubic-decoder ERK cut

Replace the two repeated pairs by **one triply repeated interior clock**, keeping six canonical opening rows and eight actual high rows. The high scalar support is \(1\), the triple \(A_1,A_2,A_3\) at one nonzero interior, and four distinct singleton interiors. All are distinct from 0 and 1. The old origin is the only weighted opening row, \(0,p,q,r\) are distinct, and the cross block remains literally \((EJ-BE)\Pi\), with the same interpolatory cubic \(\Pi\). This note rules out this changed high shape for order ten over any characteristic-zero field, for arbitrary physical shares and chronologies. It does **not** rule out releasing the cubic cross block. The unrestricted ERK10 interval is **14–15**.

The proof uses the [raw-transpose equations](../erk149-two-pair-zero-shares/README.md) and [anchored contrast](../erk149-two-pair-point-collision/README.md) independently of the previous two-pair chronology. Use their actual raw weighted covectors \(\mathbf w,\mathbf U,\mathbf G,\mathbf H,\mathbf K\) and write \(\mathbf V=\mathbf G/2+\mathbf H\), \(y=1-x\). Exact scalar quadrature and endpoint pruning work exactly as in the [dormant aggregate note](../erk149-two-pair-dormant-aggregate/README.md): there can be at most one dormant scalar site, and it cannot be the endpoint. A contribution at a clock means its aggregate weight, not an individual share. A complete contributing row is the actual normalized pooled row if it is the triple, and the normalized singleton row otherwise. Its nonzero aggregate is the only group divisor.

## Noncollided source, including a genuinely dormant triple

If \(\ell\ne E_r\), the direct size-five/six sources span \(X\mathcal P_4\), separating all five high interiors. All four lower covectors \(\mathbf U,\mathbf G,\mathbf H,\mathbf K\) are paid as group sums. If \(\ell=E_r\) but \(r\) is outside the high interiors, the lower \(\mathbf U,\mathbf G,\mathbf H\) are paid at every interior, and the two grouped columns \(\mathbf K,T\mathbf V\) have rank at most one. The latter follows directly from the old four-letter tests: the cubic clock word pays \(\mathbf K\) and the four-primitive word pays \(\mathbf K/6+T\mathbf V\) on the same four-dimensional direct source space. No assumption about the dimension of an opposed-pair space is needed here.

In either case, the first contributing completion cannot be the triple itself: only its own clock \(a\) would be available to pay its exact \(y,y^2\), whereas a single weighted donor clock \(a\) requires its target to be \(t=3a/2\). Any dormant singleton can be omitted from these reads, since both its weight and its paid \(\mathbf U,\mathbf G,\mathbf H\) are zero there. If the triple is itself dormant, do not count its completion and do not divide by its aggregate.

Thus the first contributing completion is a singleton \(t\). Its only earlier weighted nonzero site is \(a\) and \(t=3a/2\); it needs at least two actual earlier triple donors. Indeed the first nonendpoint physical row must be live (otherwise it prunes) and cannot be a paid singleton. The earliest triple value of \(U\) is \(-w_1a^2/2\ne0\), so an exact nonzero scalar tap using only that row cannot kill \(\mathbf U\). In the nonpoint branch the normalized cubic residual at this first singleton is already
\[
                    t^2 a^2/2-t^4/4=-t^2a^2/16\ne0 ,
\]
contradicting its paid \(\mathbf K\).

For the off-mesh point branch, the first two triple rows have
\[
\begin{aligned}
 U_1&=-w_1a^2/2,&
 U_2&=\kappa a w_1-w_2a^2/2,\\
 V_1&=-w_1a^3/6,&
 V_2&=-w_2a^3/6,
\end{aligned}
\]
where \(\kappa=T_{A_2,A_1}\) is the actual tap. The \(V_2\) formula holds because \(G_2/2\)'s tap on the first scalar donor cancels \(H_2=\kappa U_1\). These first two rows already precede the first contributing singleton. If the triple's aggregate is nonzero, before either of the first two contributing completions only these two triple rows can be donors: the third would itself be a contributing completion, and cannot be its own donor. If the triple is dormant, \(w_1+w_2+w_3=0\) and the grouped \(V_1+V_2+V_3=0\) shows \(V_i=-w_i a^3/6\) on the **entire** dormant triple. Thus at both compared completions the \(T\mathbf V\) response, up to nonzero common factor, is the actual scalar tap \(\mu_a\) at \(a\).

This takes seriously the two possible dormant defect directions. If the three dormant donors already precede the first contributing singleton, grouped \(\mathbf U\) forces the sum of the second and third raw weighted internal taps to be zero. Thus if \(\kappa=0\), all the available \(U_i\) are proportional to \(w_i\) and cannot pay \(P_t\mathbf U=0\) together with the nonzero \(a\)-tap. The same incompatibility with \(\kappa=0\) applies when only two donors have arrived. Accordingly \(\kappa\ne0\), and the first two entries of \(\mathbf U,\mathbf V\) have determinant \(\kappa a^4w_1^2/6\ne0\). Although the two defects really are independent, their paid \(\mathbf V\) direction is exactly the dormant scalar tap.

At the first completion the ratio \(K(t)/\mu_a(t)=-a^3/8\). The second contributing completion \(s\ne t\) has prior weighted nonzero scalar support only \(a,t\), even when more of the triple has arrived. The rank-one cap forces \(K(s)+(a^3/8)\mu_a(s)=0\). Evaluating the exact first two moments as in the raw ghost argument gives
\[
                    K(s)+(a^3/8)\mu_a(s)
                           =-s^2(2s-3a)^2/16\ne0 .
\]
This excludes both active and dormant triples in the off-mesh point branch.

## Point collision at a high interior

All nonanchor groups satisfy the seven anchored tests: exact \(y,y^2,y^3\) moments and zero reads on \(\mathbf U,Y\mathbf U,\mathbf G,\mathbf H\). In particular a first completed contributing nonanchor group needing those scalar moments cannot have only one weighted earlier interior. If the triple is the anchor, before that completion it is the only possible weighted earlier interior, contradiction. If the anchor is a dormant singleton, which can supply no weighted donor, the same one-site contradiction applies. Any other dormant singleton can be suppressed from the scalar/defect reads as above.

It remains that the anchor is a contributing singleton \(R\) at reverse clock \(c\). Let \(t\) be the first completed contributing nonanchor target. The only earlier weighted nonzero sites can be \(a,c\), so both are required and their scalar taps \(\nu,\lambda\) are nonzero. The separated tests \(P_t\mathbf U=P_t(Y\mathbf U)=0\) force \(U_R=0\) and the total \(U\) read at \(a\) zero. Consequently \(R\) could not have occurred first after the endpoint, and \(A_1\) is live with nonzero \(U_1=-w_1a^2/2\). At least two actual triple donors must precede the target \(t\). Because \(U_R=0\) and its earlier nonzero clocks are only \(a\), the normalized \(G_R/w_R\) is \(c^2(3a-2c)/6\).

If exactly two triple donors precede \(t\), there are just two possible literal patterns. In the first, \(A_1,A_2,R\), the two earlier triple rows individually satisfy \(G_i=aU_i+w_i a^3/6\). The \(G\) payment at \(t\) gives
\[
      \nu a^3+3a\lambda c^2-2\lambda c^3
                 =3a(\nu a^2+\lambda c^2)-2(\nu a^3+\lambda c^3)=0 .
\]
The exact moments imply \(t=2a\). Their two-site cubic compatibility then forces \(c=2a=t\), impossible because \(R\) is already complete. In the other pattern, \(A_1,R,A_2\), the row \(R\) has normalized \(H_R/w_R=-ac^2/4\), because its actual prior weighted tap at \(A_1\) is \(w_R c^2/(2a)\). The only honest late tap products are \(X\) for the \(A_2\) input from \(A_1\) and \(Z\) for its input from \(R\), each including its actual tap in \(P_t\) and the donor weight. The projected equations are
\[
\begin{aligned}
 -\nu a^2/2+aX+cZ&=0,\\
 -a^2 X/2-\lambda ac^2/4&=0,\\
 -\nu a^3/3+a^2X+c^2Z+\lambda c^2(3a-2c)/6&=0 .
\end{aligned} \tag{1}
\]
Eliminating \(X\) with the second equation and applying the exact scalar moments gives \(cZ=t^3/6,\ c^2 Z=t^4/12\). Hence \(t=2c\). The scalar cubic compatibility \(6ac-4(a+c)t+3t^2=0\) forces \(a=2c=t\). The only possible contributing completion at \(t=a\) is the active triple's actual third row. If it occurs there, the next nonanchor contributing singleton \(s\ne a\) still sees only \(a,c\) as weighted scalar donors; its cubic residual is \(-s^2(s-a)^2/4\ne0\). If the triple is dormant, it could not itself be the contributing completion, so there is already a contradiction.

If **all three** triple rows precede \(t\), the triple must be dormant, since otherwise its earlier completion would have been the first contributing nonanchor group. Since \(R\) cannot come first, three cases remain. For \(A_1,A_2,A_3,R\), each triple row reads only its one scalar site. The same \(G\)-payment above forces \(t=c\). In the order \(A_1,A_2,R,A_3\) permit the actual \(A_3\) tap to \(R\). On any triple row the identity
\[
    G_i-aU_i=w_i a^3/6+T_{i,R}w_R c(c-a)
\]
holds, since \(a,c\) are the only earlier nonzero scalar nodes. Summing over the triple uses the paid \(\mathbf G,\mathbf U\) and zero aggregate. Because \(c(c-a)w_R\ne0\), the single possible tap to \(R\) must vanish. Again the same \(G\)-payment gives \(t=c\).

Finally suppose \(A_1,R,A_2,A_3\). The same aggregate identity forces the two raw weighted triple taps to the anchor equal and opposite. The sum of the weighted internal triple taps also vanishes by grouped \(\mathbf U=0\). With \(\mathbf d=(0,1,-1)\) on the chronological triple, write their weighted internal tap column as \(k_0\mathbf d\) and their tap column to \(R\) as \(z_0\mathbf d\). **No normalized profiles at the triple are identified or assumed equal.** On its three physical coordinates:
\[
\begin{aligned}
 \mathbf U&=-a^2\mathbf w/2+(a k_0+c z_0)\mathbf d,\\
 \mathbf G&=-a^3\mathbf w/3+(a^2 k_0+c^2 z_0)\mathbf d,\\
 \mathbf H&=-a^2 k_0\mathbf d/2 .
\end{aligned}
\]
The last identity uses the actual first \(H=0\), second \(H=-a^2 k_0/2\) since \(U_R=0\), and the required total \(H=0\) at the triple. The normalized \(H_R/w_R=-ac^2/4\) again comes from the actual \(A_1\) as sole earlier nonzero weighted site. Put \(X=k_0 P_t\mathbf d,\ Z=z_0 P_t\mathbf d\). These real physical products again satisfy (1), not an inferred independent freedom. Thus \(t=a=2c\), but \(t\) was a contributing nonanchor singleton and \(a\) is the dormant triple clock. This completes the point-collided case with the true third physical donor retained.

## Native and independent receipts

Lean/Mathlib 4.36.0 checks the early independent-direction determinant and both resonance eliminations in which the exact second and third moments determine \(t=2a\) or \(t=2c\) before any cardinal inversion. The scalar comparison of the first two completions uses the earlier raw-transpose square lemma. The chronology, actual-rooted-to-word lift and high role of the old decoder remain mathematical, not a completely formalized exclusion theorem. The exact SymPy replay verifies the new products, aggregation, and resonances.

From ai-generated:

    python3 -B research/erk149-one-triple/replay.py
    sha256sum -c research/erk149-one-triple/sources.sha256

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.ERK149TripleDormant
    lake env lean AuditERK149TripleDormant.lean
