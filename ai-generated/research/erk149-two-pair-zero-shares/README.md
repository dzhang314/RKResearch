# Zero individual shares do not rescue the fourteen-stage two-pair ERK cut

This extends the [generic two-pair obstruction](../erk149-six-opening-two-pair-order10/README.md) and its [point-collision completion](../erk149-point-collision-exhaustive/README.md) to zero individual high weights. The fixed architecture is unchanged: six canonical opening rows, cubic \(\Pi\) at their four physical donor labels \(0,p,q,r\), scoring in the opening only at the origin, the literal high cross block \((EJ-BE)\Pi\), and eight strict new physical rows at the six distinct nonzero scalar sites \(1\), two interior pairs and three other interior singletons. Each interior is distinct from 0 and 1; the field has characteristic zero. The original weight at each individual high row can be zero or arbitrary signed, but **the aggregate at each high site must be nonzero**. In a pair, both individual weights may be nonzero, or one may vanish. This does not exclude a zero aggregate, a different cut or arbitrary fourteen-stage order ten. The stage interval remains **14–15**.

## Raw physical transpose; no weight inverse at a ghost

Put \(\mathbf w\) for the high weights in actual reversed order, \(Y=\operatorname{diag}(1-x_i)\), and \(T=B^{\mathsf T}\) after the same reversal of both indices. The literal rooted equality \(\mathbf b A=\mathbf b(I-C)\) is used as a necessary mathematical premise from the [fourteen-stage equality ledger](../ERK10-FOURTEEN-STAGE-EQUALITY.md). Its high restriction in the raw physical transpose is
\[
                         T\mathbf w=Y\mathbf w .
\]
Define actual reverse covectors, displayed as columns,
\[
 \mathbf U=T(Y\mathbf w)-Y^2\mathbf w/2,\qquad
 \mathbf G=T(Y^2\mathbf w)-Y^3\mathbf w/3,\qquad
 \mathbf H=T\mathbf U,\qquad
 \mathbf K=T(Y^3\mathbf w)-Y^4\mathbf w/4 .
\]
Pulling an actual tree word back now starts from \(\mathbf w\), moves a primitive through \(T\), and multiplies clock marks by \(I-Y\); the analogous scalar column at a clock has a factor \(w_i\). These are exactly the same word expansions as before, but evaluated by summing covector entries at equal clocks rather than dividing by physical weights. For example \(T(I-Y)\mathbf w=(Y-Y^2/2)\mathbf w-\mathbf U\), and \(T^3\mathbf w=Y^3\mathbf w/6+\mathbf G/2+\mathbf H\). All the previous grouped equations therefore hold with these raw covectors. The glued anchored prefix argument is unaffected: its fresh forward contrast drives still vanish at the old point \(r\).

For a site \(\mathfrak g\) with nonzero aggregate \(W_{\mathfrak g}\), define its normalized physical row
\[
             P_{\mathfrak g}
                    =\frac{1}{W_{\mathfrak g}}\sum_{i\in\mathfrak g} T_{i,*} .
\]
For any donor its normalized scalar tap is \((P_{\mathfrak g})_j w_j\); a zero-weight donor can nonetheless be used on \(\mathbf U,\mathbf G,\mathbf H\). When a pair completes, this sum uses its two actual strict rows. Each singleton has just one row. An opposite physical covector on a pair is an ordinary column supported on the two components with opposite values; this does not use any live-weight scaling.

The high endpoint (first reversed row) has clock \(x=1\) and weight nonzero, as follows from the general floor of fourteen. The very next reversed row cannot have zero weight: \(T\mathbf w=Y\mathbf w\) then forces its only actual tap to the endpoint zero, so in forward orientation its entire column is zero. Its own output weight is zero, hence literal row and column deletion preserves every tree and contradicts the floor. The same pruning applies whenever a subsequently considered zero-weight row has no nonzero actual tap.

## Generic or off-mesh point sources

As in the generic proof, \(\mathbf U,\mathbf G,\mathbf H\) have zero aggregate at every interior; the aggregate rows of \(\mathbf K,T\mathbf v\), for each opposed pair direction \(\mathbf v\), have rank at most one on the five interiors. To see the proof of the latter literally in raw form, \(\mathbf U\) and \(Y\mathbf U\) separate the two pairs if both first components are nonzero; if the second first component vanishes and its weight is nonzero, the component there of \(\mathbf G/2+\mathbf H\) is exactly \(-w_b b^3/6\ne0\). These covectors still span the two opposite directions. The first interior has \(U_a=-w_a a^2/2\ne0\), so is the first occurrence of a pair. The next row cannot complete that pair, since its only nonzero earlier scalar site is at the same clock and \(y,y^2\) moments disagree. It cannot be a singleton, since it would have to tap the first row nontrivially to pay the \(y\) moment and would then fail \(P\mathbf U=0\). Thus it is the first occurrence of the other pair.

If both first occurrences are live, the two chronology minors of the generic proof are unchanged, even if either later share is zero. In its first-completed-pair route, the opposed test on the *other* pair begins with the live donor \(b\); choose its first value \(w_b\) so the response is precisely its normalized scalar tap. Neither compared row has read its second occurrence. Any use of the first paired completion affects only the existing scalar site \(a\). In its first-singleton route, both early pair donors and the new singleton are live, and \(\mathbf U\) is zero at the new singleton. The two defects at the prior live donors, divided by their nonzero weights, give exactly the earlier proportional-restriction proof. The determinants are the same.

It remains that the other pair's first occurrence \(B\), at \(y=b\), is a zero-weight ghost. Its actual tap to the first live interior \(A\) must be nonzero: if it vanished, \(T\mathbf w=Y\mathbf w\) would also kill its endpoint tap and make it prunable. Thus \(U_B=T_{B,A} w_A a\ne0\). The rank-one cap quoted above still follows from \(\mathbf U,Y\mathbf U\).

Let \(t\) be the first complete interior group's target \(y\). Its only weighted earlier interior donor is \(A\), regardless of whether this group is the completion of the ghost's pair or a singleton. Exact \(y,y^2\) yield \(t=3a/2\). In particular it cannot be the other occurrence of \(A\). The normalized cubic residual and the first opposed-direction response are
\[
   K(t)=t^2a^2/2-t^4/4,\qquad P_t\mathbf v_A=t^2/(2a),
\]
where \(\mathbf v_A\) has values \(w_A,-w_A\) on the two physical \(A\) rows. Their ratio is \(-a^3/8\). The next complete target \(s\ne t\) sees only \(0,a,t\) among weighted scalar donors, and has seen only the first \(A\) in the support of \(\mathbf v_A\). Consequently
\[
 P_s\mathbf v_A=\frac{s^2(3t-2s)}{6a(t-a)},\qquad
 K(s)=(a+t)s^3/3-at s^2/2-s^4/4 .
\]
Both are determined by its actual lower moments, no matter how it uses any ghost. The rank-one cap forces the sum \(K(s)+(a^3/8)P_s\mathbf v_A\) to vanish. It is instead \(-s^2(2s-3a)^2/16\ne0\) because \(s\ne0,t\).

## Point collision: a singleton anchor

In the point-collided case the nonanchor groups have exact normalized \(y,y^2,y^3\) moments and the four reads \(\mathbf U,Y\mathbf U,\mathbf G,\mathbf H\) paid, as in the anchored chronology census. Before the first completed nonanchor group, only the first occurrences of the two pairs and the anchor singleton could have occurred.

If the two first occurrences are live, the singleton-anchor proof is unchanged. In the first completed pair the new raw defect column is the negative of the first, regardless of its share. The two other scalar cardinal taps still see those two live donor rows, while the two physical occurrences of the completed pair only affect the effective defect coefficient at their common clock. Its second-target determinant is unaffected.

If a first occurrence is a ghost, fewer than three previous physical rows cannot suffice: if one is a ghost there is at most one weighted interior, and if neither is a ghost the previous two-site separated-defect argument applies. Two first ghosts would still leave just one weighted donor after all three rows, impossible. Therefore write the three earlier physical donor clocks in chronological order as \(c,a,b\), with the first live and exactly one of the last two a ghost. For convenience apply an invertible diagonal coordinate change: use \(d_j=w_j\) at nonzero weights and \(d_j=1\) at ghosts, conjugate \(T\) by \(\operatorname{diag}(d)\), and scale all covectors by the inverse diagonal. The scalar starting column now has values 1 at live rows and 0 at ghosts. The normalized pooled row is transformed on the physical input by this same diagonal, so all equations are unchanged. Let \(\epsilon_a,\epsilon_b\) be its live flags at \(a,b\), and write \(k\) for the transformed tap \(a\leftarrow c\), and \(\ell_0,m\) for \(b\leftarrow c,a\).

Let \(p_c,p_a,p_b\) be the first normalized complete row's actual taps in these coordinates at target \(t\), and set \(X_0=p_a k+p_b\ell_0,\ Y_0=p_b m\). Direct substitution of the chronological raw defects gives
\[
\begin{aligned}
 cX_0+\epsilon_a aY_0 &=t^3/6,&
 c^2X_0+\epsilon_a a^2Y_0 &=t^4/12,\\
 Y_0kc &=t^4/24,&
 (a-b)p_a kc &=t^3(3t-4b)/24.
\end{aligned} \tag{1}
\]
Thus the ghost can appear with nonzero physical tap even if its scalar cardinal tap is zero.

* **Last donor \(b\) is a ghost.** The scalar weights are \(p_c,p_a,0\) and satisfy the same three cardinal equations on \(c,a,b\): in particular \(p_a=\mu_a(t)\) and \(p_c=\mu_c(t)\) from the earlier census. Since \(\epsilon_a=1\), (1) gives exactly the three-donor resonance \(t=b\). Equation (1) forces \(Y_0,k,p_b\ne0\), so the unique physical null direction of the first three defect columns has a nonzero \(b\) coefficient, even though its scalar tap there is zero. The independence of the columns at \(c,a\) follows from \(u_c u_a(a-c)\ne0\) if \(u_a\ne0\), and from \(h_a=-kc^2/2\ne0\) otherwise. The ghost's live mate completes its pair at \(b\); the new covector column is again a known nonzero multiple of its first. At the next complete target \(z\ne b\), the normalized scalar taps at \(c,a\) are still cardinal taps while the effective defect coefficient at \(b\) is allowed to vary. The determinant \(\mu_c(z)\mu_a(b)-\mu_a(z)\mu_c(b)\) remains the same strictly nonzero expression in the census.
* **Middle donor \(a\) is a ghost.** Now \(\epsilon_a=0\). Eliminating \(X_0\) between the first two equations (1) forces \(t=2c\), since \(t\ne0\). Weighted scalar donors are \(c,b\), whose cubic compatibility is \(6bc-4(b+c)t+3t^2=0\); therefore \(b=2c=t\). If the third physical row were already the singleton anchor, this first nonanchor completion could not be at its clock. Thus \(b\) is the other pair's live first occurrence and its mate completes at \(t=b\), whether that mate is live or not. The next complete target \(s\ne b\) still has only earlier weighted clocks \(0,c,b\). If it is the live mate of the initial ghost it is not its own donor, so that conclusion still holds. The scalar cubic residual is \(-s^2(s-b)^2/4\ne0\), a contradiction.

## Point collision: a paired anchor

Let the anchor pair be \(A,A'\), and the other pair \(B,B'\). If the first \(B\) is a ghost, the first nonanchor completion has available weighted interior donors only at the anchor's single site. That cannot pay its three scalar moments. If the first \(A\) is a ghost, the first nonendpoint row must be \(B\), with a nonzero weight. The live anchor mate must occur before the first nonanchor completion; without it only \(B\) is weighted. When it has occurred, the available scalar supports are still just \(a,b\), with a single physical donor at \(b\). The separated \(\mathbf U,Y\mathbf U\) tests force the contribution from \(B\) zero, while \(U_B=-w_B b^2/2\ne0\) and the moment equations force its scalar tap nonzero.

Finally both first occurrences may be live with a later zero share. The earlier paired-anchor census now applies without division by the second anchor's weight. Indeed, in chronology \(A,A',B\) the individual identity is \(G_i=aU_i+w_i a^3/6\) on either anchor occurrence. In \(A,B,A'\), write the raw honest products as \(X_0=(P_t)_{A'} T_{A',A} w_A\) and \(Y_0=(P_t)_{A'} T_{A',B} w_B\); the same pooled equations follow with \(\nu,\lambda\) the respective scalar tap totals. They require only the nonzero first occurrence weights and pay the same resonances with the same contradiction. No classification uses an unavailable individual-weight inverse.

## Reproduction

The exact replay covers the raw word identities, the middle/last ghost covectors and their chronological elimination, and the new early/middle-ghost scalar squares. Four further scalar identities have standalone characteristic-zero Lean proofs and a typed standard-axiom audit in Lean/Mathlib 4.36.0. This is not a native end-to-end classification; the equality/contrast lift, chronology and aggregation arguments are mathematical.

From ai-generated:

    python3 -B research/erk149-two-pair-zero-shares/replay.py
    sha256sum -c research/erk149-two-pair-zero-shares/sources.sha256

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.ERK149TwoPairRawTranspose
    lake env lean AuditERK149TwoPairRawTranspose.lean
