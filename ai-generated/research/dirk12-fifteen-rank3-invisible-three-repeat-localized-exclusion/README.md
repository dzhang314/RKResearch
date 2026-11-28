# DIRK12/15: a localized reverse cubic also cannot use a three-repeat live grid

Work in the [four-distinct-invisible-ghost fixed seven-site chart](../dirk12-fifteen-rank3-invisible-four-ghost-fixed-grid/README.md), with exactly three repeated live labels of multiplicities \(3,2,2\). This note excludes a **true weighted reverse cubic supported at one repeated label**. The two-support case has invariant grade four and is impossible by the actual unit next gain; the [three-support case](../dirk12-fifteen-rank3-invisible-three-repeat-exclusion/README.md) is also excluded. Thus the entire invisible fixed-seven chart with exactly three repeated labels is closed, under the stated four-ghost hypotheses. Four repeated pairs and the overall real **15–16** interval remain open.

Use physical reverse chronology and \(N=A^{\mathsf T}\) in that ordering. Write \(\mathbf y=1-\mathbf c\), \(Y=\operatorname{diag}(\mathbf y)\), \(\mathbf W(R)=\mathbf b\odot R(\mathbf y)\), and \(JR(X)=\int_0^X R\). Denote the true weighted cubic by \(\mathbf G\). It is supported at one live repeated label \(d\). The first three live nonzero distinct labels are \(d,v,u\): by the [one-label calculations](../dirk12-fifteen-rank3-one-active-third-debut/README.md) the genuine head
\[
           \mathbf H=N\mathbf G-\frac d2\mathbf G
\]
is nonzero at the first rows of \(v,u\), since the \(u,v\) clocks are fixed Lobatto nodes. Every grade-five weighted reverse defect is zero at singleton live and ghost rows. Thus both \(v,u\) are repeated, so all three repeats start before the first nonzero singleton \(a\). Let \(b,c\) be the next two singleton labels in physical reverse order. The clocks \(a,b\) are interior: if the reflected clock \(1\) is singleton, its row is the literal last physical row, the ordinary origin.

The genuine weighted quartic error and pure spaces are
\[
 \mathbf E_4=(3d/2)\mathbf G+\lambda\mathbf H,\qquad
 \lambda=3(v-d)(v-2d)/d^2,\qquad
 \mathcal B_4=\langle\mathbf G,\mathbf H\rangle,\quad
 \mathcal B_5=\langle\mathbf G,\mathbf H,Y\mathbf H\rangle.
\]
Each of these pure covectors sums to zero separately at each repeated label. Let \(i_{d,1}\) be the first actual live row at \(d\); its normalized amplitudes are \(G_{i_{d,1}}/b_{i_{d,1}}=d^3/6=:g_1\ne0\) and \(H_{i_{d,1}}=0\).

## Stronger early cut: no repeated group is spent before \(a\)

A group is spent once all its actual live rows have occurred. Suppose at least one repeat group is spent strictly before \(a\). A reverse input \(R_4=X(X-d)(X-v)(X-u)\) has degree four, and its actual weighted state \(\mathbf W(R_4)\) is supported on or after the cut immediately before \(a\). For the opposing ordinary forward test, take any scalar degree-six polynomial \(S\) vanishing at \(a,b,c\) and at every unspent repeated label. There are at most two such repeated labels, and hence its monic hull \(G\) has degree at most five. All of \(G P_{6-\deg G}\) is available as an actual grade-six early-supported state: the four numerical ghosts can be masked by a true \(\mathbf hP_3\) correction, using cubic interpolation at their four distinct clocks. There is **no** extra compatibility equation at degree six.

Lower triangularity and the genuine \(\mathcal B_5\perp T_6\) budget give \(I(S JR_4)=0\), now at \(6+5=11\) with the higher grade on the forward test. Among the fixed hull multiples at least one such integral is nonzero for every one of the 140 allowed grid choices, as checked below. Thus by \(a\) the outer repeated sites have not been spent, and neither has \(d\).

## Exactly two \(d\)-rows occur before \(a\), with different normalized cubic amplitudes

Suppose all observed live \(d\)-rows before \(a\) have the same normalized cubic amplitude \(g_1\). Interpolate the scalar quartic \(S\) at \(0,a,d,v,u\) with value \(g_1\) at \(d\), and zero at the other four. The actual grade-four weighted input \(\mathbf W(S)-\mathbf G\) vanishes through \(a\), whether or not \(H\) has already changed inside its support. Its primitive error lies in \(\mathcal B_5\), zero at \(a\). Thus \(JS(a)=0\). But \(S\) is a nonzero multiple of the corresponding Lagrange cardinal, and its exact degree-four tap at \(a\) is nonzero on the fixed grid. Contradiction.

So at least two live \(d\)-rows with differing normalized cubic amplitudes are already present. Since the group is not spent, it is necessarily the triple, with exactly two prior rows. The other two groups \(v,u\) each have exactly one live row before \(a\), and hence have nonzero observed normalized head amplitudes \(h_v,h_u\), respectively. Write \(g_2\ne g_1\) and \(h_2\) for the second actual \(d\)-row's normalized \(\mathbf G,\mathbf H\) values.

The clean singleton restriction of \(\mathcal B_6\) has rank at most one, for the [same paid forward mask and terminal-coordinate reason](../dirk12-fifteen-rank3-invisible-three-repeat-chronology/README.md): five independent forward degree-five scalar profiles are available on live rows after the single four-ghost quadratic-interpolation condition. Their live evaluation annihilator has rank two, and the literal terminal-zero condition cuts it by one since a degree-five polynomial cannot represent its lone terminal card on seven distinct nodes. This applies to every reverse cubic support shape. The restriction is nonzero at \(a\), by applying the true degree-five primitive to
\[
                         P_a=X(X-a)(X-d)(X-v)(X-u).
\]
Its actual weighted input vanishes through \(a\), whereas its scalar primitive does not vanish there (fixed interior anchored check). Write \(\mathbf E_5=N\mathbf W(X^5)-\mathbf W(X^6)/6\) for the actual scalar degree-five-input error; its singleton \(a\)-value is \(-b_a JP_a(a)\ne0\).

## If \(\mathbf H\) is zero on the triple, the localized lines separate

The pure space \(\mathcal B_5\) then has independent localized lines \(\mathbf G_d,\mathbf H_v,\mathbf H_u\), since \(\mathbf H,Y\mathbf H\) separate the two outside clocks. If no repeated group is spent before \(b\), use the actual grade-four pure correction \(\mathbf H\) and quartic \(S\) with roots \(0,a,d\) and values \(h_v,h_u\) at \(v,u\). This matches every prior actual live row by the given counts. Its input \(\mathbf W(S)-\mathbf H\) is zero before \(b\), including \(a\). Its grade-six commutator is zero at \(a\), hence also at \(b\) by the paid singleton ray. If \(S(b)=0\), the true grade-five primitive would give three double roots \(0,a,b\) at degree at most five, impossible. Thus \(S(b)\ne0\) and the \(-N_{i_bi_b}^2\) commutator diagonal forces \(N_{i_bi_b}=0\). Actual grade-five clean precision then gives \(JS\) proportional to \(X^2(X-a)^2(X-b)\). Its derivative would vanish at \(d\), giving \(5d^2-(3a+4b)d+2ab=0\), excluded by the fixed derivative check.

Otherwise take the actual cut immediately after the **first spending event** between \(a\) and \(b\). Exactly one repeated label has been spent. Some outside pair is still single-observed and has nonzero \(H_i/b_i\). Since the lines separate, choose its independent pure grade-five localized correction to realize arbitrary scalar value at that one label, and zero realized values at the other two repeated sites. Every late scalar \(R\) in the two-dimensional degree-four hull times \(P_1\) (roots \(0,a\) and those other two labels) is therefore genuinely available. The early forward degree-five test has roots \(b,c\) and the two remaining unspent groups. It has at least dimension one after the one ghost-mask equation. This is the [rank-two true \(5+6=11\) cut](../dirk12-fifteen-rank3-invisible-three-repeat-exclusion/README.md), with exactly one shared nonzero label, and is impossible. Thus the separable case is closed.

## Nonseparable triple: the trace ratio is determined before \(a\)

Now suppose \(\mathbf H\) is nonzero on \(d\). It sums to zero on that triple and is zero at its first live row, so its other two entries are both nonzero. In particular \(h_2\ne0\), and its local restriction and \(\mathbf G_d\) are linearly independent, since only the latter has a nonzero first component. Put
\[
                   m=(g_1-g_2)/h_2\ne0,\qquad
                   p_v=m h_v/g_1,\qquad p_u=m h_u/g_1 .
\]
For a correction \(\gamma\mathbf G+q(Y)\mathbf H\) with affine \(q\) to match a scalar constant on the first two live \(d\)-rows, it must have
\[
        q(d)=m\gamma,\qquad \text{its common normalized value is }\gamma g_1 .
\]
No other coefficient is divided by an uncertain amplitude.

At actual row \(a\) let \(T_w\) be the aggregate weighted physical tap to label \(w\), divided by \(b_a\). For \(w=d,v,u\), these are the known degree-four Lagrange integrals \(I_w=J L_w(a)\), where \(L_w\) is the cardinal on \(0,a,d,v,u\): all five labels are present and the actual weighted primitive is exact through degree four at \(a\). They are nonzero by the fixed nodal coefficient checks. The actual \(N\mathbf G\) is zero at \(a\), so the weighted tap to the second \(d\)-row equals \(g_1T_d/(g_1-g_2)\). Since the first row has zero \(\mathbf H\), the total contribution of \(d\) to \(N\mathbf H\) there is \(g_1T_d/m\). The actual \(N\mathbf H\) also vanishes at \(a\) (grade five), giving
\[
                              T_d+p_v T_v+p_uT_u=0 . \tag{1}
\]
**No vanishing of \(NY\mathbf H\) at \(a\) is assumed**: it is grade six.

There are two genuine return chronologies, one at a time:

* **The second \(d\)-row precedes the first \(u\)-row.** The scalar quartic return identity gives \(\lambda h_2=(v-d/2)(g_2-g_1)\). Nonzero \(h_2\) and \(g_2-g_1\) exclude \(v=d/2\) and \(v=2d\) in this chronology. Since the first \(v\)-amplitude is \(h_v=d^2v^3/[36(v-d)]\), this fixes
  \[
          p_v=-\frac{(v-2d)v^3}{d^3(2v-d)}.
  \]
  Then (1) fixes \(p_u\) because \(T_u\ne0\).

* **The first \(u\)-row precedes the second \(d\)-row.** At that first \(u\)-row only the first \(d\) and first \(v\) have contributed outside the physical scalar zero, and only the first \(d\) contributes to \(N\mathbf G\). If \(T_{u,d}\) is the actual normalized aggregate tap to \(d\), then \(h_u=g_1 T_{u,d}\). Its true leading scalar moments through degree two are exact, and the scalar cubic-input error equals \(\lambda h_u\). Applying that equality to \(L=X(X-v)(X-u)\) gives
  \[
   T_{u,d}\bigl[d(d-v)(d-u)-\lambda g_1\bigr]
                  =JL(u)=u^3(2v-u)/12 .
  \]
  The bracket equals \(d(v-d)(u-v/2)\). If \(u=v/2\), the right hand side is nonzero, contradiction; hence the bracket is nonzero. Comparing to \(h_v\) gives
  \[
                      h_u/h_v=\frac{u^3(2v-u)}{v^3(2u-v)} .
  \]
  This fixes \(p_u/p_v\), and (1) determines both, since \(T_d\ne0\) precludes a zero coefficient of \(p_v\) there.

For the integral checker write \(p_x=P_x/D\) in either chronology. With \(n=-(v-2d)v^3,\ l=d^3(2v-d)\) in the first chronology, take
\[
                 D=lT_u,\qquad P_v=nT_u,\quad P_u=-(lT_d+nT_v).
\]
With \(n=u^3(2v-u),\ l=v^3(2u-v)\) in the second chronology, take
\[
                 D=lT_v+nT_u,\qquad P_v=-T_d l,\quad P_u=-T_d n.
\]
The actual real guards above justify \(D\ne0\), but the modular checker never inverts \(D\), even if a reduction is zero.

## If a group is spent before \(b\), the first spending event contradicts a rank-two cut

Because no group was spent before \(a\), cut immediately after the **first** chronological spending event before \(b\). Exactly one group \(s\in\{d,v,u\}\) has been spent; the other two still have future live rows. A baseline late weighted profile \(R_0=P_a\) has zero correction. An independent quartic \(R_1\) has roots \(0,a\), with the following prescribed values on \(d,v,u\) (unlisted values zero):

- if \(s=d\), set \(R_1(v)=P_v(v-d)\), \(R_1(u)=P_u(u-d)\), using pure correction \((mD/g_1)(Y-d)\mathbf H\);
- if \(s=v\) or \(u\), let \(r\) be the other outside pair. Set \(R_1(d)=D(d-s)\), \(R_1(r)=P_r(r-s)\), using pure correction \([D(d-s)/g_1]\mathbf G+(mD/g_1)(Y-s)\mathbf H\).

This construction matches all past observations at the still-partial triple by its actual two-row trace identity, zeroes the spent group, and matches the sole observed row of each remaining outside pair. In the first case it vanishes at every past triple row because \(\mathbf G\) is absent from the correction and \(q(d)=0\). In the second case both components contribute the same scalar at the first two \(d\)-rows by \(q(d)=m\gamma\), and vanish at the complete outside group by \(q(s)=0\). Thus both \(R_0,R_1\) give true **late** weighted grade-five states.

The early forward scalar states in degree five vanish at \(b,c\) and the two still unspent repeated labels, giving a two-dimensional fixed hull space before the one quadratic ghost-mask constraint. The cut at paid \(5+6=11\) would imply rank at most one, whereas the literal 2-by-2 matrix on \(R_0,R_1\) against the two early hull multiples has rank two in each of the six finite chart families (two return chronologies and three first spent labels).

## If no group is spent by \(b\), use the grade-six ray twice, not a false clean read

No repeated group can have acquired a new row between \(a,b\) in this case: both outer groups still have one observed row and \(d\) still two. Let \(S\) be the scalar quartic with roots \(0,a\) and values \(g_1,mh_v,mh_u\) at \(d,v,u\), using the actual grade-four correction \(\mathbf G+m\mathbf H\). It matches all earlier weights by the two-row trace. As in the separable argument, its actual grade-six commutator is zero at \(a\), hence at \(b\); a vanished \(S(b)\) is impossible by three double roots. The true diagonal at \(b\) is zero. Then \(JS\) is a nonzero multiple of \(B=X^2(X-a)^2(X-b)\).

The literal clock-lifted input \(Y(\mathbf W(S)-\mathbf G-m\mathbf H)\) is grade five and has zero actual primitive at both \(a,b\). Here \(NY\mathbf G=d\,N\mathbf G\) vanishes at both singleton rows, but \(NY\mathbf H\) may not. Since its true grade is six, its restriction lies in the **same** singleton ray as the scalar error \(\mathbf E_5\). Lower scalar primitive errors of degrees at most four already vanish on these singleton rows. Consequently \(\mathbf W(J(XS))\) on \(a,b\) also lies on the same ray. At \(a\), and at \(b\) with its just proved zero diagonal, the actual input \(\mathbf W(P_a)\) has zero primitive by the same prior live numerical source set, so \(E_{5,i}=-b_i JP_a(y_i)\) at both \(i=a,b\). Because \(J(XS)(a),J(XS)(b)\) are the respective negatives of a common nonzero multiple of \(JB(a),JB(b)\) by integration by parts, their paid proportionality gives the fixed gate
\[
                         JB(a)JP_a(b)-JB(b)JP_a(a)=0 .
\]
Every one of its ordered interior roles is nonzero in the exact checker. This closes the no-spending branch, and hence the localized cubic.

## Exact arithmetic and scope

    python3 -B check.py

The standalone checker reconstructs all polynomial entries using monomial antiderivatives at the simple split prime \(1013\): 140 asymmetric first-cut choices, 80 rank-two fixed hull choices, 480 ordered coefficient roles for each of the literal tap, singleton anchor, derivative and unspent gates, and all 2880 first-spent determinants. This finite arithmetic uses only the fixed Lobatto root field. It does not reduce an unknown tableau coefficient, ghost clock or \(\mathbf G/\mathbf b\) amplitude. All actual divisions and chronology guards are proved before entering the finite algebra.

The complete analytic reduction uses the actual weighted reverse flags and paid forward/weighted products. It is not an end-to-end native Lean stage-lower theorem.
