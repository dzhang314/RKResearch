# Three literal forward ports and an altered-grade 13-stage SDIRK9 prototype

This is an actual **strict SDIRK method of exact ordinary order eight in thirteen stages**, with scalar precision eight. It is deliberately only a partial order-nine construction. It verifies a new three-port stage-sharing mechanism, pays the first missing reverse quadratic on every unprotected site, and has a separated order-nine mixed primitive failure. The unrestricted real-algebraic order-nine interval stays 13–14. The positive 14-stage witness is independent and unchanged.

## A third protected port at net zero stage cost

Start with the actual six-row forward bank in the [fourteen-stage witness](../../upper-bounds/real-algebraic/sdirk14-order9-movable-double-merge/README.md). Denote its size-four exact return by $D_4$ (valued in degree at most three) and its two true size-five ports by $v,w$. Put, in unit-diagonal coordinates,
$$
 F(X)=X(X-v)^2(X-w)^2,\qquad P=F',\qquad
 S(X)=X^3-(v+w+5)X^2+(vw+3(v+w))X-vw.
$$
The primitive $JP$ equals $F$ and $(J-I)P=(X-v)(X-w)S(X)$. In particular $P(v)=P(w)=0$ and $\mu_vP=\mu_wP=0$, for $\mu_yf=(Jf)(y)-f(y)$. If $0<v<w$, the signs of $S(0),S(v),S(w),S(+\infty)$ alternate, so there is one simple root in each of the three separated intervals. Select a real root $z\ne v,w$. At such a root $P(z)\ne0$: otherwise $F(z)=0$ and $z$ would be one of $0,v,w$, none of which is a root of $S$.

Append one physical row at $z$ with unit diagonal and strict row $\mu_zD_4$; there are no virtual predecessors. It is genuinely locally pure through size five, since every strictly read child through size four is reconstructed, and the implicit diagonal can be paid by induction from its own lower child profiles. Extend the closed-prefix map to
$$
 D_7=D_4+\frac{P}{P(z)}(\mathbf e_z^{\mathsf T}-E_zD_4).
$$
The contrast is zero on all actual trees through size four, so this degree-four-valued decoder is still exact through that cap. Its range degree is safe for every later residual, whose grade is at least four. All three evaluation rows $E_vD_7,E_wD_7,E_zD_7$ are their literal physical coordinate rows. Since $\mu_vP=\mu_wP=\mu_zP=0$, all three literal strict rows are also $\mu_vD_7,\mu_wD_7,\mu_zD_7$ on **all physical coordinates**, not only model polynomials or a lower-degree span.

The genuine size-five forward residual is
$$
 U_5=\{H\in\mathcal P_4:H(v)=H(w)=H(z)=0\}.
$$
For equality and the actual early-null claim, take the joint value of every linear combination of trees through size five: its physical stage vector in seven coordinates and its polynomial model in degree at most four. The four independent low actual columns on the original first four rows are carried by the invertible commutator $CA-AC-A^2$ (first-four diagonal $-1$) into four independent pure size-at-most-five columns. Their polynomial model is zero. The joint image projects onto all five model coefficients by the bushes and its kernel has dimension at least four by these commutator columns, so the joint image has dimension at least nine. Projection to the seven physical coordinates has kernel dimension at least two; the corresponding model polynomials vanish at all three true size-five physical ports. Thus every polynomial in the displayed two-dimensional space is the exact model of an actual early-null combination through size five. Such a polynomial is also a decoder residual, since the decoder reads zero on its old actual vector. Conversely every actual residual through size five vanishes at the three ports by the literal evaluation property. This proves the stated equality without identifying a projected residual with an actual null source by assumption.

The cost is one additional physical forward row and one additional protected suffix redirect, so the net forward cost remains four. This upgrade cannot use a cubic correction: a primitive of degree at most four cannot have double zeros at both old nonzero ports and a separate zero at zero.

## Alter the reverse grade instead of claiming a dense quadratic return

There are only three old reverse rows. A degree-two return exact on the actual words is unavailable: the polynomial columns $\mathbf1,\mathbf c,\mathbf c^2$, together with the nonzero actual pure $\mathbf g=L\mathbf c-\mathbf c^2/2$, would be four independent columns. We instead choose a degree-one return $D_r$ exact through one letter, killing the actual $\mathbf g$, on the invertible frame $\mathbf1,\mathbf c,\mathbf g$.

The physical six-site precision-eight rule has initial reverse clock $G=\gamma$, two other live sites $R,S_*$, and the three protected sites $1-Gv,1-Gw,1-Gz$. The old reverse rows occupy the three live sites, with unit clocks $1,a_r=R/G,b_r=S_*/G$ and strict rows $(),(a_r-1),(b_r-1-f,f)$. The monic quadratic residual through length two is
$$
 Q=X^2-\tfrac43X+\beta,\qquad
 \beta=\frac{(a_r^2-4a_r/3)/2+g_2/3}{g_2-1/2},
 \qquad g_2=2a_r-1-a_r^2/2.
$$
Indeed $\mu_1Q=0$ and $Q(a_r):Q(1)=g_2:(1/2)$. Choose $f$ so that the actual third quadratic defect is $Q(b_r)/(2Q(1))$. The interpolant of all actual quadratic defects is therefore $Q/(2Q(1))$. Since $D_r$ kills this actual column while paying constants and the linear clock, $X^2-D_r\mathbf c^2=Q$ and every first length-two residual is on this same line. This pays **neither a dense quadratic return nor any untested higher-order assumption**.

Every site receives a fresh reverse representative following the old bank; the order is live $0,1,2$ then protected $3,4,5$. Each old live occurrence and its fresh partner get signed/weighted half of their actual aggregate (positive in this witness), and each protected fresh row gets its full mass. Use the usual grouped law in normalized mean coordinates,
$$
 ML=E_yJD_r+T(M-E_yD_r).
$$
Here $T_{ii}=1$ and the only strict taps are $T_{j0}=\mu_{y_j}Q/Q(1)$ for the two later live sites. This makes the entire raw next primitive discrepancy on $Q$ vanish **separately at each unprotected site**, including the first by $\mu_1Q=0$. The three protected rows and columns are unit rows/columns. As in the 14-stage construction, solving for each fresh physical row by subtracting its old weighted occurrence gives literal causal lower triangular rows with diagonal one.

## Exact ordinary order eight and literal stage count

The forward tail wraps the actual weighted reverse transpose with the usual cross feed $(E_xJ-BE_x)D_7$. Its primitive error vanishes on every size-at-most-four input, so the actual suffix is pure through size five. Through order eight there is no product of two imperfect primitive children. The exact single-spine rooted decomposition only needs reverse words up to length two, except for one last primitive on a two-letter word from a size-five forward source. Shorter responses and scalar quadrature are paid by the exact low decoder and precision-eight site rule. The exceptional response lives on the line $Q$; it vanishes off the protected ports by the actual taps above, and it pairs to zero with the entire forward size-five residual because that residual vanishes at all three protected ports. This proves every ordinary tree through order eight **identically**. It is not inferred from the residual intervals.

The virtual count is $7+(3+6)=16$. In the virtual forward chronology the first three suffix rows are the protected rows in order $z,w,v$; their only suffix entries are their self diagonals, and their literal strict feeds are $\mu_zD_7,\mu_wD_7,\mu_vD_7$. Redirect zero-based virtual row 9 into 4, row 8 into 5, and row 7 into 6. Every later physical tap and output share is transferred. The final count is 13, diagonal $G>0$ after scaling.

At the fixed real-algebraic root of the seven exact equations, the contraction slopes are separated, all six weights are greater than $1/16$, and all site gaps exceed $1/64$. The equations are the two cardinal conditions and one second-port condition of the 14-stage construction with $a=3/5$, the cubic $S(z)=0$, and the three integrated sextic-hull equations for precision eight. The 312-bit fixed rational preconditioner gives center displacement at most $2^{-313}$ and Lipschitz constant at most $2^{-138}$ at radius $2^{-160}$; the same exact rational contraction and algebraicity proof as in the 14-stage packet applies.

## The actual order-nine failure and stronger structural restriction

The exact interval replay checks all 200 ordinary rooted conditions through order eight (maximum residual radius $2^{-130}$), and separates **117 actual size-nine failures**, despite the precision-eight scalar rule. One actual root with three leaves and a four-leaf bush as its fourth child has residual approximately $9.6091\cdot10^{-5}$. The marked old reverse null polynomial $XQ$ gives an explicit failed next mixed primitive: its earliest two off-port discrepancies, after multiplication by the actual sextic hull derivatives, have difference of magnitude about $0.00969273165$. Thus the failure concerns the mixed word system, not missing scalar precision.

More generally, a full order-nine tableau in this **specified** three-port, three-old, six-site grouped architecture would force reverse length-three raw accuracy at every unprotected site. Use actual early-null forward sources from $U_5$ above, and append any fixed three-letter clock/primitive context. These sources are locally pure in the virtual suffix and their early data stay zero through every letter. Also test their one-root-leaf marks, of size at most six, with the same contexts. The marked source has the exact polynomial times the literal clock, so no internal primitive error was added. Reflection of labels only introduces shorter paid words. Since $U_5+YU_5$ is the whole degree-five space vanishing at the three protected sites, its evaluations span all three off-port coordinates. Hence each raw next discrepancy vanishes there individually.

If the three old reverse rows have pure-word rank three through length three, every $K\in\mathcal P_3$ is the model of an old-null reverse word combination: correct each monomial word by its physical vector in the full pure rank-three span. Through length three this combination now has exact raw profile off ports. Any discrepancy on protected coordinates cannot tap an unprotected row, because those columns are literally protected. Consequently the mixed length-four test on $U_5$ forces all off-port raw next discrepancies, times the actual full sextic hull derivatives, to be equal. At the first two unprotected live sites $r,s$, restrict to every $K\in(Y-r)\mathcal P_2$ to kill the only candidate earlier live tap. The two functionals $\mu_r,\mu_s$ must be proportional there. For nonzero $r,s$, the minors on the pairs of basis polynomials
$$
 (Y-r,\,Y(Y-r)),\qquad (Y(Y-r),\,Y^2(Y-r))
$$
would force both
$$
 s^2-sr-3\gamma s+\gamma r=0,\qquad
 s^2-sr-4\gamma s+2\gamma r=0.
$$
They differ by $\gamma(s-r)\ne0$. If $s=0$ and $r\ne0$, the first minor is already nonzero; for $r=0$ and $s\ne0$, the nonzero shifted primitive cannot annihilate both $Y,Y^2$. Thus any exact order-nine solution in this chart needs actual old pure rank **two**, not three.

On three old rows with first normalized clock 1 and second $a$, a regular pure rank-two choice with $g_2\ne0$ forces the third normalized clock $b=2a-1$ if its second tap is nonzero, and $b=4-a$ if that tap is zero. This follows from the actual two relations $L\mathbf g=\mathbf g+(C-I)\mathbf g/(2g_2)$ and $\mathbf d=2(L+C)\mathbf g/3$, determined by the first two rows. If two old rows are literal twins the paid modeled frame cannot be invertible; if $g_2=0$ then $a^2-4a+2=0$ is the exceptional branch. The exact interval replay separates all three exclusions ($x^2-4Gx+2G^2$, $y-2x+G$, $x+y-4G$) for every allowed old clock choice in this fixed mesh. Thus no allowed pure-rank-two retuning of the old three rows on this exact grid can rescue order nine. This is not a stage lower bound for either unrestricted strict SDIRK or every movable three-port mesh.

## Reproduction and native status

    sha256sum -c sources.sha256
    python3 triple.py check root.json /tmp/actual-13-stage.json
    cmp actual-13-stage.json /tmp/actual-13-stage.json

The default replay uses only the Python standard library. The independently isolated root fixture and literal interval matrix are included. The borrowed exact directed-arithmetic engine from the 14-stage packet is copied without changing that frozen packet.

The [typed Lean audit](../../lean/evidence/sdirk9-triple-port-20261127/README.md) verifies the exact cubic factor, the rank-one update of actual linear reads, the reviewed ordinary order-eight specialization, and all three chronological diagonal-twin contractions on Lean 4.36.0. The concrete dyadic root isolation is an independently replayed rational certificate rather than an unconditional Lean existence theorem.
