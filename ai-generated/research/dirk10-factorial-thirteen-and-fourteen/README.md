# Factorial-localized DIRK order ten in 13 stages

The [literal 13-stage tableau](tableau13.json) has **exact order ten over \(\mathbb Z[1/10!]\)** and over every nonzero commutative ring inverting \(10!\). Together with the separately known rational lower bound, the minimum over \(\mathbb Z[1/10!]\) is now **12–13**. This lowers the prior unconditional 17-stage upper coming from ERK inclusion, and differs from the earlier 12-stage local/finite-characteristic portfolio. It does not prove an unconditional 12-stage upper. The [intermediate 14-stage tableau](tableau14.json) is also an independent factorial-localized witness.

The two common denominators are
\[
   D_{13}=10890936000=2^6 3^4 5^3 7^5,\qquad
   D_{14}=8401579200=2^6 3^7 5^2 7^4 .
\]
They divide \((10!)^5\) and \((10!)^4\) respectively. Both have unequal nonzero diagonals and distinct literal rows. Neither assumes an ordered ring, a field, or that any other prime is invertible.

## Three unit donors in the raw reflected system

Keep the ten scalar sites \(j/6\) for \(-3\le j\le6\), with degree-nine interpolatory weights; the origin's weight goes on the old zero row. The reverse chronological suffix for width 13 is
\[
   (1,-1/2,-1/3,-1/6,5/6,2/3,1/2,1/6,1/3).
\]
The future merged rows are the last three reflected sites. The first three weights, at \(1,-1/2,-1/3\), are \(7/150,3/2800,-3/280\), all units of the localization. Use the **raw** reflected transpose \(K\), with \(\mathbf y=\mathbf1-\mathbf x\) and weights \(\mathbf w\) carried by the reverse vectors. In particular one does not divide each row by its own output weight.

Pay the first three actions
\[
 K\mathbf w=\mathbf w\odot\mathbf y,\qquad
 K(\mathbf w\odot\mathbf y)=\mathbf w\odot\mathbf y^2/2,\qquad
 K(\mathbf w\odot\mathbf y^2)=\mathbf w\odot\mathbf y^3/3+\mathbf U .
\]
The endpoint \(1\) has \(U_1=0\). On the eight proper sites use the Lagrange density
\[
 U_i=\frac{\tau\bigl(1-6(x_i+1/2)\bigr)}{x_i P_8'(x_i)}
\]
for their nodal polynomial \(P_8\), fixing \(\tau\) from the actual second reverse trapezoidal row. This kills \(X,\ldots,X^6\). The first three action columns on the three unit donor sites have a paid Vandermonde inverse. Later rows may create free changes in the other available columns while preserving these actions.

The actual top tests are the orthogonality of
\[
 K(\mathbf w\odot\mathbf y^3)-\mathbf w\odot\mathbf y^4/4,\qquad K\mathbf U
\]
to the three true source polynomials below. These are six linear conditions on the paid null directions of the previous actions. Clearing the row denominators and contents gives Smith factors \(1,1,1,42,210,5880\), all units. The supplied exact solution is checked directly, rather than relying on a Smith oracle. No within-port unknown tap is used.

## Actual ports and the extra rank-one correction

For width 13 the seven opening clocks are
\[
         0,\ 1/12,\ 1/6,\ u=1/3,\ p=2/5,\ q=1/6,\ r=1/2 .
\]
The repeated clock \(1/6\) denotes two distinct physical stages. Use trapezoidal stage 2, Simpson stage 3 and Simpson stage 4 (which skips stage 2), and a four-donor cubic stage 5. Let \(\Pi\) interpolate on the actual clean coordinates at \(0,u,p,q,r\), and put
\[
 H(X)=X(1-14X+56X^2-84X^3+42X^4),\quad
 \sigma=(A_{u,\bullet}-J_u\Pi)/H(u).
\]
Open \(q,r\) with rows \(J_q\Pi+H(q)\sigma,\ J_r\Pi+H(r)\sigma\). The forbidden future coefficient in the \(q\) row vanishes because \(p=2/5\) solves the exact affine gate in the [rational three-port proof](../dirk10-twelve-rational-three-ports/README.md). The first size-six projected residuals are in the span of
\[
      H,\quad F_0=X(X-u)(X-q)(X-r),\quad XF_0
\]
by the actual rank-one port values. The raw top system pays all three polynomials. Set \(\eta_i=H(x_i)\) on the proper sites and \(\eta_1=H(1)-J_1H/w_1\) at the endpoint \(1\). Unlike in the restricted nine-site symmetric family, here the endpoint weight is a unit. The builder independently verifies orthogonality to all 31 actual reflected words through length four.

The forward cross block is \((EJ-TE)\Pi+\boldsymbol\eta\sigma\). The first three suffix rows are at \(u,q,r\) and have no internal suffix action. They are **exactly** old rows 4, 6, 7, including all zero padding. Cross-term and weight redirects leave \(7+9-3=13\) **actual** rows. The independent literal verification does not assume the projected proof or the row contractions.

The 14-stage alternative drops the rank-one correction, uses \(u=1/5,p=1/14,q=1/6,r=1/2\) and the two true local size-six ports \(q,r\), replaces the last reverse order as recorded in the data, and pays sources \(X(X-q)(X-r)P_2\). Its six Smith factors \(1,3,6,84,1260,17640\) are also units. It merges exactly two complete rows.

## Exactness in every specialization

For both tableaux the normalized eleventh bush has defect \(179/279936\). The tree with two leaves and one eight-vertex bush as children has factorial 88 and normalized defect \(-9809/1049760\). The denominators divide each \(D_s^2\), and
\[
                   274(179)+5(-9809)=1 .
\]
Both eleventh conditions cannot hold in any nonzero ring inverting the tableau denominator. No single next bush is assumed nonzero in every specialization.

    python3 -B audit_tableau.py
    python3 -B rebuild.py 13 --emit /tmp/dirk-factorial13.json
    python3 -B rebuild.py 14 --emit /tmp/dirk-factorial14.json
    cmp tableau13.json /tmp/dirk-factorial13.json
    cmp tableau14.json /tmp/dirk-factorial14.json
    sha256sum -c sources.sha256

These are the original rational solutions with the recorded Smith tap vectors. Regeneration and the independent all-tree witness checks require only the Python standard library. Native kernel evidence, if supplied, is a separate receipt.

A [compact 13-stage variant with a full Lean proof](../dirk10-factorial-thirteen-compact/README.md) improves coefficient size while retaining the same universal upper bound. The original two tableaux above are unchanged.
