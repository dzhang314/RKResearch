# DIRK12/15: the high visible cubic when the reverse rank is four

Consider the actual fifteen-stage real DIRK order-twelve equality frame, with \(C(2)\) and \(f_5=\dim F_5=3\). Here \(T_j\) is the genuine numerical rooted space, \(F_j\) the zero-profile rooted space, and the grade is tree order minus one. Put \(\mathbf c=A\mathbf1\), \(C=\operatorname{diag}(\mathbf c)\), \(\beta\mathbf v=\mathbf b\odot\mathbf v\), and \(\mathbf h=A\mathbf c^{\,2}-\mathbf c^{\,3}/3\). Assume the **true grade-six reverse flag** \(\mathcal B_6\) has rank four, and that the cubic is visible: \(\beta\mathbf h\ne0\). Then only these two reduced possibilities remain:

1. At the active dirty rows, \(h_i=P(c_i)\) for a nonzero polynomial \(P\) of degree at most three. There are exactly ten such physical rows at distinct labels and exactly three distinct active clean interior labels, plus the literal origin and terminal. **The terminal weight is not \(1/42\); in particular some genuine \(F_6\) element has nonzero terminal value.**
2. At the active dirty rows, \(D(c_i)=T(c_i)h_i\), where \(D=L'_6\) is the fixed shifted-Legendre derivative and \(T\ne0\) has degree at most two. This is the not-necessarily-polynomial branch. The formula permits singular \(T(c_i)=D(c_i)=0\) and makes no division there. Both endpoint weights are \(1/42\), every other active clean clock is a root of \(D\), and all \(F_6\) vanish at the terminal.

No assertion excludes either remaining possibility. These are reductions on the rank-four **visible** band only, not a change to the real 15–16 interval.

## Genuine rank and the two endpoint cards

Use the [actual fifteen-stage frame](../dirk12-fifteen-frame/README.md), the [weighted grade-six band](../dirk12-fifteen-weighted-reverse-band/README.md), and the [active-support census](../dirk12-fifteen-rank3-four-active-cubic/README.md). Let \(o,t\) be the literal origin and terminal. They are clean, \(c_o=0,c_t=1\), and \(b_t\ne0\). Both leading adjoint differences vanish. The earlier five-label reflected support argument needs only actual reverse ranks \(1,2,3,4\) through grades 3–6, available here. Thus \(\beta\mathbf h\in\mathcal B_3\) spans the nonlocal reflected cubic line and has \(r\ge5\) active physical labels. The exact support census excludes \(5\le r\le9\), hence \(r\ge10\). The rank-four reverse flag now has exactly the moment form
\[
           \mathcal B_6=(\beta\mathbf h)P_3(\mathbf c).
\]
It vanishes on **all** clean rows and on any zero-weight row; this conclusion concerns the actual reverse chronology, not a normalized full adjoint order statement. The broader terminal-zero annihilator
\[
 Z=\{\boldsymbol\lambda\in\operatorname{Ann}T_5:\lambda_t=0\}
\]
has dimension five by the genuine \(q=5\) debit, and contains \(\mathcal B_6\).

The moment space at grade six is separated by the literal zero origin:
\[
           T_6=P_6(\mathbf c)\oplus F_6,\qquad f_6=5.
\]
The actual endpoint \(\mathbf e_t\in T_6\) has unique scalar component \(b_t X D(X)\). In fact the endpoint product tests against scalars through degree five give the moments \(b_t\) (the pure \(F_6\) terms vanish on these probes). Its scalar component vanishes at \(0\), so the \(X\,dX\) Gram is nonsingular. Integration by parts gives \(\int X^{k+1}D(X)\,dX=1\) for \(0\le k\le5\), identifying the component. Hence
\[
         \mathbf e_t-b_t C D(\mathbf c)\in F_6.
\]
This uses the true \(6+5=11\) budget, not a purported grade-six unanchored debit. If \(F_6\) is clean at the terminal then \(b_t=1/42\). More generally, \(b_t=1/42\) alone makes this particular card terminal-zero, so if \(b_t=1/42\) then
\[
 \mathbf K_t=\beta[C D(\mathbf c)]-\mathbf e_t\in Z.
\]
This latter card is used only under the explicit weight condition \(b_t=1/42\).

Always, the opposite card is
\[
 \mathbf K_o=\mathbf e_o+\beta[(I-C)D(\mathbf c)]\in Z .
\]
To prove it, write a \(T_5\) element as \(P(\mathbf c)+\mathbf f\) with \(P\) degree at most five and \(\mathbf f\in F_5\). The real origin is zero on \(F_5\). The paid \(5+6=11\) products give the scalar integral \(\int (1-x)D(x)P(x)\,dx=-P(0)\) by integration by parts and the fixed Legendre orthogonality, canceling the origin evaluation. The vector is literally terminal-zero. We use \(D(0)=-42,D(1)=42\).

## Uniform cubic: an exact reflected pivot

If \(\beta\mathbf h^{\,2}\in\mathcal B_6\), then some polynomial \(P\) of degree at most three gives \(h_i=P(c_i)\) on all active dirty physical rows, by dividing only \(b_i h_i\) there. Let \(V\) be the monic hull of the active clean clocks outside \(\{0,1\}\), of degree \(k\). If \(k\le1\), the scalar polynomial \(x(1-x)V(x)^2P(x)\) of degree at most seven is a paid cubic probe; it vanishes on clean sites. The resulting scalar quadrature of \(x(1-x)V^2P^2\) is zero, contrary to the strictly positive real integral (degree at most ten). Thus \(k\ge2\), and the physical count \(r+k+2\le15\) gives \(k\le3\). For \(k=2\), the same weighted mask \(x(1-x)V\) and all multipliers of degree at most four give \(VP\perp P_4\) for \(x(1-x)\,dx\); these probes have degree at most eight and the scalar integral degree at most eleven. Consequently \(P\) is cubic and \(VP\) is proportional to \(D\). In particular \(P\) is a fixed cubic factor of \(D\), a case ruled out below.

Write \(y=1-x\) and \(P^\rho(y)=P(1-y)\). In actual reflected chronology consider the weighted grade-four contrast
\[
                 \mathbf z=\beta[\mathbf y\odot(P^\rho(\mathbf y)-\mathbf h)] .
\]
It is zero on all active dirty rows and all unweighted rows. It is not identically zero: otherwise its scalar part \(\beta[\mathbf y\odot P^\rho(\mathbf y)]\) equals the genuine reverse pure vector \((\beta\mathbf h)\odot\mathbf y\) of grade four. Pair this with \(P(\mathbf c)\) (grade at most three) to obtain the impossible positive integral \(\int y(P^\rho(y))^2\,dy=0\). At the first nonzero coordinate, take \(v=y_i\), necessarily nonzero and \(P^\rho(v)\ne0\). The actual lower triangular reversed commutator \(YN-NY-N^2\) gives \(-A_{ii}^2 z_i\) on that row, yet belongs to \(\mathcal B_6\) and reads zero on this clean pivot. Thus \(A_{ii}=0\); applying the actual primitive directly to \(\mathbf z\) and to \(Y\mathbf z\) pays
\[
                J[XP^\rho](v)=J[X^2P^\rho](v)=0 .
\]
These outputs have grades at most five and six. No ordinary forward ordering, ghost cancellation or extra commutator grade is presumed.

Two fixed-polynomial receipts are used:

- For every monic degree-two or degree-three factor \(W\) of \(D\), the residual polynomials of \(J[XW](v)/v^2\) and \(J[X^2W](v)/v^3\) are coprime, with unchanged degrees in the modular proof. Thus both cannot vanish for any \(v\ne0\).
- For every monic quadratic factor \(U\) of \(D\) and every \(v\in\{1\}\cup\{D=0\}\) with \(U(v)\ne0\), the determinant of the \(2\times2\) moment matrix for \(XU(X)\,dX\) on \([0,v]\) is nonzero. Equivalently the two paid primitives cannot both vanish for \(P^\rho=(X-\sigma)U\), for any parameter \(\sigma\).

The first receipt already rules out \(k=2\). Then \(k=3,r=10\) and the physical count is exact, establishing the first case's row census.

Now suppose \(b_t=1/42\). Both \(\mathbf K_o,\mathbf K_t\) are then in \(Z\), without assuming the last value of any other \(F_6\) vector is zero. If \(\mathbf K_o\in\mathcal B_6\), evaluating on the active dirty labels gives \((1-X)D=P R\) as a polynomial identity: the two sides have degree at most six and agree at \(r\ge10\) distinct labels. Thus \(P\) has degree three, and the clean clocks outside the ends are all roots of \(D\) by the clean zero entries of \(\mathbf K_o\). Since \(D(1-X)=-D(X)\), \(P^\rho\) either is a cubic factor of \(D\), or is \(X\) times a quadratic factor of \(D\). The former is excluded by the first receipt at any pivot. In the latter case the pivot is a fixed \(D\)-root or \(1\), and the second receipt excludes it.

Otherwise \(\mathbf K_o\notin\mathcal B_6\), and the codimension-one quotient gives \(\mathbf K_t-\lambda\mathbf K_o\in\mathcal B_6\) for some scalar \(\lambda\). Evaluating on the dirty rows now gives
\[
       [X-\lambda(1-X)]D(X)=P(X)R(X)\quad(\deg R\le3).
\]
The nonzero affine factor may be constant (when \(\lambda=-1\)); in that case \(\deg P\ge2\) and \(P\) is a factor of \(D\), already excluded. If not constant, \(\deg P=3\). If \(P\) divides \(D\), apply the first receipt. Otherwise it has that affine root and two distinct roots of \(D\), allowing also an affine root coincident with one of the two. On every **active clean interior**, the same product \([x-\lambda(1-x)]D(x)\) is zero by the zero clean entries of the card combination. A pivot with \(P(c_i)\ne0\) therefore cannot be the affine root, leaving only a fixed \(D\)-root or in reflected coordinates the endpoint \(1\). The second receipt then excludes this pivot. This proves \(b_t\ne1/42\) and hence the genuine terminal-dirty \(F_6\) restriction in case 1.

## The nonpolynomial branch reduces to a quadratic denominator

Now let \(\beta\mathbf h^2\notin\mathcal B_6\). The actual rooted products put it in \(Z\), so \(Z=\mathcal B_6+\langle\beta\mathbf h^2\rangle\), entirely supported on active dirty rows. Also \(F_6=\mathbf hP_3(\mathbf c)+\langle\mathbf h^2\rangle\) by dimension and the independence after weighting. Thus \(F_6\) is terminal-clean and \(b_t=1/42\). Evaluating \(\mathbf K_o\) on the literal origin gives \(1-42b_o=0\); at every other active clean clock besides the two ends, \(D(c_i)=0\).

Resolve the two cards in \(Z\) and divide by \(b_i\) only on active dirty rows. There are \(P,Q\) of degree at most three and scalars \(a,d\) such that on those rows
\[
                    cD=hP+a h^2,\qquad (1-c)D=hQ+d h^2 .
\]
Define \(T=P+Q,\ \delta=a+d,\ R(X)=\delta X-a,\ S=dP-aQ\). At all these dirty labels the genuine identities give \(D=hT+\delta h^2\) and \(RD=hS\).

- If \(\delta=0\) but \(a\ne0\), then \(D=hT\) and \(h=(cT-P)/a\) at all dirty rows (all have \(h\ne0\)). Consequently \(D=T(XT-P)/a\) polynomially, since the degree is at most seven and \(r\ge10\). A degree-three \(T\) would give degree seven, impossible; for degree at most two \((XT-P)/a\) is cubic or lower. This gives \(\beta\mathbf h^2\in\mathcal B_6\), contrary to the branch.
- If \(\delta\ne0\), then \(R\) is affine nonconstant, and the two identities imply \(S^2-RTS-\delta R^2 D=0\) on all dirty labels: multiply the first by \(R\), use \(RD=hS\), and use nonzero \(h\) rather than dividing by any unknown \(R(c)\) or \(D(c)\) (if \(R(c)=0\), then \(S(c)=0\)). More explicitly \(S=R(T+\delta h)\) at each dirty label, so substitution gives the claimed zero. Degree at most seven and the label count give the polynomial identity. At the root \(\rho\) of \(R\) it forces \(S(\rho)=0\). Write \(S=RU\) and obtain \(D=U(U-T)/\delta\), with \(\deg U=2\) by the degree-five derivative and \(\deg T\le3\). Put \(W=(U-T)/\delta\), a true cubic factor of \(D\). On every dirty label other than \(\rho\) the equality \(S=R(T+\delta h)\) gives \(h=W(c)\). At \(\rho\) the quadratic equation is \(\delta(h-W)(h+U/\delta)=0\), so there is at most one other possible amplitude. Each anomalous row has that same amplitude at that same label. They cannot be absent, since otherwise \(\beta\mathbf h^2\in\mathcal B_6\). The genuine terminal-zero pure vector \(\beta(\mathbf h^2-\mathbf hW(\mathbf c))\in Z\) is supported precisely on the anomalous rows with one common nonzero coefficient times \(b_i\). Its pairing with the stage constant forces their ordinary weights to sum to zero. Thus there are at least two such physical rows, and they can be dropped from the scalar moments and the cubic probes. On the remaining regular dirty labels \(h=W(c)\). If there are at most nine such labels, the actual eight-degree cubic probes give zero aggregate on each by Vandermonde, consuming at least two rows per label. There are at least nine regular labels because \(r\ge10\) and only one label could be exceptional, impossible. Thus at least ten regular dirty rows, at least two anomalous rows, and the two literal endpoints leave at most one active clean interior. The scalar mask \(x(1-x)V(x)^2 W(x)\) now gives the same impossible positive square integral as before (anomalous signed sums vanish). This excludes the entire \(\delta\ne0\) branch.
- Hence \(a=d=0\). The sum gives \(D=hT\) at all active dirty labels. This polynomial \(T\) is nonzero (the dirty labels cannot all be roots of \(D\)). The identity \(XT=P\) follows by division only by \(h_i\ne0\) at all \(r\ge10\) labels and the degree bound. Therefore \(\deg T\le2\), as claimed.

## Exact arithmetic and proof scope

The stand-alone check forms the degree-two and degree-three squarefree root factors of \(D=-42+840X-5040X^2+12600X^3-13860X^4+5544X^5\), the two primitive residual polynomials for each, and all quadratic-factor pivot determinants. It independently verifies 20 gcds and 40 determinants at each of two primes, 43 and 181, where \(D\) has five distinct roots. Fixed-degree resultants of the coprime pairs and the determinant product lift their nonvanishing in characteristic zero by taking the symmetric product over all root choices. The integration denominators and leading coefficients are units at both primes. No unknown DIRK coefficient is reduced modulo a prime.

The portable **DIRKOrderTwelveFifteenHighVisibleArithmetic** checks the 20 fixed-degree coprime pairs and the 40 moving-factor determinants modulo 43, importing the compatible core arithmetic from the four-active-label packet. Both modules build on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 with standard axioms only. The 181 verification is the independent Python replay. The actual rooted and causal ingredients have separate native checks in the equality, reverse, and four-active-label packets. The endpoint-card and high-branch reductions given here are mathematical, not an end-to-end native branch exclusion.

    python3 -B check.py
    sha256sum -c sources.sha256

From **ai-generated/lean**:

    lake build +RKCert.ReviewedNative.DIRKOrderTwelveFifteenHighVisibleArithmetic
