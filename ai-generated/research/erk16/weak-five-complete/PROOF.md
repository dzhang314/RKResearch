# The complete paid weak-five scalar obstruction

**Theorem.** Over any ordered field there is no actual `WeakFive16.Moments q Z c`. More generally, the scalar conditions below are inconsistent even without nonvanishing of $q$ at the inserted origin. This is a mathematical proof using finite rational certificates and ordered real-closure algebra; the full chain has not been checked in Lean.

## 1. Exactly what is used

Put $(u,a,h,z)=(c_1,c_2,c_3,c_4)$ and $w=X(1-X)$. The four marked clocks are distinct, different from 0 and 1, and $q$ is nonzero at each. Also $q\ne0$, $\deg q\le4$, and $Z=(X-a)(X-h)$. The six local equations and the global equations are
$$
\begin{gathered}
 I_{0,u}(Xq)=I_{0,u}(X^2q)=I_{0,a}(X(X-u)q)=0,\\
 I_{z,1}((1-X)q)=I_{z,1}((1-X)^2q)=I_{h,1}((1-X)(z-X)q)=0,\\
 I_{0,1}(wqN S)=0\quad(\deg S\le5),\qquad
 N=(X-u)(X-a)(X-h)(X-z).
\end{gathered}
$$
Here $I_{l,r}$ is formal antiderivative difference; $N$ is exactly `nodalTail c Z`. These are the fields of the reviewed packet in `ERKOrder16WeakFiveMoments.lean` (distinctness and $c_0=0$ give $c_i\ne0$ for $i>0$). Nothing below needs $q(0)\ne0$ or $q(1)\ne0$.

Normalize $q$ to monic when convenient. Work in an order-preserving real closure; identities and strict signs from the original field persist there. The fixed positive rational 19-point integration rule is exact through degree 19, also under every increasing affine substitution. Its data and all twenty monomial equalities are included in [check_references.py](check_references.py), independently of any numerical input. We use this rule to justify each strict sign-definite polynomial integral. In the relevant degree range, an integrand that is nonnegative on the mesh and has a positive sample has positive integral. Integrals, weights and affine substitutions are algebraic; the intermediate-value property for polynomials over a real closed field suffices for root selection.

Let $e$ be the number of exterior marks and $k$ the number of sign-changing roots of $q$ in $(0,1)$ (distinct roots of odd multiplicity). If $N=\pm E D$, where $E$ is the product of exterior factors oriented positive on $(0,1)$ and $D$ the product of interior factors, the tests $S=D H$, $\deg H\le e+1$, pay
$$
 I_{0,1}(w E D^2 qH)=0.
$$
If $k\le e+1$, take $H$ as the product of the odd-multiplicity unit roots and orient it so that $qH\ge0$ on the unit interval. The resulting nonzero integrand has degree at most 15 and so cannot vanish at all 19 samples. Thus $k\ge e+2$. In particular $e\le2$, degree at most one is impossible, and any $e=2$ packet has degree four with all four roots simple and interior. The two endpoint pairs each require at least two sign-changing roots in their oriented interval between $0,u$ or $z,1$: if there were at most one, an affine sign fit would contradict the pair under its fixed-sign weight. The interval is reversed first if necessary and the weight given positive orientation. For these sign fits, the integrand degree is at most six.

Throughout we may reflect $X\mapsto1-X$ and send
$$
 (u,a,h,z)\longmapsto(1-z,1-h,1-a,1-u).
$$
The forward and reverse tests swap, with exactly the original factors; the global test is reflected in the same degree range. For a monic profile of degree $d$ use $(-1)^d q(1-X)$ if we want monicity preserved. This reflects the six equations and the four nonorigin marks, not an extra hypothesis at the inserted origin. In particular a previously unmarked endpoint root is harmless.

Write
$$
 F(t)=I_{0,t}(X(X-u)q),\qquad G(t)=I_{t,1}((1-X)(z-X)q).
$$
The local words give $F(0)=F(u)=F(a)=0$ and $G(z)=G(h)=0$. Thus the true local difference windows $I_{u,a}(X(X-u)q)=0$ and $I_{h,z}((1-X)(z-X)q)=0$ are paid.

## 2. The exact square balance and two exterior directions

Write $L=X(X-u)$ and $P=(X-1)(X-z)(X-h)$. The polynomial $F$ factors as $F=LV$ with $V=(X-a)J$, $\deg J\le4$: these are its three distinct zeros at $0,u,a$ and $\deg F\le7$. The global test $J$ pays $I_{0,1}(P V F')=0$, since $F'=Lq$ and $wqNJ=-P V F'$. The derivative of $PLV^2$ is $(P'L-PL')V^2+2P V F'$, and the former product vanishes at 0 and 1. Consequently
$$
 u\,I_{0,1}(F^2)=zh\,I_{0,1}((F/X)^2)+P(u)\,I_{0,1}((F/(X-u))^2),                 \tag{1}
$$
by expansion of $u(P'L-PL')=u L^2-zh(X-u)^2-P(u)X^2$. These are polynomial quotients. Every squared integral is strictly positive since $F'\ne0$ and the degrees fit the rule. In particular:

* If $z<0$ and $0<u,h<1$, (1) gives $P(u)>0$, hence $u<h$.
* If $0<z<u<1$ and $h<0$, then $zh<0$ and $P(u)<0$, impossible. Reflect for $a>1$ with the same outer overlap.

If $u,z$ are interior and $u<z$, the two disjoint endpoint windows require four distinct odd roots, so $q$ is a monic quartic with two simple roots in each window and is strictly positive on the gap and outside the unit interval. This rules out $a>1$: the actual difference $I_{u,a}(X(X-u)q)=0$ has positive contributions on $(u,z)$ and $(1,a)$. Moreover $I_{z,1}(q)>0$. To see this, multiply by the monic quadratic of the two right roots; its product with $q$ is nonnegative with a positive sample, and writing that quadratic as its positive value at 1 plus a linear combination of $(1-X),(1-X)^2$ proves the assertion by the right pair. Hence
$$
 I_{z,1}(X(X-u)q)=(1-u)I_{z,1}(q)>0
$$
by expanding $X(X-u)$ in the same basis. The three contributions contradict the paid difference. Reflection rules out $h<0$ in the disjoint case. Altogether if both outers are interior, neither $a>1$ nor $h<0$ is possible.

### Two exterior marks

Here $q$ has four simple unit roots and is positive on the exterior. Thus $u>0$ and $z<1$ by their own exterior end test otherwise; then $a>0$ and $h<1$ by their own inner tests otherwise. If both $u,a>1$, the true difference between them has fixed nonzero sign because $X-u$ does, impossible. If both $z,h<0$, reflect. Therefore the exterior labels must be one of $\{u,a\}$ to the right, one of $\{z,h\}$ to the left. Both inner external is already impossible by the previous paragraph.

We need a simple reciprocal sign fact for the remaining choices. If $W=(X-\ell_1)(X-\ell_2)(d_1-X)(d_2-X)$ with $\ell_i\le0$, $d_i\ge1$, and a monic degree-six $T$ is orthogonal through degree five for $W$ on $(0,1)$, then
$$
 I_{0,1}(T)>0.                                                               \tag{2}
$$
In fact the sign-fit argument forces six distinct simple unit roots of $T$. At these roots interpolate $f=1/W$ by a polynomial $H$ of degree at most five. The order-six divided differences of $f$ on this interval are strictly positive. Indeed for a reciprocal right pole $1/(d-X)$ every divided difference is positive, and for a reciprocal left pole $1/(X-\ell)$ its sign in order $j$ is $(-1)^j$, by the elementary divided-difference formula. The product rule preserves these signs for products with poles all on the same side. Expand mixed products using
$$
 [(X-\ell)(d-X)]^{-1}
 =(d-\ell)^{-1}\big((X-\ell)^{-1}+(d-X)^{-1}\big).
$$
First pair the four factors into two mixed pairs; in the four resulting products split any remaining mixed pair. This expresses $f$ as a positive sum of single poles and products with poles all on one side, so every even-order divided difference in question is positive. For clarity, the reciprocal formula follows by subtracting the value at a knot and dividing by $X-\text{knot}$; the product rule follows by telescoping a difference of products and iterating. At any $x$ other than an interpolation knot, $f-H=T$ times the order-six divided difference with $x$ appended. Thus the **polynomial** integrand $T-WTH=WT(f-H)$ is nonnegative and has a positive sample, since $T$ has only six roots. Its degree is at most 15 and $I_{0,1}(WTH)=0$. This proves (2); no rational function is integrated.

For $z<0<u-1$ use $W=w(X-z)(u-X)$ and $T=q(X-a)(X-h)$ in (2). The paid combination
$$
 (1-h)I_{0,u}(X(X-a)q)-h I_{z,1}((1-X)(X-a)q)=0
$$
has integrand $T$ on the unit overlap. On $(1,u)$ and $(z,0)$ the remaining terms are positive, because $a,h$ are interior and $q$ is positive outside. This contradicts (2). For $z<0,a>1$, use $W=w(X-z)(a-X)$, $T=q(X-u)(X-h)$, and the paid combination
$$
 (1-h)I_{0,a}(X(X-u)q)-h I_{z,1}((1-X)(X-u)q)=0.
$$
The same calculation gives $T$ on the overlap and positive exterior contributions. Reflection handles $u>1,h<0$. That exhausts $e=2$.

## 3. The single exterior cases

If $e=1$, $u<0$ or $z>1$ is impossible: its own endpoint pair would require two new, disjoint exterior changes, in addition to at least three unit changes. Hence the only outer directions are $z<0$ and $u>1$. If the single exterior is inner, both outers are interior; the preceding wrong-direction argument leaves exactly $a<0$ or its reflection $h>1$.

### Sole outer exterior

Reflect so that $z<0$ and $u,a,h\in(0,1)$, taking $q$ monic after reflection. Equation (1) forces $u<h$. The left pair supplies two unit roots before $u$ and the paid inner suffix at $h$ supplies one after $h$. We claim that there is exactly one root after $h$ and that
$$
 q=C\prod_{r\ {\rm unit}}(X-r),\qquad C>0\ \text{on }(0,1),                     \tag{3}
$$
with all indicated unit roots simple. In degree three this is immediate, $C=1$. In degree four, if $q(0)<0$, monic far-left positivity supplies a fourth, simple root below zero, so $C=X-\alpha$ with $\alpha<0$. If $q(0)=0$, that endpoint root uses the last degree, so $C=X$. These cover the reflected endpoint seam irrespective of the original $q(1)$.

If $q(0)>0$ and only two unit changes occur before $h$, they already occur before $u$. There is no other root on $(0,h)$: a remaining even root would use two more degrees, and a further simple root would add a change. The phase on $(u,h)$ is positive. On $(z,0)$ it is also positive, since a negative exterior root would have to be simple and the only degree outside the three demanded unit changes, making $q(0)<0$. As before the quadratic of the two roots in $(0,u)$ gives $I_{0,u}(q)>0$ by the left pair (use its positive constant coefficient). Set $V=(1-X)(X-z)$. The actual reverse difference gives $I_{z,h}(Vq)=0$, but its middle contribution is $I_{0,u}(Vq)=-zI_{0,u}(q)>0$ and both other contributions are positive. This is impossible. Hence there are three unit changes before $h$ and exactly one after, saturating degree four, with $C=1$. This proves (3).

Let $r_*$ be the unique root after $h$. If $a<h$, let $D$ be the product of all unit roots below $h$ times $(X-u)(X-a)$. This is a paid test, $\deg D\le5$. Its global integrand is $w(X-z)C D^2(X-h)(X-r_*)$, so its prefix on $(0,h)$ has positive integral. On $(h,1)$ it is $V q\,B$ with
$$
 B=X(X-h)(X-u)^2(X-a)^2\prod_{r<h}(X-r).
$$
There all factors are positive and increasing. And $q$ transitions from negative to positive at $r_*$. Since $I_{h,1}(Vq)=0$ is the true inner word up to sign, subtracting $B(r_*)$ proves this suffix integral is strictly positive as well. This contradicts the paid global zero. Thus $a>h>u$.

Now split the unit factors as $P_LP_R$ by location before and after $u$, with respective degrees $p,k$ and $p+k\le4$. On $(0,u)$ put
$$
 D_+=(1-X)(u-X)P_R^2(X-a)^2(X-h)^2,\qquad g=|P_R|/D_+ .
$$
Here $g$ is the product of reciprocal right poles at $1,u$, the roots after $u$, and doubled poles at $a,h$; all poles lie at or above $u$. Let $H$ be its degree-at-most-$(p-1)$ Newton interpolant at the left roots. The divided differences of $g$ at these knots are positive, so $H(x)>0$ for $x>u$, and on $(0,u)$ the remainder is $g-H=P_L$ times a strictly positive divided difference away from the knots. Use the paid global test $P_R(X-a)(X-h)H$ (degree at most $k+2+p-1\le5$). Add $(-1)^k$ times the actual left zero $I_{0,u}(X(X-z)q)=0$, an affine combination of the endpoint pair. On $(0,u)$ the sum of integrands is
$$
 X(X-z)C P_L D_+(g-H)\ge0 ,
$$
with positive samples by the remainder sign. On $(u,1)$ the unchanged global integrand is
$$
 w(X-z)C P_L(X-u)P_R^2(X-a)^2(X-h)^2H\ge0 ,
$$
again with positive samples. The equalities exercise only polynomial integrals of degree at most 15. This contradiction excludes either single exterior outer mark, including the cubic and either orientation of the endpoint-zero seam.

## 4. A paid stopped sign argument

We give the needed excluded-stop comparison directly, including its exact degree cost. Write a global signed functional as
$$
 \nu(Q)=I_{0,1}(A H P Q)=\sum_{x\in C}\eta_x Q(x)
 \quad(\deg Q\le b),
$$
where the $m$ distinct nodes in $C$ are interior, the live stop $t\in C$ has $P(t)\ne0$, $A>0$ on the open unit interval, and $H$ is a product of one or more right-pole factors $d-X$ with $d\ge1$. Assume $P$ has $k$ simple unit roots giving all its unit sign changes, the true prefix equation $I_{0,t}(A P)=0$ is paid, and
$$
 k+2(m-1)\le b,\qquad
 \deg A+\deg H+\deg P+k+2(m-1)\le19,\qquad \deg P+m-1<19 .
$$
These are the only bounds used in the applications. Then
$$
 \operatorname{sgn}(P(t))\sum_{x<t}\eta_x/H(x)<0.                 \tag{4}
$$
Reflect first for a suffix with left poles. The summation is only over displayed nodes, and no reciprocal is integrated.

To prove this, let $R$ be $(t-X)$ times the product of $r-X$ for unit roots $r>t$ and the doubled factors $(c-X)^2$ for displayed $c>t$. Interpolate $1/(H R)$ at the unit roots below $t$ once and displayed nodes below $t$ twice, giving a Newton polynomial $B$. The knot list is nonempty since the true prefix zero with positive $A$ forces a change on the left. The positive reciprocal divided-step identity
$$
 (d-x)^{-1}-(d-v)^{-1}=(x-v)(d-v)^{-1}(d-x)^{-1}
$$
is preserved by positive sums and products via a difference-of-products expansion. Iterating at the knots, including repeated knots, gives positive Newton coefficients and a remainder equal to the knot product times a positive function below the first pole. This argument is algebraic and works at a repeated knot without any limiting divided difference. Therefore $B(x)>0$ for $x>t$. Put $Q=RB$; its degree is at most $k+2(m-1)$. On $x<t$, the sign of $P( H Q-1)$ away from its zeros is $-\operatorname{sgn}P(t)$: the root factors of the interpolation remainder supply precisely the prefix sign changes and the doubled factors do not affect sign. On $x>t$ the sign of $P H Q$ is the same negative orientation, by the right cut factors and the additional $t-X$. The weak inequalities hold at the zero sites. A strict prefix sample survives because the union of the $P$ zeros and left off-stop nodes cannot cover 19 points. Thus the paid local zero implies $\operatorname{sgn}P(t)\,\nu(Q)<0$. At left nodes $Q=1/H$, and at the stop and right nodes $Q=0$, proving (4). This is the needed half of the generic `FiniteStoppedBracket.strict_bracket_of_pole_grid` argument, independent of any package-external signed-mass assumption.

### Sole inner exterior

Reflect to $a<0$, $u,h,z\in(0,1)$. The outside true word $I_{a,0}(X(X-u)q)=0$ forces a root in $(a,0)$. The unit count $k\ge3$ then forces degree four and exactly three simple unit roots, with the outside root also simple. The end pairs cannot have disjoint windows. Write $q=(X-\alpha)P_3$ with $\alpha\in(a,0)$ and $P_3$ the monic product of the three unit roots. For $W=w(X-a)$ the six global moments give a signed rule for $\nu(Q)=I_{0,1}(WqQ)$ on the three marks $z,h,u$, exact through degree 8 by division by $D=(X-z)(X-h)(X-u)$. If $\ell_x$ is a degree-two cardinal polynomial, then
$$
 \eta_x P_3(x)=I_{0,1}(W(X-\alpha) P_3^2\ell_x^2)>0 .
$$
The test $P_3\ell_x^2$ is paid and the integrand is positive off finitely many zeros on the mesh. Thus each $\eta_x$ has the sign of $q(x)$.

Use the right suffix version of (4), with local weight $1-X$ and left poles $X(X-a)$. At $z$, multiply the profile by $X-e$ for $e=u$ and for $e=h$ in turn. Both true stopped zeros are affine combinations of the right endpoint pair. Such multiplication erases the atom at $e$ exactly, giving two atoms with masses $(x-e)\eta_x$ and law degree 7. The profile has four unit cuts and degree five; the bracket costs $4+2=6$, total integration degree at most $3+5+6=14$ and the strict survivor bound $5+1<19$. Each comparison forces the other atom strictly above $z$, so $z<h,u$. Apply the same comparison at $h$, erasing $z$ with the true right inner zero. It forces $u>h$. With $z<h<u$, the singleton comparisons at $z$ say that $q(h)$ has sign opposite $q(z)$ (erase $u$; both tilt values are negative) and that $q(u)$ has the same sign as $q(z)$ (erase $h$; the tilt values have opposite signs). This proves all the chronology needed for the [uniform one-inner density proof](../one-inner-exterior/PROOF.md), which excludes this actual packet. Both orientations have now been covered, without assuming nonvanishing at a reflected origin.

## 5. The all-interior packets

We now have $e=0$, hence $k\ge2$. If $k=3$ use the [uniform three-change exclusion](three-change/PROOF.md). It uses a positive affine residual after orientation; the closed parameter range includes the constant residual $s=1$ when $q$ is cubic, and the factor $X$ when a quartic's remaining root is an endpoint after reflection. If $k=4$ use the [uniform four-change exclusion](../interior-four-changes/PROOF.md), which includes positive, zero and negative eighth quadrature weights and does not presume separation at parameter-box boundaries.

It remains to check $k=2$. Let $r<s$ be the two odd-multiplicity unit roots (possibly with further even multiplicity). Both end pairs use these same two changes, so $0<z<r<s<u<1$. Let $\sigma$ be the common sign of $q$ on the two unit tails where it is nonzero. Since $a,h$ are interior and $F(a)=F(u)$, $G(h)=G(z)$, neither anchor can be outside the overlap: otherwise its own window or its difference window would have fixed sign. More precisely, if $a>u$ its difference has no sign change; if $a<u$, both $(0,a)$ and $(a,u)$ need a change, forcing $r<a<s$. Similarly $r<h<s$. The active marks $a,h$ have the opposite phase to $z,u$.

To get the strict **crossed** order, suppose $a\le h$. Put $U=X(u-X)$ and $V=(1-X)(X-z)$. On $(z,u)$ both are positive, and
$$
 V/U=(1-z/X)\bigl(1+(1-u)/(u-X)\bigr)
$$
is strictly increasing, as a product of positive strictly increasing factors. The true $a$ inner zero gives $I_{z,a}(U\,\sigma q)<0$ by its positive portion on $(0,z)$. On $(z,a)$ there is one sign change at $r$, from positive to negative for $\sigma q$. The polynomial $(V-(V(r)/U(r))U)\sigma q$ is nonpositive on that interval and strict away from finitely many zeros. Hence $I_{z,a}(V\,\sigma q)<0$. The signs on $(a,h)$ only add a nonpositive contribution, contradicting the true reverse difference. Therefore
$$
                          z<r<h<a<s<u .
$$
This argument is valid even when $q$ has an even-multiplicity root on either tail or at an endpoint. All tests are the original polynomials.

Write $H_2=(X-r)(X-s)$. In degree four with monic $q$, the residual $q/H_2$ is monic quadratic, with constant sign on the unit interval outside its finite zero set. If $\sigma=+1$ it is a monic quadratic $B\ge0$ on the whole closed interval in the real closure; if $\sigma=-1$, set $B=-q/H_2\ge0$. Then $B$ has leading coefficient $-1$ and
$$
 B=w+b_0(1-X)+b_1 X,\qquad b_0=B(0)\ge0,\quad b_1=B(1)\ge0.
$$
In particular it is strictly positive on $(0,1)$, even when either or both endpoint coefficients vanish. In the positive case $B$ may have a double unit root or an endpoint zero, which does not harm strict mesh positivity on squares. In degree at most three the residual has degree at most one; change the overall sign of $q$ if needed to make $q=B H_2$ with $B\ge0$ and positive on the open interval.

In all cases the global law gives the six-node Gaussian rule for $wB$, with nodal product $N H_2$ and nodes $z,r,h,a,s,u$. This follows by division (exact through degree 11) and cardinal squares (strictly positive weights), also if $B$ has isolated zeros. The [crossed negative-tail proof](crossed-interior-negative-tail.md) applies to the negative monic-quartic tail with $b_0,b_1\ge0$, including their zero endpoints. The [crossed positive-tail inequality](crossed-interior-positive-tail.md) applies when $q=B H_2$ with monic quadratic $B\ge0$. Its conclusion is $I_{0,1}(wB H_2)<0$. But the paid left pair gives $I_{0,u}(wq)=0$ and the remaining tail $(u,1)$ is strictly positive in integral. This excludes the positive quartic tail.

### Constant or affine residual: a finite perturbation, not a limit assumption

The same positive-tail inequality suffices for a quadratic or cubic $q$ with $k=2$. We only need to exclude a **strictly positive** mixed moment for the second and fifth nodes of the six-node rule for $wB$, where $B$ is constant or affine, nonnegative and nonzero. Suppose that mixed moment is positive. Set $B_\epsilon=B+\epsilon X^2$. For $\epsilon>0$, $B_\epsilon/\epsilon$ is monic quadratic, nonnegative on $[0,1]$. Its six-node Gaussian polynomial is the same as for $w B_\epsilon$ (positive scaling preserves orthogonality). It exists with six simple unit roots and positive weights by Gram positivity, the sign-fit test of degree five, and division/cardinal squares.

Here is a purely finite justification that a positive $\epsilon$ gives a positive mixed moment, with no root-continuity premise. Let $\beta_1,\ldots,\beta_6$ be the actual ordered $wB$ sites. The mixed moment expression
$$
 I_{0,1}\big(w(B+\epsilon X^2)(X-r')(X-s')\big)
$$
is polynomial in $\epsilon,r',s'$. At $(0,\beta_2,\beta_5)$ it is positive by supposition. For a polynomial $f$ and a fixed point $v$, an explicit finite bound on the unit box is
$$
 |f(v+\Delta)-f(v)|\le C\max_i|\Delta_i|\quad (|\Delta_i|\le1),
$$
where one may take $C$ as the sum over its monomials of the absolute coefficient times the total degree times $\prod_i(1+|v_i|)^{\text{exponent}_i}$, by telescoping each product. Thus for all coordinate changes of size less than $\min(1,f(v)/(2(C+1)))$ the mixed moment stays positive. Choose a positive half-width $\eta$ below that bound, below half each successive node gap, and below the endpoint distances; shrink by another factor of two if needed. The six intervals $(\beta_i-\eta,\beta_i+\eta)$ are disjoint inside $(0,1)$, and the unperturbed monic Gaussian polynomial has opposite nonzero signs at each pair of interval ends.

The coefficients of the perturbed monic Gaussian polynomial are rational functions in $\epsilon$, by its $6\times6$ Gram system; the determinant is nonzero at 0. Clear that denominator at the twelve fixed interval ends. Their nonzero numerator and denominator values at $0$ preserve signs for all sufficiently small $\epsilon>0$ by the same finite polynomial estimate. Choose $\epsilon$ strictly below the minimum of the resulting finitely many positive bounds and the mixed-moment bound, for example half that minimum. The 12 signs then persist, so there is one Gaussian root in each of the six intervals by sign change and degree, and in particular the second/fifth roots make the mixed moment strictly positive. This contradicts the quadratic positive-tail theorem for $B_\epsilon/\epsilon$, whose weights are scaled by a positive constant. Every step takes place in the ordered real closure of the original field; no sequence or Archimedean approximation is needed. Thus in the constant/affine case the mixed moment cannot be positive either. The actual positive tail from the left pair contradicts this.

This exhausts all $k$ and all degrees up to four. The repository lemmas `Moments.natDegree_eq_four_of_full_packet` and `Moments.exterior_count_le_one` may alternatively shortcut the lower-degree or double-exterior reductions in a native integration; the present mathematical proof needs neither as a premise.

## 6. Native connection and scope

The conclusion applies to the exact scalar packet returned by `width24_weak_five_moments_of_ordinary_head` (and hence to the unchanged packet in `width24_weak_five_quartic_remaining`) in the reviewed native ERK16 branch. No additional order condition, positivity of original tableau weights, or substituted numerical clock is used. The signs and tests above close the weak-five scalar branch only. The separate weak-four branch and any unconditional ERK16 stage bound are not asserted.
