# Crossed negative tail: an exact incompatible pair of root bounds

This is the negative-tail part of the [complete weak-five scalar proof](PROOF.md). The oriented actual data are
$$
 0<z<r<h<a<s<u<1,\qquad
 q=-B(X-r)(X-s),\qquad B=w+b_0(1-X)+b_1X,\quad b_0,b_1\ge0,
 \quad w=X(1-X).
$$
Both endpoint coefficients may be zero; even in that case $B>0$ on $(0,1)$. The argument needs the actual globals and the end pairs, not the two inner words again after the crossed order is known. Use formal polynomial integrals over an ordered real closure. The positive 19-site rule in [check_references.py](check_references.py) justifies every positivity comparison below, and the same checker verifies the small rational reference identities.

## The exact rules and a finite comparison

Put $\beta=wB$ and $H=(X-r)(X-s)$. The global words make the monic product $NH$ orthogonal through degree five for $\beta$. Division gives its six-node rule on $z,r,h,a,s,u$ exact through degree eleven. The weights are strictly positive by evaluating the squared degree-five cardinal polynomials and applying the positive interval rule. The same construction applies to any of the reference positive polynomial weights below: Gram positivity gives the monic orthogonal polynomial in degree six, a sign-fit of degree at most five would contradict orthogonality unless it has six distinct simple unit roots, and then division and cardinal squares give the positive rule. The actual left pair independently says $I_{0,u}(X B H R)=0$ for every affine $R$.

If positive polynomial weights $W_0,W_1$ have ratio $f=W_1/W_0$ nondecreasing on the sample interval and the threshold $d$ is interior, then
$$
 I(W_1(X-d)P^2)\ \ge\ f(d)I(W_0(X-d)P^2).
$$
This follows by multiplying the sign of $(X-d)(f(X)-f(d))$ at the finite samples; each side integrated is polynomial. Reverse the comparison if $f$ is nonincreasing. The same reasoning holds for a polynomial coordinate $\tau$ and a ratio monotone as a function of $\tau$, even when $\tau$ is not globally monotone in $X$.

For an exact positive rule, strict positivity of a localizer $(X-d)$ on a $j$-dimensional subspace of polynomials of degree at most five forces at least $j$ nodes above $d$. Otherwise a nonzero vector of the subspace vanishes at every above-cut node, whereupon all remaining terms are nonpositive. Conversely the cardinal span of $j$ nodes above $d$ is such a subspace. The analogous statements hold for the negative sign and below-cut nodes. The same rank argument holds on the three-node rule in $\tau$ with degree-at-most-two polynomials. All localizer integrands used with six nodes have degree at most eleven before multiplication by the weight.

## The second global node lies below $1/4$

Reflect through $X\mapsto1-X$ if necessary so that $b_0\ge b_1$, swapping the two end pairs and preserving the crossed order with reflected roots. Set $c=(b_0+b_1)/2$, $\varepsilon=(b_0-b_1)/2\ge0$, and $\beta_{\mathrm{sym}}=w(w+c)$. The ratio
$$
 \frac{\beta}{\beta_{\mathrm{sym}}}=1+\varepsilon\,\frac{1-2X}{w+c}
$$
is nonincreasing on $(0,1)$. For $y=2X-1$ the nonconstant factor is a positive multiple of $-y/(A-y^2)$ with $A=1+4c\ge1$. For $y_2>y_1$ in $(-1,1)$, the difference of $y/(A-y^2)$ has positive numerator $(y_2-y_1)(A+y_1y_2)$ over positive denominators.

To find two below-cut nodes for $\beta_{\mathrm{sym}}$, use $\tau=(2X-1)^2$. The symmetric six-node rule has three reflected pairs, since its monic nodal polynomial is unique, invariant under reflection, and has simple roots (a midpoint zero of an even polynomial would not be simple). Folding each pair gives a positive three-node rule in $\tau$ exact through degree five. For the reference weight $w^2$, the corresponding monic degree-three orthogonal polynomial in $\tau$ has numerator
$$
 R_3(\tau)=143\tau^3-143\tau^2+33\tau-1 .
$$
This is verified by the centered even moments $16/[(2j+1)(2j+3)(2j+5)]$ for $(1-y^2)^2\,dy$. Its signs at $0,1/4,1/2,1$ follow from values $-1,35/64,-19/8,32$. Hence there are two reference $\tau$ nodes above $1/4$. Their cardinal span has strictly positive $\tau-1/4$ localizer. Since $\beta_{\mathrm{sym}}/w^2=1+4c/(1-\tau)$ is nondecreasing in $\tau$, that two-dimensional subspace stays strictly positive. Thus $\beta_{\mathrm{sym}}$ has two reflected pairs with $\tau>1/4$, and in particular two $X<1/4$ nodes. Finally transfer the strictly negative cardinal span of these two nodes from $\beta_{\mathrm{sym}}$ to $\beta$ at threshold $X=1/4$ by the nonincreasing ratio. The second actual node is $r$, so
$$
                               r<1/4.                         \tag{1}
$$

## The last global node lies above $7/8$

Use $\beta_L=w(1-X)$. The ratio $\beta/\beta_L=B/(1-X)=X+b_0+b_1X/(1-X)$ is strictly increasing. It suffices to find one reference $\beta_L$ node above $7/8$ and transfer its positive cardinal line at that threshold.

Reflect to the reference weight $Xw$. Let $P_6,P_7$ be the monic $w$ orthogonal polynomials, with centered formulas $P_n(X)=A_n(2X-1)/(2^n A_{n,n})$, where
$$
 A_6(y)=429y^6-495y^4+135y^2-5,\qquad
 A_7(y)=715y^7-1001y^5+385y^3-35y .
$$
Their orthogonality follows from the even moments $4/[(j+1)(j+3)]$ for $1-y^2$ and zero odd moments. At $0$, $P_6(0)=1/429$, $P_7(0)=-1/1430$. The monic polynomial for $Xw$ in degree six is
$$
 \frac{P_7+(3/10)P_6}{X},
$$
since the numerator vanishes at 0 and is orthogonal to every degree-at-most-five test against $w$. At $X=1/8$, $y=-3/4$, the numerator is $(A_7+A_6)/(715\cdot2^7)<0$: $A_7(-3/4)+A_6(-3/4)=-55733/(4\cdot4096)$. The monic orthogonal polynomial for $Xw$ is positive at zero because its six roots are interior. Hence a root lies below $1/8$; reflection gives a $\beta_L$ node above $7/8$. The ratio comparison yields
$$
                               u>7/8.                         \tag{2}
$$

## The actual left pair forces $r>1/4$

For affine polynomials on $[0,7/8]$, the weight $w$ has a positive definite localizer at $1/4$. To verify this, substitute $X=(7/8)Y$. After removing the positive factor $(7/8)^2$, in basis $1,Y$ the matrix is
$$
 \begin{pmatrix} 37/768 & 71/1920 \\ 71/1920 & 11/384 \end{pmatrix},
 \qquad \det=93/7372800>0 .
$$
The entry with exponent $j\in\{0,1,2\}$ is $-1/[4(j+2)]+35/[32(j+3)]-49/[64(j+4)]$. Extending the interval to $u>7/8$ adds a nonnegative form, since $X-1/4>0$ on the added piece. The ratio $(XB)/w=B/(1-X)$ was just shown strictly increasing. Applying the comparison at $1/4$ on $(0,u)$ gives
$$
 I_{0,u}\big(XB(X-1/4)(X-s)^2\big)>0 .
$$
But
$$
 (X-1/4)(X-s)^2-(r-1/4)(X-s)^2=H(X-s),
$$
and the actual left pair pays the integral of $XB$ times the right side. Since $I_{0,u}(XB(X-s)^2)>0$, the preceding strict sign implies $r>1/4$, contradicting (1).

All numerator degrees are within the fixed positive grid budget: the six-node localizers cost at most 11 before the weight and at most 15 after it; the folded $\tau$ tests have degree at most 10 in $X$ before their weight; Gaussian existence and signs fit the same budget. Every ratio was used in a pointwise comparison, not a rational integral. No nonzero endpoint $q$-value or positivity of any RK tableau weight is needed.
