# All repeated clocks are excluded for five strict stages over \(\mathbb Z[1/30]\)

Let \(S=\mathbb Z[1/30]\). A five-stage strict SDIRK tableau of order five over \(S\), if one exists, has five **distinct** physical clocks. This eliminates every repeated-clock chronology, not the distinct-clock case. The six-stage [uniform witness](order-five-paid-six.md) is unchanged.

The order-five equations over \(S\) imply those over \(\mathbb Q\). Apply the archived [normal form](order-five-five-stage-normal-form.md) there: every weight is nonzero, \(D(1)\) holds, the reflected quadratic defect is a nonzero scalar multiple \(\lambda\) of the forward defect, and the first and last clock pairs are each distinct. The rational quadrature floor is four active sites. Consequently any repeat must be **one pair**, all four aggregate weights are nonzero, and the possible chronological pairs are
\[
 (2,3),(3,4),(1,3),(3,5),(1,4),(2,5),(1,5),(2,4).
\]

Reflection here is **only a rational normal-form operation**. Reflect \(A^\star=W^{-1}A^{\mathsf T}W\) in chronological order, where \(W=\operatorname{diag}(\mathbf b)\). Its rational order five follows from the archived criterion. Its clocks and weights, which are all we use, are the reversed and reflected original clocks and the reversed original weights; they belong to \(S\). We do not assume its matrix entries are in \(S\), and do not specialize this matrix at a prime.

## Scalar identities for the four-site chart

Use centered chronological clocks \(t_i=2c_i-1\), so \(t_1=a=2\gamma-1\) and \(t_5=-a\). For a distinct site \(x\) among the four sites \(T\), write
\[
 H_x=I\!\left(\prod_{y\in T\setminus\{x\}}(t-y)\right),\qquad
 \omega_x=\frac{H_x}{\prod_{y\in T\setminus\{x\}}(x-y)}.
\]
Here \(I(t^{2j})=1/(2j+1)\), \(I(t^{2j+1})=0\). These are the unique aggregate weights by interpolation, all nonzero. In particular \(H_x\ne0\) and \(\omega_x\in S\).

Divide the forward quadratic defect by its first entry \(\gamma^2/2\) and call the resulting vector \(\widehat{\mathbf q}\). Its first two entries are \(1,\kappa(t_2)\), and its last two entries, multiplied by \(\lambda\), are \(\kappa(-t_4),1\), where
\[
 \kappa(x)=\frac{1+2x+4ax-2a^2-x^2}{(a+1)^2}.
\]
These two-row formulas follow directly from triangularity over \(\mathbb Q\). All four boundary values are nonzero because \(\sqrt{2}\notin\mathbb Q\). From the three paid defect moments, the aggregate defect mean at site \(x\) is \(\mu_x=\alpha/H_x\) for one \(\alpha\ne0\), by the four-site barycentric null vector. A first-pair singleton determines \(\alpha\), and a last-pair singleton determines \(\lambda\). If a duplicate site \(z\) carries the two actual defect values \(d,e\), the paid defect square gives
\[
 0=\sum_{x\in T}\omega_x\mu_x^2+
        \omega_z(d-\mu_z)(\mu_z-e).                         \tag{1}
\]
Indeed at that site \(q^2=(d+e)q-de\) for either of its two values, even if \(d=e\).

If \(a\ne0\), put \(T=\{a,r,s,-a\}\). The vanishing degree-four hull gives
\[
 rs=h(a)=\frac{5a^2-3}{5(1-3a^2)}.
\]
In particular \(R(a)=3a^2-1\) is a unit of \(S\): it divides \(5a^2-3\) and \(5R(a)-3(5a^2-3)=4\). The gate formulas below are exact rational identities checked by the [replay](verify-order-five-paid-all-repeated-clock-exclusion.py).

### Pairs \((3,4),(2,3),(3,5),(1,3)\)

Up to reflection the first two stages are singletons at \(a,u\); the other two sites are \(v,-a\), irrespective of which site is repeated. Thus \(H_a=\kappa(u)H_u\). This is precisely the first-two-row scalar equation in the [central repeated-clock derivation](order-five-five-stage-repeated-clock.md), together with the same hull equation \(uv=h(a)\). Its two roots for the second clock give either the prohibited equality \(u=a\), or the same functions of \(a\) as in that derivation. The [complete arithmetic exclusion](order-five-paid-central-repeat-exclusion.md) used only these two clock formulas and the **aggregate** weights, not the location of the duplicate or how its weight is split. It therefore excludes all four pairs here.

### Pair \((1,5)\)

Here \(a=0\) and the clocks are \((0,u,v,w,0)\). The hull gives
\(uv+uw+vw=-3/5\), so \(v=(-3/5-uw)/(u+w)\). The denominator is nonzero over \(\mathbb Q\), since \(u+w=0\) would give \(u^2=3/5\). Take \(\alpha=H_u\kappa(u)\), \(\lambda=H_w\kappa(-w)/\alpha\), \(d=1\), and \(e=1/\lambda\) in (1). The left side of its test, with the right side put at zero, is
\[
 -\frac{4(5w^2-3)(u^2-2u-1)(2uw-u+w-2)}
 {3(5u^2-3)(5uw+3)(w^2+2w-1)} .
\]
All factors except the third numerator factor are nonzero: the square-root cases are irrational, and \(5uw+3=-5v(u+w)\ne0\). Hence
\[
 w=\frac{u+2}{2u+1},\qquad v=-\frac{(u+3)(5u+1)}{10(u^2+u+1)}.
\]
Since \(v\in S\), the denominator polynomial \(u^2+u+1\) divides \(147\) in \(S\), by the identity
\[
 (-11u-13)(5u^2+16u+3)+(55u+186)(u^2+u+1)=147 .
\]
Write \(u=m/n\) in lowest terms with \(n>0\). The positive integer \(m^2+mn+n^2\) has no prime factors outside \(2,3,5,7\), with \(7\)-valuation at most two. Primitive residue pairs show it is odd and not divisible by \(5\). If divisible by \(3\), the numerator and denominator are congruent nonzero modulo \(3\), giving valuation exactly one. Thus \(m^2+mn+n^2\in\{1,3,7,21,49,147\}\), and completing the square bounds \(|m|,n\le14\). The exact enumeration leaves six distinct-site candidates with all clocks in \(S\):
\[
 u\in\{4,-13/2,1/2,-2/3,-5/4,-3/8\}.
\]
Each has a forced aggregate weight outside \(S\) (all values checked by the replay).

### Pairs \((2,4),(2,5),(1,4)\)

For \((2,4)\) let the clocks be \((a,r,s,r,-a)\). In (1) take \(\alpha=H_a\), \(\lambda=H_{-a}/H_a\), \(d=\kappa(r)\), \(e=\kappa(-r)/\lambda\). The necessary equation is
\[
 Q_4(a)r^2=P_6(a),\quad
 Q_4=15a^4+30a^3+24a^2+10a+2,\quad
 P_6=15a^6-34a^4-10a^3+22a^2+14a+2.                         \tag{2}
\]
For \((2,5)\), or \((1,4)\) after scalar reflection, use \((a,-a,s,r,-a)\), with \(\alpha=H_a\), \(\lambda=H_r\kappa(-r)/H_a\), \(d=\kappa(-a)\), \(e=1/\lambda\). This gives
\[
 D_5(a)r=-N_6(a),\quad
 D_5=30a^5+45a^4+12a^3-10a^2-6a-1,\quad
 N_6=30a^6+15a^5-46a^4-30a^3+14a^2+13a+2.                  \tag{3}
\]
For clarity, let \(S_\pm=5(3a^2-1)r^2-5a^2\pm4ar+3\). The two square-test expressions in (1) are respectively
\[
 \frac{4S_-(Q_4r^2-P_6)}
 {3(a+1)^4(5(3a^2-1)r^2+5a^2-3)S_+},\quad
 -\frac{4S_-(N_6+D_5r)}
 {3(a+1)^2(3a^2-1)(5a^2-3)(15a^3r-5a^2-5ar+3)(2a^2+4ar+r^2+2r-1)}.
\]
Here \(S_-\) and \(S_+\) are \(-15r(3a^2-1)H_a\) and \(-15r(3a^2-1)H_{-a}\). The remaining variable denominator factors correspond to \(r-s\), \(a+s\), and \(\kappa(-r)\); none vanish by the chart assumptions. Thus neither equation uses a denominator cancellation in positive characteristic.

**Specialization of the scalar data.** Suppose a prime \(p\notin\{2,3,5\}\) divides the numerator of \(a\) in \(S\). Reduce the *clock and weight identities* at \(p\). All clocks now lie in \(\{0,r,s\}\). The degree-three hull \(t(t-r)(t-s)\) and its \(t\)-multiple vanish at all actual stages and have paid integrals. This gives \(r+s=0\) and \(rs=-3/5\), hence \(r^2=3/5\). Equation (2) at \(a=0\) gives \(r^2=1\), excluding every such \(p\) in that branch. Equation (3) gives \(r=2\), so only \(p=17\) can remain in its branch. In \(\mathbb Z_{(17)}\), equation (3) and \(s=h/r\) give \(r+s\equiv17/10\pmod{a}\), since the denominators have unit values at \(a=0\bmod17\). But the aggregate weight \(\omega_a\) is integral at \(17\); its denominator is \(2a(a-r)(a-s)\), so its numerator \(H_a=(a-r-s)/3+a h\) is divisible by \(a\). It follows that \(a\) divides \(17/10\) in \(\mathbb Z_{(17)}\). Thus any extra prime dividing \(a\) occurs only to the first power at \(17\). This applies to the mirrored branch without a reflected matrix specialization.

**Finite diagonal list.** Write \(a=m/n\) in lowest terms. The denominator \(n\) and \(m+n\) are \(2,3,5\)-smooth up to sign, since \(\gamma=(a+1)/2\) is a unit in \(S\). The numerator \(B=3m^2-n^2\) of the unit \(R(a)\) has \(2\)-valuation at most one (odd squares modulo \(8\)), \(3\)-valuation at most one (primitive pair), and no factor \(5\) (3 is not a square modulo 5). Reduction modulo \(3\) and \(8\) gives \(B\in\{-1,2,3,-6\}\). These bounds also imply \(\gamma>0\): \(m<-n\) would give \(3m^2-n^2\ge11\), while \(m=-n\) gives \(\gamma=0\).

The Pell observation used in this finite list is elementary. Every positive solution of \(x^2-3y^2=-2\) has \(x+y\sqrt3=(1+\sqrt3)(2+\sqrt3)^j\), \(j\ge0\). For \(y\ge2\), multiplication by \(2-\sqrt3\) gives \(2x-3y>0,\ 0<2y-x<y\); induction reduces to \(x=y=1\). Set \(k=2j+1\). The coefficient of \(\sqrt3\) in \((1+\sqrt3)^k\) is \(2^j y\); modulo \(3\) it is \(k\). Cubing \(X+Y\sqrt3\) sends this coefficient to \(3Y(X^2+Y^2)\), which increases its \(3\)-valuation by exactly one since \(X^2\equiv1\bmod3\). Thus \(v_3(y)=v_3(k)\). If \(y=3^e\), then \(y\le k\), and the succession \(1,3,11,\ldots\) with growth greater than three after \(y\ge2\) leaves only \(y=1,3\). If \(y=17\cdot3^e\), then \(y\le17k\); the succession \(1,3,11,41,153,571,\ldots\) leaves only \(y=153\), \(x=265\).

First remove the possible \(17\)-factor in (3). With \(17\mid m\), the squares modulo \(17\) and \(B\equiv-n^2\) permit only \(B=-1,2\). For \(B=-1\), the denominator has no factor \(3\) or \(5\), and as above reduction modulo \(8\) gives \(n=1,2\), incompatible with \(17\mid m\ne0\). For \(B=2\), both \(m,n\) are odd, and \(n=5^d\) with \(d\ge1\) (otherwise \(|m|=1\)). The preceding valuation bound and coprimality imply \(|m|=17\cdot3^e\). Taking \(y=|m|\), \(x=n\) in the Pell observation gives \(n=265\), not a power of \(5\). Thus \(a\) is a unit in both (2) and (3).

For unit \(a\), the full list follows from the same four \(B\) cases:
- \(B=-1\): \(n=1,2\) and \(m\ne0\) leave \(a=\pm1/2\).
- \(B=2\): \(n=5^d\). If \(d=0\), the positive diagonal gives \(a=1\); otherwise \(|m|=3^e\), and the Pell observation gives \(|m|=3,n=5\).
- \(B=3\): \(n=3z\), \(m^2-3z^2=1\). Since \(3\nmid m\) and \(5\mid m\) would require \(z^2\equiv3\bmod5\), \(|m|\) is a power of 2. It cannot equal 1, and modulo 8 with \(z\) odd it must equal 2. Hence \(a=\pm2/3\).
- \(B=-6\): \(n=3^d\), since \(n\) is odd and \(5\mid n\) would require \(m^2\equiv3\bmod5\). Now use \(y=3^{d-1}\), \(x=|m|\) in the Pell observation. This gives \(a=\pm1/3\) or \(a=\pm5/9\); \(+5/9\) fails the unit \(m+n\) condition.

Thus \(a\in\{1,\pm1/2,\pm1/3,\pm2/3,\pm3/5,-5/9\}\). Equation (2) has a rational square on this list only at \(a=-2/3,1\); either sign of \(r=1/3\) gives a forbidden aggregate weight. In (3) only \(a=-2/3,-1/2\) give all clocks in \(S\); their aggregate weight at \(a\) is respectively \(93/232\), \(8/19\), both outside \(S\). This completes all chronologies with a repeat.

The remaining [distinct-clock gate](order-five-paid-distinct-clock-gate.md) is a separate open chart, not an inference of unrestricted nonexistence.
