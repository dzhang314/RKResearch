# Two arithmetic off-zero thirds are impossible in the paid asymmetric SDIRK8 three-zero graph

Suppose a strict ten-stage SDIRK tableau over a characteristic-zero field or a field of characteristic greater than seven pays all ordinary order-eight rooted tests. The common diagonal is $\gamma\ne0$, with $c=A1$, $g=Ac-c^{\odot2}/2$. There are exactly three physical quadratic zeros at three distinct clocks and a nonzero supported grade-two vector. Work in the already reduced remaining asymmetric chart: its centered trace is $r(y)=y^2+ky+q$, $y=2c-1$, with $k\ne0$, no midpoint zero, all weights live, and all regular pivots as in the [prior reduction](../sdirk-eight-asymmetric-singular-pivots/README.md).

This note rules out **A/A**, the actual chronology with off-zero arithmetic third stages at both ends. It requires no symmetry of the tableau. It does not by itself give an arbitrary ten-stage exclusion.

## 1. Literal arithmetic gap coordinates

For one orientation put $s=2\gamma-1$, $R=s^2+ks+q$, $D=R+4\gamma^2$, and $U=2R-2\gamma(4\gamma-2+k)$. The nonzero second gap $u$ obeys $Du=U$. In the A phase write $H(u)=-2+u+4u^2-u^3$. The nonzero adjacent tap and actual quadratic graph at the off-zero third give
$$D H(u)=2R(3u-2).$$
Using $H(u)-2(3u-2)=-(u-1)^2(u-2)$, this implies $R(u-1)^2(u-2)=4\gamma^2H(u)$. Therefore $u\ne1,2$, since $H(1)=2$ and $H(2)=8$ are paid units. So the inverse gap $t=1/(u-1)$ is finite, nonzero and not 1. Put
$$f(t)=(t+1)(t+2),\qquad a(t)=-2t^2-8t-9+8/(1-t).$$
The same two exact literal equations, dividing only by already guarded factors, give
$$k=2-4\gamma f(t),\qquad R=4\gamma^2 a(t).$$
For the reflected end use inverse gap $z$ and replace $k$ by $-k$, with $q,\gamma$ unaltered. In particular
$$F=f(t)+f(z)\ne0,\quad \gamma=1/F,\quad
k=2(f(z)-f(t))/F.$$
As $k\ne0$, the difference $f(t)-f(z)=(t-z)(t+z+3)$ shows $t-z\ne0$ and $w=t+z+3\ne0$.

The actual forward and reverse normalizers must differ by $2ks$, hence
$$a(t)-a(z)=(f(z)-f(t))(2-F).$$
Equivalently $a(t)+2f(t)-f(t)^2=a(z)+2f(z)-f(z)^2$. Subtract these two rational expressions and divide by the nonzero **literal** $t-z$. The remaining expression is
$$[1-t][1-z](wF+2)=8.$$
The identities $2(1-t)(1-z)=w^2-5w+12-F$ and $(t-z)^2=2F-w^2+1$ now give the paid symmetric projection
$$\begin{gathered}
C(F,w)=(w^2-5w+12-F)(wF+2)-16=0,\\
k^2=4w^2(2F-w^2+1)/F^2,\qquad
q=[-F^2+2w(5-w)F-8(w-1)]/F^2 .
\end{gathered}$$
The last expression follows from the average of the forward and reverse graph normalizers, using the same product constraint. Neither endpoint reflection of the *tableau* nor prime-field gaps were assumed.

## 2. Paid univariate characteristic support

Use the exact signed Cramer cubic and diagonal polynomials in the [asymmetric regular chart](../sdirk-eight-three-zero-169-paid-characteristics/README.md). Substitute the three invariant expressions $\gamma=1/F$, $k^2=X/F^2$, $q=Y/F^2$, with $X,Y$ the above numerators. For the two primitive anchors use the free algebra $\mathbb Z[1/(2\cdot3\cdot5\cdot7)][w,F,\ell]/(\ell^2-X)$, where $\ell=k F$. Both reflected anchor resultants must vanish, so their even and divided-odd components in $\ell$ must both vanish (because $2\ell\ne0$). Compute each anchor from its original cubic $P$ and clean earliest-zero primitive $H(y)$ after clearing by $F^6$ and $F^3$, respectively. No division by a potentially zero fiber coefficient is made in this simultaneous projection.

Take resultants in $F$ of $C$ against the diagonal and the two anchor components. Integer contents are retained. Whenever polynomial factors are removed, the source checks that they are primitive and divide a product of actual nonzero factors: $F,w,X$, the signed leading and constant coefficient guards, and the cleared products of the two graph normalizers, actual gap denominators and gap numerators. The exact $w$ projection polynomials have degrees $38,93,82$ and common primitive factor $(w-1)^{10}$.

* At $w=1$, $C=F(6-F)$ forces $F=6$ since $F\ne0$. At this literal point the exact evaluations of the *original cleared* diagonal and both anchor components have integer numerator gcd 1 after stripping paid primes. Thus this entire common projection fiber is impossible over every paid field.
* At $w\ne1$, divide out the common factor, then take the gcd of the two resultants of the diagonal projection quotient with the anchor projection quotients. All these divisions are exact integer-polynomial divisions. The resulting paid-prime-stripped support is
$$13^4\cdot17\cdot19\cdot29\cdot73^{12}\cdot1193\cdot43627^3.$$
This calculation uses only fixed polynomial determinants; any common root in an algebraic field extension produces the same divisibility even when a modulus drops a coefficient degree.

For each of the seven remaining prime characteristics, the checker independently reduces the original regular A/A bivariate system, computes its full $q$ projection, and tests every irreducible $q$ factor in its splitting extension with the same actual nonzero guards. The precise algorithm is shared with the previous [169-domain census](../sdirk-eight-three-zero-169-paid-characteristics/README.md); here the prime list is justified by the preceding characteristic support, not a range scan. Every surviving univariate fiber gcd is constant. In particular the algebraic-closure check for characteristic 1193 is included, rather than extrapolated from smaller primes.

## Reproduction and Lean scope

Run `python check_projection.py` and `python check_primes.py` with Python-flint 0.8. The finite script reuses the exact basis generator in the sibling 169-domain packet and verifies all seven primes by integer trial division. `RKCert.Research.SDIRKEightTwoArithmeticThirds` proves the inverse-gap sum identity, the singular common fiber implication, and the numeric prime-support factorization. The full chronology reduction and resultant/finite projections are the exact source proof and replay above, not a single native `HasOrder` theorem. Lean/Mathlib 4.36.0 audit attached.
