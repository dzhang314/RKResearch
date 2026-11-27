# The rational one-clock DIRK10 chart has one fourth-power coset

The rational single-dirty-abscissa branch is now closed by the [genus-two argument](dirk-order10-rational-single-clock-genus-two.md). The local and coset cuts below give its starting conditions.

For a rational eleven-stage DIRK method of order ten whose cubic defect is on a **single numerical clock**, the previous [rational cuts](dirk-order10-rational-clock-gates.md) force the invisible one-row, nonshared affine chart. In that chart we now prove that, up to inverting the ratio of the first two nonzero exterior clocks,
\[
 \boxed{\ a/b =3x^4,\qquad 5t-3=27z^4\quad(x,z\in\mathbb Q^\times),\
        (s,t)\equiv(8,8)\pmod{11}\ },
 \qquad s=a+b,\quad t=s/u .
\]
This is an unbounded arithmetic restriction, not an exclusion of the surviving coset. The **necessary split clock system** in this coset has points over every completion of \(\mathbb Q\). These local points are not Runge–Kutta tableaux, and no rational point or rational stage-bound change is proved. Multiple numerical dirty clocks are outside scope.

We use the exact clock system from the previous note: the plane equation \(E(s,t)=0\), the first-three roots \(a,b\) of \(X^2-sX+s^2/(6-t)\), the centered front \(K(k)=0\), and the suffix quotient of \(M Q+\Phi\ell\) by its two front factors. Use \(r,z_0,e,f\) for the four coefficient scalars in \(H=(r+z_0X)D+(e+fX)J\), so that the independent \(z\) in the box is not a coefficient of \(H\). The exact formulas \(f=168-4z_0\) and \(E_0+4B=1/5\) simplify the centered front:
\[
 L_k=(k+4)((k-1)B-1/5),\quad
 y_D=z_0(k+4)-168,\qquad
 w_D=z_0(k+4)/5-168(k-1)B.
\]
All local arguments concern the clock equations after this necessary tableau reduction.

## 1. The four mod-11 residue branches

The former four survivors were \((0,2),(0,6),(8,8),(9,0)\).

At \((0,2)\), work over the 11-adic local ring and put \(s=h\), \(t\equiv2\). By the unit \(E_t(0,2)=-12\),
\[
 t=2-(28/3)h+O(h^2).
\]
The natural front polynomial is \(h^3 K\): it is integral with unit leading coefficient and reduces to \((8/5)(k+4)(k+3)^2\). Thus \(k\) is integral. If \(k\equiv-3\), both \(h^4 y_D,h^4 w_D\) are units, and \(y,w\equiv0\). If \(k\equiv-4\), the derivative of the normalized front is a unit. In fact
\[
 (h^3K)(-4)=h^4\,168(3-t)/(t(3-2t)),
 \qquad k+4=(105/2)h^4+O(h^5).
\]
The exact first terms of \(y_N,y_D,w_N,w_D\) are then \(-32h^{-3},-2688,-336h,-672\). So \(y\) has a pole and \(w\equiv0\). In both cases normalize \(M\) by \(h^4\) and \(Q\) by \(h\); their limits are \(192X\) and the fixed reverse polynomial for the moment vector \((112,8,0,0)\). For the first case the interpolant limit is the linear Taylor term of \(-MQ/\Phi\) at zero; for the second the intercept comes from zero and the slope from infinity. The two suffix limits, up to unit scale, are
\[
 -180X^3+336X^2-196X+35,\qquad
 -168X^3+308X^2-175X+30 .
\]
Neither even has an affine root modulo 11, and both leading coefficients are units. This excludes \((0,2)\).

The other three residues are genuinely possible for split **clock data** over \(\mathbb Q_{11}\). The independent [Hensel replay](check-dirk10-rational-local-11.py) starts at these exact inputs:

| Residue | Fixed rational input | Other early parameter | Front chart |
|---|---|---|---|
| \((0,6)\) | \(s=121\) | \(t\equiv6\) simple for \(E(s,t)\) | \(k\equiv7\) simple |
| \((8,8)\) | \(s=2/3+11\) | \(t\equiv8\) simple | \(k=3+11\kappa,\ \kappa\equiv3\) simple in the rescaled front |
| \((9,0)\) | \(t=88\) | \(s\equiv9\) simple | \(\kappa=tk\equiv10\) simple |

Every nested polynomial is checked at its actual coefficient precision. The replay normalizes or shifts double-root residue discs, and uses the reciprocal chart at a pole. It certifies all ten distinct exterior/terminal positions, all \(M,\Phi\) values used in the clock formulas, both front tap denominators, and the three genuine finite suffix roots. For example, the \((0,6)\) case has two integral suffix roots of residues 4 and 6, and a pole with \(11X\equiv1\); the prefix poles have \(11a,11b\equiv3,8\). Repeated residues in the other rows do not count as collisions: the ball differences exclude zero at higher precision.

## 2. Finite fourth-power census, without a height cap

Put \(R=a/b,\ T=5t-3\). The preceding valuation bounds give
\(v_q(R),v_q(T)\in4\mathbb Z\) at every prime \(q>7\). Therefore choose signed representatives
\[
 (A,D)\in\left\{\pm2^{e_2}3^{e_3}5^{e_5}7^{e_7}:0\le e_i<4\right\}^2
\]
with \(R=A x^4,\ T=D z^4\). This has exactly 262,144 pairs. The [exact class sieve](check-dirk10-rational-cosets.py) is a finite obstruction on **all** representatives, rather than a bounded search of numerators/denominators.

For \(q>7\) we use the multiplicative character \(u\mapsto u^{(q-1)/\gcd(4,q-1)}\) of the normalized unit, which is unchanged by a fourth power. At infinity, \(v_q(t)=-4m\) implies
\[
 t u^4\equiv1/140,\quad
 [R]\in\{[-140],[-1/140]\},\qquad [T]=[1/28],
 \quad u=s/t.
\]
Indeed \(t=4-R-R^{-1}\), so when \(R\) has a pole its normalized unit differs from that of \(t\) by a minus sign, and in the zero branch use the reciprocal. Include the infinity pair classes only if at least one of the two infinity cubics in the previous rational note splits. This is necessary, not asserted sufficient.

In the integral base chart, enumerate \((s,t)\) and all unit \(R\) residues with \(t=4-R-R^{-1}\). If \(5t-3\not\equiv0\), it supplies its own unit class. At a zero of \(5t-3\), the exact shifted early identity gives \((5t-3)/(5s-3)^4\equiv28/9\). The code accepts the early singular denominators conservatively. Else the front has unit leading coefficient, so enumerate \(k\bmod q\). For finite \(y,w\) at which \(\Phi\) is a unit, the divided difference gives the interpolant modulo \(q\), including its derivative when \(y,w\) have the same residue. With one pole, compute the slope from the linear leading term of \(-MQ/\Phi\), and use the value at the finite head. With two genuine poles, divide \(-MQ/\Phi\) into an affine polynomial plus a proper fraction. At a pole \(X=1/U\), the proper part is \(U\) times an integral regular function of \(U\). The divided difference between two poles has a factor \(UV\), so the affine quotient reduces to the true interpolant. A \(0/0\) head, an evaluated \(\Phi\) pole, or the zero reduced numerator is retained rather than used to reject a class.

For every decided nonzero numerator, dividing by \(X-\bar y\) and \(X-\bar w\) at finite heads gives the true reduced suffix after projectivizing any pole factors. A factor \(1-X/y\) at a pole reduces to 1; division is integral from its constant coefficient. A primitive split rational cubic remains a product of nonzero linear or constant factors under reduction, even if the leading degree drops or roots collide. Therefore all remaining affine factors must split. This justifies the conservative finite test without assuming any denominators of the tableau integral.

Use the displayed finite rule at
\[
 11,13,17,19,29,31,37,41,53,61,67,73,79,83,89,97,101,109,113,
 137,149,157,173,181,193.
\]
At 11 the preceding exact boundary cuts are used. The residue and infinity checks leave 66 pairs.

For each \(p=2,3,5,7\), test the coset representatives by the literal early coefficient valuations. Write \(d=-v_p(t)>0\) at a pole. Then \(v_p(R)=\pm d\). With \(R_0\) the normalized unit of \(R\), the leading unit of \(t p^d\) is \(-R_0\) if \(v_p(R)=-d\), or \(-R_0^{-1}\) if \(v_p(R)=d\). Put \(\alpha=v_p(420),\ \beta=v_p(3)\). For \(d\ge21\) the only possible uniquely least terms or least-term tie of \(E\) come from \(420s^4,-3t^3\). To see this, compare \(4e-\alpha\) and \(3d-\beta\), where \(e=-v_p(s)\). The largest secondary denominator degrees are \(e+2d,2e+d,3e\); on either side of \(4e-\alpha=3d-\beta\) each is strictly smaller than the larger leading degree, using \(\alpha\le2,\beta\le1\) and \(d\ge21\). If \(v_p(s)\ge0\), the \(t^3\) term is uniquely least instead. Hence \(4e=3d+\alpha-\beta\), and test the two scaled leading terms modulo \(p\). The test depends only on \(d\bmod4\) and the unit, so \(21,22,23,24\) cover the tail. At \(1\le d\le20\), use the exact coefficient valuations and every possible \(v_p(s)\) between \(-4d-10\) and \(4d+10\). Below this interval the quartic is uniquely least, and above it only the constant-in-\(s\) terms contribute to the minimum, already seen at the upper endpoint. A zero sum among the scaled least terms is necessary. For \(p=2\) the unit fourth-power class is taken modulo 16, so use the exact identity \(p^dt=4p^d-p^dR-p^d/R\) at 2 to transport the class of \(5t-3\), not only its parity. For \(p=5,d=1\) with cancellation \(5t\equiv3\), allow every class of \(T\). In the other pole cases \(T=5t-3\) has its leading unit from \(5t\).

When \(R\) is a \(p\)-unit, the formula for \(T=17-5(R+R^{-1})\) gives its residue directly whenever nonzero. At 2 it is always odd; use its value modulo 16. At 5 it is 2 modulo 5. At 3 the only cancellation is \(R\equiv-1\); from \(T=27-5(R+1)^2/R\) its valuation and scaled residue are \((2,2)\) if \(v_3(R+1)=1\), or \((3,1)\) otherwise. At 7 cancellation means \(R\equiv1\), and \(T=7-5(R-1)^2/R\) has valuation 1 and scaled residue 1. The corresponding finite counts after the primes \(2,3,5,7\) are \(8,8,3,3\), leaving
\[
 (A,D)=(-1,27),(3,27),(27,27).
\]
In particular the local \((9,0)\) mod-11 branch, though split, cannot occur for rational parameters of the chart: there \(T\equiv-3\) is nonsquare modulo 11, incompatible with \(27z^4\) of unit valuation.

## 3. The negative ratio class fails at 29

At \(q=29\), the infinity cubics are nonsplit. The class \((A,D)=(-1,27)\) has normalized characters \((28,17)\); its only finite bases are
\[
 (s,t,R)\equiv(0,6,28),\quad(14,6,28)
 \qquad (14\equiv12/5).
\]
Here the extra singular analyses below close the cases deliberately retained during the conservative class census.

At \(s\equiv0,t\equiv6\), take \(h=s\). The exact early root gives \(t=6-28h^3+77h^4+O(h^5)\); the front limit is \((168/15)(k+2)^2(k+4)\), and \(M\to336-168X\). Normalize the four reverse moments by \(12h^3\); their limit is \((84,0,0,1)\). At the simple root \(k=-4\), the limiting heads are \(2,0\), neither a \(\Phi\) pole at 29. Its suffix reduces from \(308X^3-567X^2+324X-56\), nonsplit.

At \(k\equiv-2\), first \(v_q(k+2)\ge v_q(h)\): otherwise the quadratic term in \(k+2\) from the limiting front is uniquely least compared with the linear coefficient \(O(h)\), constant \(O(h^2)\), and cubic term. Set \(\kappa=(k+2)/h\). The reduced front is the nonzero multiple \((14/5)(8\kappa^2-39\kappa+112)\), and the exact first terms give
\[
 \bar y=\frac{168\kappa-756}{84\kappa-3136},\qquad
 \bar w=\frac{112\kappa/5}{28\kappa-3136/5}.
\]
The two roots modulo 29 are \(10,13\). Both denominators, the difference \(y-w\), and both evaluated \(\Phi\)'s are units. The respective suffixes have ascending residue coefficients \((25,20,8,19),(24,27,27,18)\); each has just one simple affine root, so neither splits.

At \(s\equiv12/5,t\equiv6\), the same smooth branch as in the previous mod-11 note works at 29. With \(\epsilon=t-6\), the exact expansions
\(s=12/5+(93/448)\epsilon+O(\epsilon^2)\) and, for integral \(k\), \(k=-2-\epsilon/12+O(\epsilon^2)\) have unit derivative denominators. In the integral front branch \(y\) has a pole and \(w\) reduces to zero. If \(k\) has a pole, the linear and cubic front terms tie, \(\epsilon k^2\) is a unit, and both \(y,w\) reduce to zero. Using moments normalized by the fourth, the respective suffix limits are
\[
 63X^3-124X^2+76X-14,\qquad
 196X^3-371X^2+220X-40.
\]
Neither has an affine root modulo 29 and both leading coefficients are units. This completes the negative-class exclusion. The two other ratio classes are reciprocals, since \(27/ (1/3)=3^4\). At 11 they have square ratio class; only the \((8,8)\) clock branch remains.

## 4. A remaining global curve, not a local obstruction

Write \(R=3x^4,\ T=27z^4\) after taking the ratio or its inverse. With \(x=m/n\) primitive, \(n>0\), the relation \(RT=17R-5R^2-5\) implies
\[
 \boxed{\ 45m^8+5n^8+B^4=51m^4n^4,\quad B=3mnz\in\mathbb Z.\ }
\]
Here \(B\) is integral because its rational fourth power is an integer. The same small-prime valuation table forces \(v_p(R)=0\) at \(p=2,5,7\), and at 3 allows \(v_3(R)=1,-3\) before imposing \(T=27z^4\). The value \(-3\) would give \(v_3(T)=-3\not\equiv3\pmod4\), so \(v_3(R)=1\). Thus \(m,n\) are units at all four primes. At 2 and 5, \(T\) is a unit; at 7 its only possible zero residue would require \(R\equiv1\), incompatible with \(R=3x^4\) since 3 is a nonsquare modulo 7. At 3, \(v_3(z)=-1\). Therefore \(m,n,B\) are coprime to 210. They are pairwise coprime as well: a prime \(>7\) dividing \(m\) or \(n\) cannot divide \(B\) by the displayed equation and primitivity. This is still only a necessary equation; the early/front/suffix conditions have to hold. Another way to place the obstruction is on the elliptic curve
\[
 Y^2=X(X-21)(X-81),\qquad X=(3z)^4 .
\]
Indeed \(W=5(R-R^{-1})\) satisfies \(W^2=(7-T)(27-T)\), and \(X=3T,\ Y=27z^2 W\) give the displayed cubic. The visible \(t=2/3\) point is \((X,Y)=(1,\pm40)\), already excluded by the exact front. This reduction does not assert a classification of rational points or of fourth-power abscissas on the elliptic curve.

To see why a single-prime analysis of the remaining **clock system** cannot exclude the positive class, take \(s=2/3+h\) at a prime \(q>7\). The simple early equation gives \(t=2/3-252h^3+O(h^4)\), and choose the simple front root \(k=6-(8505/2)h^4+O(h^5)\). For small nonzero \(h\), \(y\) has a pole (\(1/y=2268h^3+O(h^4)\)) and \(w\to1\). Projectivize the suffix by dividing \(M Q+\Phi\ell\) by \((X-w)(1-X/y)\), obtaining \(S_h\). The [tracked exact Laurent replay](check-dirk10-rational-boundary-series.py) gives
\[
\begin{split}
 S_0&=-14336(X-1)^2(7X-6),\\
 \operatorname{disc}(S_h)&=-2^{45}3^3 7^5 h^3+O(h^4),\\
 u-w&=(63/2)h^2+O(h^3),\\
 S_h(w),S_h(u)&=-1354752h^3+O(h^4),\qquad S_h(1)=-32256h^2+O(h^3),\\
 \ell(-e/f)&=-1693440h^4+O(h^5).
\end{split}
\]
The early and front derivatives and the scaled series division denominators are \(q\)-units for \(q>7\). For a sufficiently small \(h=q^{2j}\eta\), choose the unit \(\bar\eta\) to make the leading unit of the discriminant square. Then the discriminant is a nonzero square. A simple root lifts from \(6/7\); factoring it off leaves a quadratic with square discriminant, so all three roots are distinct and in \(\mathbb Q_q\). The three displayed evaluations exclude collisions with \(u,w,1\); limiting positions exclude collisions with \(0,a,b\) and the pole \(y\). At the potentially coincident root of \(M\) near \(6/7\), \(\Phi\) has nonzero limit and \(\ell(-e/f)\ne0\); thus it is not a suffix clock. All other \(M,\Phi\) values have nonzero limiting values, or a leading term at the pole. The prefix quadratic splits near \(a,b=1/6,1/2\); orient its ratio near 3. The local fourth-power classes are automatic near these nonzero \(\mathbb Q_q\) fourth powers by Hensel (near \(R/3=1\) and \(T/27=1/81\)). The real version takes a sufficiently small negative \(h\), so the discriminant is positive and the same guard arguments apply.

At the exceptional primes \(2,3,5,7\), the ball replay supplies explicit positive-class Hensel inputs. At \(2,3,7\) fix \(R=3x^4\) with \(x=13/19,1/2,1/3\) respectively, and solve the early polynomial for \(s\) in its indicated Hensel disc. At 5 fix \(s=2/3+50\) and lift \(t\) and the centered front. The replay verifies all distinctness and pole guards and checks \(T/27\) is a local fourth power. At odd primes unit fourth powers are detected in the residue field by Hensel. At 2 a unit congruent to 1 modulo 16 is a fourth power: solve \(u=(1+8z)^2\) by the simple equation \(z+4z^2=(u-1)/16\), then solve \(1+8z=(1+4w)^2\) by \(w+2w^2=z\).

Thus a failure of local solvability of these **clock equations** is not the right target for the positive coset. A global rational point argument, or new necessary constraints from actual tableau taps beyond this clock system, may still decide the endpoint.

## Verification scope

The [Init-only Lean module](../../lean/RKCert/ReviewedNative/DIRKOrderTenRationalLocalResidues.lean) checks the complete prime-29 negative-class residue inventory and the nonsplit polynomial tests at 11 and 29 in the kernel. Its typed audit succeeded without axioms on 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. Exhaustive global coset filtering, Hensel ball arithmetic and all formal series jets are independently exact Python certificates. The valuation and graded-tableau bridges in this and the earlier note are mathematical, not claimed as a full native \(\mathtt{HasOrder}\) theorem.
