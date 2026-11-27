# Exactly two quadratic-zero rows are impossible in every paid characteristic

Let a ten-stage strict SDIRK tableau of ordinary order at least eight have common nonzero diagonal $\gamma$, and let $g=Ac-c^{\odot2}/2$ with $c=A1$. Over **any field of characteristic greater than seven**, it cannot have exactly two literal zero entries of $g$, at equal or at distinct clocks. The [previous characteristic-zero result](../sdirk-eight-two-zero-line/README.md) already excludes that row count in characteristic zero. This is not a restriction on where the remaining zero-free or three-and-more-zero tableaux may exist, and is not an unconditional ten-stage lower bound.

In the distinct-clock case the relevant branch forces both zero rows live (nonzero output weight) and exactly one silent **off-zero** row. No sign, ordering of the field, reflection assumption, or initial distinctness of the off-zero clock set is imposed. The coefficient-ring corollary is only for a nonzero commutative ring with $8!$ and the common diagonal units and all eight other residuals units: reducing at a maximal ideal preserves the exactly-two-zero pattern and all order identities.

## Saturation, weights and the graph

Use the [prior two-zero argument](../sdirk-eight-two-zero-line/README.md) and [saturated two-sided flags](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md). All rank and structural steps of that argument precede the real sign replay and are algebraic in the paid characteristics. The Hilbert determinants needed have size at most four and support only $2,3,5,7$; the Volterra commutator $M=CA-AC-A^2$ is triangular with unit diagonal entries $-\gamma^2$. With $U=\ker\operatorname{diag}(g)$, the argument at coincident zeros (two identical scalar traces on two supported axes, contradicting clean $F_4$) does not use real ordering. The [zero-clock proof](../sdirk-eight-saturation/README.md) forces both distinct clocks to be roots of the simple shifted $L_4$. The same supported trace and rank comparisons give
$$
 E_2\cap U=0,\qquad \dim(E_3\cap U)=1,\qquad F_4=GE_2,
\quad G=\operatorname{diag}(g).
$$
The alternatives $\dim(E_3\cap U)=0,2$ are excluded by the $L_3$ trace and the complementary Gauss quadratic $r$ exactly as in the prior proof. The two-sided support identity gives a supported reverse $W_2$ line; its forward preimage is
$$
 v=r(c)+\alpha g,\qquad
 r(X)=L_4(X)/[(X-a)(X-b)]
$$
for the chronologically ordered distinct zero clocks $a,b$. The same support identity and weighted low-grade isomorphism force exactly one silent row, not on $U$, so there are exactly seven live off-zero rows. Both zero-row weights are the actual Gaussian masses. This follows by pairing the supported trace with the two degree-three Gaussian cardinals. Gaussian masses are nonzero without positivity: the monic consecutive-polynomial formula gives $\mu_z=h_3/(L_4'(z)L_3(z))$, where $h_3=1/2800$ and all its factors are units at any root in these paid characteristics.

There is no null graph $\alpha=0$ even if the first stage is silent. Otherwise all seven active off-zero rows lie on the two complementary Gauss clocks. Each of those clocks carries its nonzero Gaussian mass. The paid moments $b^\mathsf T G^k\boldsymbol1$ and $b^\mathsf T C G^k\boldsymbol1$ for $1\le k\le3$ separate the two clocks, giving zero first three residual powers at each. If a clock had at most three distinct nonzero residual values, their annihilator in the residual variable would have degree at most three and nonzero constant term. Its weighted evaluation would give that constant times the nonzero clock mass, a contradiction. Thus the two clocks would need at least eight active off-zero rows, not seven. It follows that the live off-zero graph is genuinely $g=-r(c)/\alpha$, including at the terminal row.

## The two ends, with a silent weight

With $J$ the zero-constant primitive and $J^*$ the reverse primitive, the supported reverse row applied to the last zero has exactly its diagonal read. As in the previous proof this gives
$$
 \gamma=(J^*r)(b)/r(b),\qquad
 D=(Jr)(a)-\gamma r(a),\qquad N=(J(Xr))(a)-\gamma a r(a).
$$
If $D=0$, necessarily $N=0$. Otherwise the silent row strictly precedes the first zero, and its literal clock is $d=N/D$. The first zero row is at least physical row 5, since $F_4$ is clean there and the prefix $1,c,c^2,g$ probes give four independent columns in the kernel of its actual commutator row. The last zero is at most row 8: the two independent suffix rows $b^\mathsf T$ and $b^\mathsf T(I-C)$ annihilate the suffix commutator column because $Z_2,Z_3$ are clean on $U$. Their independence follows by reading that zero column before and after $A$ (the $2\times2$ determinant is $-b_j^2(1-b)^2/2\ne0$ for the physical zero index $j$). The commutator column is nonzero by its diagonal; these two independent annihilators force suffix width at least three.

If $D\ne0$, the actual last three rows have live weights. For the $D=N=0$ case admitted by the exact norm check, the finite forward checks force the silent row among the first three, so the actual last three are live as well. Thus we may use the [outer-edge local weighted reverse identities](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md). They involve only the non-silent suffix, not a reflected tableau through the silent row. Normalize that block by its output weights and reverse its order. Its clock is $y=1-c$, and its quadratic residual on every such physical row is $g\,\gamma^2/(2g_{10})$ by the actual pure row $b^\mathsf T G$ proportional to $b^\mathsf T M$. In particular its first three rows obey the same star or arithmetic equations as the forward end. The suffix rank forbids a duplicate first clock among the first two reverse rows, because all scalar words in $A,C$ would then have proportional coordinates there.

Put $\kappa(u)=1+2u-u^2$ and $H(u)=-2+u+4u^2-u^3$. At either physical end with first gap $u$, the star has third gap $2-u$ and residual ratio $\kappa(u)$, while the arithmetic case has third gap $2u$ and strict adjacent tap ratio $2u(3u-2)/H(u)$. The uncleared branch equations never assume this denominator a priori; in characteristic greater than seven a genuine cross-fed row has it nonzero. The front scalar gates for silent row 2, row 3, or later (and the separately included first silent row) are precisely those of the previous packet. For the reverse gate use $r^*(y)=r(1-y)$: at its first two (nonzero-residual) rows the graph fixes the gap by
$$
 (R^*+\gamma^2)u^*=2R^*-\gamma(2\gamma+k^*),
 \qquad R^*=r^*(\gamma),\quad k^*=-2-k
$$
when $k$ is the linear coefficient of $r$. Its third row is either off-zero and pays the graph star/arithmetic gate, or is the last zero row $b$ at actual row 8. The latter must have arithmetic gap $2u^*$ and zero quadratic residual. This finite testing uses only the literal suffix vector spaces.

## Denominator-cleared prime support and geometric coverage

The two live zero clocks are either reflected, $a+b=1$, or are a nonmirror pair. In the mirror case $D$ is identically zero; the ordinary resultant numerator of $N$ has no exceptional prime divisor beyond $19,137$ and the fixed inversion primes below.

For nonmirror pairs work in the degree-eight algebra of the ordered complementary-clock equations
$$
 L_4(a)=0,\qquad b^2-b+a^2-a+2/7=0 .
$$
A primitive generator is $\theta=a+2b$. The literal rational polynomials for $a(\theta),b(\theta)$ and the annihilating degree-eight polynomial are obtained in `pair_field.py`. `check_norms.py` checks their identities in the ordered two-variable quotient, not just on one automatically chosen real pair. The primitive leading coefficient 48020 is a unit at every paid prime. The only extra lost denominator in these coordinate polynomials and the cleared computations is **13**; it is retained as a direct finite exception. The source verifies that all rational coefficient denominators have support in $\{2,3,5,7,13\}$.

Use homogeneous front and rear gate polynomials before taking norms: for example replace $u_d=(N-\gamma D)/(\gamma D)$ in the front star quadratic and arithmetic quintic, and multiply by $(\gamma D)^2$ and $(\gamma D)^5$, respectively. Treat $u_D=2-u$ and $u_D=2u$ by cross multiplication. For the reverse gap use its actual numerator and denominator similarly. This prevents cancellation of a pole in a *different conjugate* from hiding a genuine exceptional prime. Where a gap denominator is zero, its numerator must also be zero, so use the gcd of their two norm numerators. The script verifies that no nonmirror $D=N=0$ exceptional prime is lost, and the gcd of the both-end cleared products has support only in $\{107,137,997,3137\}$ beyond the inverted primes. Norms here are resultant numerators, up to powers of the universally paid leading coefficient. A method in any field, including a nonalgebraic extension, necessarily maps the oriented algebra into that field or its algebraic closure, so it must lie over a prime in the explicit support.

At each exceptional prime the actual four roots are all enumerated in a splitting finite subfield of the algebraic closure. The script asserts four distinct roots before testing all twelve directed pairs. A field admitting a pair has an algebraic copy of that pair in this census; requiring nonvanishing in the splitting extension excludes its image and hence any ambient coefficient field. Remaining algebraic scalar gates are either uniquely determined by a paid pivot or give a separately checked degenerate case. No assumption that $a,b$ belong to the prime field is made:

| Characteristic | Splitting-field degree | Front survivors | After local reverse gate |
|---:|---:|---:|---:|
| 13 | 2 | 0 | 0 |
| 19 | 2 | 1 | 0 |
| 107 | 1 | 0 | 0 |
| 137 | 1 | 2 | 0 |
| 997 | 1 | 1 | 1 |
| 3137 | 1 | 0 | 0 |

## The final F997 chronological obstruction

The sole remaining directed pair is $(a,b)=(89,337)$, with $\gamma=591$ and the silent row at clock 470 in physical position 2. The first and last three physical rows are the two arithmetic phases given in the replay. The actual fourth front gate comes from $A(g-T)$, where $T$ is the quadratic interpolating the three preceding residuals, then dividing out the two earlier graph clocks. It forces the physical fourth clock 562. The fourth reverse gate has exactly its three earlier nonzero-graph roots, since there the interpolation quadratic is the graph itself. A repeated identical pair in a fourth 3-predecessor row would repeat the earlier strict taps by the scalar $1,c,c^2$ Vandermonde and the paid grade-three identities. Full forward/reverse rank forbids it. Thus in this branch the reflected fourth row is zero at clock $b$, in physical row 7. The earlier zero is in row 5 or 6.

The six actual active nonzero-residual clocks known so far are $591,349,562,407,197,984$. Subtract the Gaussian masses at $a,b$ from the scalar integration functional, obtaining $I_0$. With $Q_6(X)$ the product of the six known factors, the one remaining active graph clock $v$ must satisfy $I_0(XQ_6)=v I_0(Q_6)$. This is valid also for a repeated-clock candidate before recovery. The residues are $(I_0(Q_6),I_0(XQ_6))=(572,968)$, forcing $v=922$, distinct. Scalar interpolation then specifies all active weights. Both candidate placements pay all polynomial clock and pure-quadratic moments; they have not earned true RK order.

At each row-5 prefix, take the explicit grade-three vector with coefficients in $1,c,c^2,c^3,g,cg$ supplied in `check_p997.py` and the Lean module. Its five prefix values are $(0,0,0,0,1)$, so its image by the actual triangular tableau must have prefix $(0,0,0,0,\gamma)$. Its pure correction from its scalar primitive is in $F_4=GE_2$, with four known columns. The displayed left annihilators kill all four columns but read respectively 166 and 650 on the required displacement. Thus both actual placements fail, even though their scalar and mixed polynomial moments pass.

Run `python check_norms.py`, `python check_primes.py` and `python check_p997.py` with SymPy 1.14 and Python-flint 0.8. `RKCert.Research.SDIRKEightTwoZeroPaid` kernel-checks the literal stage-five profile and displacement data and proves both linear-system rejections; it also contains the simple scalar mass guard. The field-wide norm and saturation bridge is the exact mathematics and external replay above, not a native end-to-end `HasOrder` theorem.
