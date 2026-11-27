# Forcing one early clock in the regular reflected quartic-pole chart

This is an exact reduction and a family of rational exclusions, **not** a lower bound for arbitrary nine-stage SDIRK7 tableaux. Use [the quartic-pole notation](../strict-sdirk7-quartic-pole/README.md): the integration interval is $[0,2m]$, $P_j$ is its monic shifted Legendre polynomial, $g=P_4+\delta P_3$, and the affine denominator is $W(Y)=Y-h$. The fixed fourth early clock is $c$; the reflected suffix is $1,u,4-u$ with $M=(u-2)^2-2$. Work on the finite affine-pole, seven-distinct-clock, nonvanishing regular branch. This does not treat constant $W$, vanishing $V=g/W$, or degenerate suffix or chronology branches.

The quartic-pole fourth-read equation $Q_g(c)=0$ is independent of $M$. The linear map $Q$ takes the quartic coefficients $a_0,\ldots,a_4$ to the polynomial with coefficients
$$
(11a_0+6a_1+6a_2+12a_3+36a_4,\
 -8a_0-7a_1-12a_2-30a_3-96a_4,\
 a_0+a_1+2a_2+6a_3+24a_4).
$$
Thus $g$ is fixed by $(m,c)$ when $Q_{P_3}(c)\ne0$.

## Deliberately forcing a rational port

Set $q=Y^2-4Y+2-M$, $R_3=(Y-1)q$. The quadratic interpolation polynomial multiplied by $M/2$ is
$$
T_{\mathrm{sc}}=\operatorname{rem}_{R_3}(g)+g(1)q=T_0+MT_1.
$$
This follows by monic division; both quadratics appear literally in `recovery.py`. The nodal polynomial is $\Omega=R_3 S_4$, with $S_4(c)=0$. Write $J_I f(Y)=I_X((f(Y)-f(X))/(Y-X))$. The Gram chart gives $J_I(g)S_4\equiv\lambda WT_{\mathrm{sc}}/R_3\pmod g$ for a scalar $\lambda$. The Legendre Wronskian gives $J_I(g)^{-1}\propto P_3\bmod g$, and monic division gives
$$
T_{\mathrm{sc}}/R_3\equiv g(1)/(Y-1)-(Y+g_3+5)
              \equiv -\bigl((g(Y)-g(1))/(Y-1)+Y+g_3+5\bigr)\pmod g.
$$
The quotients are defined here because $g$ and $R_3$ are coprime. Put
$$
B=\operatorname{rem}_g\!\left[P_3\bigl((g(Y)-g(1))/(Y-1)+Y+g_3+5\bigr)\right],
\qquad A=\operatorname{rem}_g(YB).
$$
Then $S_4=g-g(c)(A-hB)/(A(c)-hB(c))$, since $S_4-g$ has degree below four and vanishes at $c$ after adding $g$. With $P_0=(A(c)g-g(c)A)/(Y-c)$ and $P_1=(B(c)g-g(c)B)/(Y-c)$, forcing an early rational clock $a$ gives
$$
 h=P_0(a)/P_1(a),\qquad M=-T_0(h)/T_1(h).
$$

The two other early clocks split only when the discriminant of the quadratic
$$
 \frac{P_0(Y)P_1(a)-P_1(Y)P_0(a)}{Y-a}
$$
is a square. Its unnormalized discriminant $D_{\rm early}(a)$ has degree at most four in $a$. The suffix splits only if $M+2=N(a)/D(a)$ is square, where $N,D$ are coprime of degree six on the tested fibers. The equivalent square class is $N(a)D(a)$. Two square splittings do not by themselves verify chronology or rooted order.

One can instead force two mirrored early clocks $m\pm t$. Elimination of $h$ gives
$$
P_0(m+t)P_1(m-t)-P_1(m+t)P_0(m-t)=2t(E_0+E_1t^2+E_2t^4).
$$
The literal $E_i$ are in native `mirrored_ports`. This reduces selecting a mirrored early pair to a quadratic in $t^2$ before the remaining checks.

## Whole rational fiber exclusions

In every row below, $(P_0,P_1)$ and $(T_0,T_1)$ are coprime, and **no rational $a$** passes both square tests:

| $m$ | $c$ | Obstruction modulus |
|---:|---:|---:|
| 3 | 4 | 256 |
| 1 | 3 | 19 |
| 3 | 3/4 | 64 |
| 3 | -3/2 | 64 |
| 1/2 | 1/2 | 81 |
| 3/2 | 5/2 | 23 |
| 3/2 | 3/4 | 13 |
| -1/2 | 3/2 | 47 |
| 1 | 1942/1399 | 19 |
| 2 | 0 | 256 |
| 1 | 2 | 9 |

The missing pivots cannot hide a finite $h,M$ because of the coprime checks. The replay retains the signed scalar and the odd-multiplicity polynomial factors, and multiplies by a square to get integral representatives. A removed square factor cannot vanish on the regular branch: the genuine discriminants and denominator are nonzero. Any further prime normalization removes only an even valuation. If $a$ is $\ell$-integral, reduce the integral polynomial directly; otherwise $s=1/a$ lies in $\ell\mathbb Z_{(\ell)}$ and reversing the polynomial is multiplication by an even power of $s$. A rational square that is $\ell$-integral has an $\ell$-integral square root. Thus the empty intersections modulo $\ell^k$ are finite proofs for entire rational fibers, not a height cutoff. For example, $(m,c,a)=(3,4,3)$ yields four distinct rational early clocks $4,3,6,27/7$, but $M+2=6604/1945$ is nonsquare.

Run `PYTHONDONTWRITEBYTECODE=1 python check-fibers.py` with Python-flint 0.8 and SymPy. It reconstructs all 11 modular obstructions, including both primitive homogeneous charts. For the two principal rows $(3,4)$ and $(1,1942/1399)$ it independently matches the coefficients in `RKCert.Research.SDIRKSevenQuarticPort`. That verified stock Lean 4.36.0 module checks forced-port and mirrored-port ring identities, square-class transfer, and the two full finite no-simultaneous-square receipts with kernel `decide`. The rational-chart reduction is proved above, not a native `HasOrder` theorem. No real or ordered-field exclusion is claimed.
