# A doubled triple cannot oppose a genuine two-singleton star

Assume a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, every quadratic residual nonzero, exactly seven different clock labels, and a genuinely quadratic singleton graph \(R\). Type D denotes a doubled clock, S a singleton. The actual endpoint labels are D. Orient a D,D,D prefix forward, and assume the other orientation is D,S,S with a **literal star**, meaning the third has zero tap from its second. This packet rejects that shape, allowing signed weights and both shared and distinct endpoint labels. It does not yet reject D,D,D opposite D,S,S in arithmetic.

## Exact two surviving shape fields

Normalize to common diagonal one, let \(\ell=1/\gamma=2m\), \(h=m-1\), and use centered \(t=x-m\). The two D endpoint labels are \(-h,h\), sharing their clock only for \(h=0\). By the [odd projection](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md), \(Q/B=L_3-\mu t L_4\), \(\mu\ne0\). Use the [actual D,D,D mesh census](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md). A true star equates the two singleton residuals, so in its own clock the graph has axis \(x'=2\). In original centered coordinates the graph axis is \(c=m-2=h-1\).

For \(h\ne0\), if the third D label besides \(\pm h\) is zero, the graph is even, so \(c=0\), \(h=1\). This is the midpoint forward arithmetic phase: a forward star with central D would require \(h=2/3\). The even graph has \(W=t^2-156/49\) at \(m=2\), as checked in the endpoint star packet. If the third D label \(d\) is nonzero, the other two \(Q\)-roots are \(0,-d\), so \(c=-d/2\) and \(d=2-2h\). A nonmidpoint forward arithmetic requires \(d=3h\), hence \(h=2/5,m=7/5,d=6/5\); its squared-root polynomial \(35h^2d^2-21m^2(h^2+d^2)+15m^4\) is \(-21/125\), not zero. A forward star requires \(d=2-3h\), forcing the forbidden \(h=0\).

For \(h=0\), the D clocks are \(0,u,w\) in actual forward order. The two nonzero D labels cannot be opposite in either true forward phase. Therefore the graph roots are \(-u,-w\). The reverse star axis \(c=-1\) requires \(u+w=2\); forward arithmetic \(w=2u\) would give \(u=2/3\), an illegal nonzero-tap gap. Thus the forward is star \(w=2-u\). Set \(Y=(u-1)^2\); the paired squared-root condition gives the irreducible
\[
 35Y^2-112Y+8=0.
\]
Then \(P=t((t-1)^2-Y)\), \(W=(t+1)^2-Y\), with \(R=rW\). There is no missing repeated/Hermite projection: choosing the two later D roots in either true phase gives two different squares, and the distinct-even option fixes the separate nonzero square \(156/49\). All graph data in the shared case depend only on \(Y\), so no choice of \(\sqrt Y\) is needed.

## Star pair and normalized trace

The three known forward D residuals give the degree-two interpolant \(T=g_{\rm f}\) on those labels, and \(A_0\) interpolates \(L_4/g_{\rm f}\). These are rationally determined even if the two noncentral D labels are in a quadratic extension. For the distinct midpoint they are immediate from \(g_{\rm f}=(1/2,1,3/2)\) at \(t=(-1,0,1)\). In the shared forward star \(T=1-(t-1)^2/2\), and \(A_0\) is quadratic with \(A_0(0)=2L_4(0)\) and remainder \(2L_4/(2-Y)\) at the two other D labels. The check verifies the inverse read \((A_0T-L_4)\bmod P=0\). The terminal shared product gives \(\beta_0=B\lambda=-L_4(h)/(g_{\rm f}(h)/2)\), where \(\lambda\) is the nonzero reverse-to-original scale. Hence \(A_2=A_0-\beta_0 T/\lambda\).

For the reverse star gap \(v\), let \(X=(v-1)^2\). The two true singleton labels are \(t=c\pm\sqrt X\), so \(X\ne0,1,2\) by its literal gap and nonzero residue guards. Write \(W=(t-c)^2-S\) in either shape, where \(S=156/49\) or \(Y\); \(X\ne S\) because those singleton residuals are nonzero. Both reverse normalized values are \(\tau=(2-X)/2\), so \(r/\lambda=\tau/(X-S)\). With \(\nu=r/\lambda\), the [literal singleton shape](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md) is
\[
 H=L_4+\beta_0\nu W T-\lambda\nu W(A_0+\beta_0\nu W).
\]
Reduce modulo \((t-c)^2-X\); at that pair \(\nu W=\tau\). Its two coefficient equations are therefore affine in \(\lambda\) with polynomial entries in \(X\). The exact [normalized quadratic trace](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md) gives the third affine condition
\[
 (2-X)\,\mathcal T(A_0)\lambda+
          2c_{\rm tr}(X-S)-(2-X)\beta_0\mathcal T(T)=0.
\]
Here \(c_{\rm tr}/r+\mathcal T(A_2)=0\) is the trace with interval factor \(\ell\). The check computes the sums of \(A_2/L_4\) using quotient traces in the two- and three-dimensional quotients; the coefficient of \(t^7\) modulo \(L_4^2\) gives the weighted inverse sum as before. It explicitly checks graph squarefreeness before using \(W'\).

The two root-pair rows and this trace row require all \(2\times2\) minors of the augmented two-column array to vanish. For both fields, their exact gcd is one after removing factors of \(X(X-1)(X-2)(X-S)\), all literal guards. This treats vanishing affine coefficients without division. Thus every D,D,D opposite a genuine D,S,S star is excluded. There is no outcome claim for other quadratic prefixes.

Run `python check_reverse_star.py` with SymPy 1.14 and python-flint 0.8. This packet uses the earlier staged scalar Lean modules and adds no new native build or end-to-end formalization.
