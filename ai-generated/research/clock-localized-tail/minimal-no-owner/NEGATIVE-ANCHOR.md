# The final negative anchor: a diagonal law and a prime-degree exclusion

The proof uses the [pointwise final projection](ONE-MARK.md). It concerns balanced order, a minimum canonical early block, zero early output weights, distinct late abscissae and a minimum-width late block. It does not apply to arbitrary SDIRK tableaux.

## 1. A necessary and sufficient law for just the first physical late row

Assume balanced \(p=2m\), \(r=m\), a canonical minimum early cache of cap \(h=m-1\), and a late bank of size \(L(m)\) with distinct true clocks. Work with a real negative diagonal \(\gamma=-g<0\). Set \(\alpha=\gamma\lambda\), with \(\lambda>0\) the chosen actual normalized final early Laguerre root. The relevant common-factor evaluation rank is \(m\) if at least \(m\) of the late sites differ from \(\alpha\); for \(m\ge3\) this holds with distinct late clocks at width \(L(m)\). Let \({\cal L}_m\) be monic shifted Legendre and \(P_m\) standard Legendre with \(P_m(1)=1\). Use monic normalized Laguerre \(W_j=j!(I_0-I)^j1\) in the variable \(Z=X/\gamma\), and ordinary normalized Laguerre \(\mathscr L_j\), so \(W_j=(-1)^j j!\mathscr L_j\) in this variable.

The forced final primitive for any actual \(F\) in the early-null first-excess space is \(JF-(JF)(\alpha){\cal L}_m/{\cal L}_m(\alpha)\). At the first physical late row the strict left side vanishes. Suppose this row is at the negative clock \(x=\gamma z\), \(z>0\). In normalized coordinates, write \(\mathcal K\) for the true normalized first-excess space and \(J_1=I_0-I\). Scaling \(X=\gamma Z\) multiplies each \(J\)-value by the same \(\gamma\) relative to its normalized polynomial. Therefore this row condition is equivalent to
\[
 E_zJ_1|_{\mathcal K}=c\,E_\lambda J_1|_{\mathcal K},
 \qquad
 c=\frac{P_m(1+2gz)}{P_m(1+2g\lambda)}
   =\frac{\mathscr L_m(z)}{\mathscr L_m(\lambda)} .
 \tag{1}
\]
The last ratio is determined by \(W_{m-1}\in\mathcal K\), since \(J_1W_{m-1}=W_m/m\). Its denominator is nonzero by strict interlacing at the chosen root \(\lambda\). The entire linear functional \(E_\lambda J_1|_{\mathcal K}\) is consequently nonzero. If the numerator \(\mathscr L_m(z)=0\), the positive Legendre ratio could not equal it. The Legendre denominator is never zero at a negative physical clock since its roots are interior to \([0,1]\).

If \(z=\lambda\), equation (1) holds for every \(g\), but this does **not** produce a permissible first row at minimum total width. With no earlier late taps, that row has the same literal strict feed \(E_\alpha J D_F\) as the last earlier stage, and the same diagonal. The two stages are identical. Keeping the old one, collecting the two weights and redirecting later taps would violate the ordinary strict SDIRK commutator floor \(L(m-1)+L(m)=m(m+1)/2\) for order \(2m\). The floor also applies after such a merge with a nonzero early weight. Thus only \(z\ne\lambda\) is useful.

For \(z\ne\lambda\), first test the actual source proportionality in (1) with \(c=\mathscr L_m(z)/\mathscr L_m(\lambda)\), which is independent of \(g\). Then a finite negative diagonal exists for this one row **if and only if** \(c\) lies strictly between \(1\) and \((z/\lambda)^m\). It is unique. To see this, put \(A(t)=P_m(1+2t)=\sum_{j=0}^m a_jt^j\), with every \(a_j>0\). The logarithmic derivative \(\phi(t)=t A'(t)/A(t)\) is the mean exponent with weights \(a_j t^j\); its derivative in \(\log t\) is the positive variance, so \(\phi\) grows strictly. Therefore \(A(gz)/A(g\lambda)\) is strictly increasing in \(g>0\) if \(z>\lambda\), and strictly decreasing if \(0<z<\lambda\). Its limits at zero and infinity are \(1\) and \((z/\lambda)^m\). Neither endpoint occurs at a finite positive \(g\). For algebraic \(z,\lambda\), the unique allowed \(g\) is algebraic by cross-multiplication into a nonzero polynomial. If a prescribed magnitude range is required, apply the same monotone comparison at its endpoints (including equality at a positive finite endpoint). This law is sufficient only for the first late strict row's zero on the projected sources. It does not solve any subsequent physical chronological row, the scalar grid, or full order.

## 2. The penultimate actual impulse gives a precise field test

Suppose \(h\ge5\). In normalized coordinates the actual last coefficient impulse is \(P_{h-2}=W_{h-2}-r_{h-2}W_{h-1}\), where \(r_j=W_j(\lambda)/W_{h-1}(\lambda)\). Combining its \(J_1\) value with \(J_1W_h\) shows that any candidate \(z\) for proportionality in (1) is a root of \(W_h\) or
\[
              \xi=(h\lambda-1)/(h-1).
 \tag{2}
\]
Explicitly the combination with coefficients \(1\) on \(J_1P_{h-2}\) and \(1/[h^2(h-1)]\) on \(W_{h+1}\) is \((Z-\xi)W_h(Z)/[h^2(h-1)]\), vanishing at \(\lambda\). This is the normalized finite screen, independently of the Legendre coefficients.

At level \(h-1\), the actual cache has exactly two selected true normalized roots \(u,v\) of \(W_{h-1}\). The penultimate unit copy impulse initially has the form \(W_{h-4}+aW_{h-3}+bW_{h-2}\), zero at both those roots. The final copy leaves those three coordinates untouched and chooses the coefficient of \(W_{h-1}\) to vanish at the actual \(\lambda\). Thus the genuine normalized final propagated impulse is \(P_{h-4}+aP_{h-3}+bP_{h-2}\). On roots of \(W_{h-1}\), the first polynomial before that final copy, divided by \(W_{h-2}\), equals
\[
              (Z-u)(Z-v)/[(h-3)^2(h-2)^2].
\]
Indeed it is a quadratic at those roots by the Laguerre recurrence, has the stated leading coefficient and the two literal zero values. Comparing linear coefficients gives
\[
                    a(h-3)^2=4h-8-(u+v).
 \tag{3}
\]
This uses the true two chosen stage samples, not a choice of a formal variance mode.

At all roots of \(W_h\), the ratio of \(J_1(P_{h-4}+aP_{h-3}+bP_{h-2})\) to \(W_{h-1}\) is a quadratic: the \(W_h\)-terms vanish, and the recurrence expresses \(W_{h-2}/W_{h-1}\) linearly and \(W_{h-3}/W_{h-1}\) quadratically there. Its leading coefficient is \(1/[(h-3)(h-2)^2(h-1)^2]\), and its linear coefficient divided by that one is \(-(4h-4)+a(h-3)(h-2)\). Since \(W_{h+1}/W_{h-1}=-h^2\) at all those same roots, proportionality at another root \(z\ne\lambda\) requires equality of that quadratic at \(z\) and \(\lambda\). Using (3), the exact necessary mirror relation is
\[
                  z+\lambda=\frac{(h-2)(u+v)-4}{h-3}.
 \tag{4}
\]
This is a purely normalized algebraic screen on the actual early choices.

## 3. Prime \(h\): neither additional root nor \(\xi\) can qualify

Assume now that \(h\ge5\) is an odd prime. The normalized monic Laguerre \(W_h\) is Eisenstein at \(h\): its coefficient of \(Z^{h-i}\) is \((-1)^i i!\binom hi^2\), which is \(h^2\)-divisible for \(1\le i<h\), and the constant has valuation one. Its splitting group is transitive, so contains a cycle of order \(h\) through all the roots. This cycle has no fixed value among unordered root-pair sums under any nontrivial power: if a value were fixed, averaging over that cycle would give \(2h\), a rational pair sum. A rational pair sum \(c\) between roots of the irreducible polynomial would make its entire root set invariant by \(Z\mapsto c-Z\) (the affine polynomial has a common root and the same degree). Since the degree is odd, there would be a rational fixed root, contradiction. Thus the orbit in every conjugacy class of such sums decomposes into cycles of size \(h\); the field degree of a root-pair sum is divisible by \(h\). The right side of (4) belongs to the splitting field of the degree-\((h-1)\) polynomial, whose degree divides \((h-1)!\). That degree has no factor \(h\), so (4) is impossible at any other root \(z\ne\lambda\).

For \(\xi\), define
\[
 D_j(Z)= J_1P_j(Z)
           -\frac{J_1P_j(\lambda)}{W_{h+1}(\lambda)}W_{h+1}(Z).
\]
By the last impulse, \(D_{h-2}(\xi)=0\); hence actual proportionality for the penultimate impulse requires \(D_{h-4}(\xi)+aD_{h-3}(\xi)=0\). The coefficient of \(a\) is **nonzero**, with no evaluation of a protected candidate. The recurrence gives the exact expression
\[
 D_{h-3}(\xi)=
  \frac{\xi-\lambda}{(h-2)(h-1)^2}W_{h-1}(\xi)
 +\frac{h(h-1)-(\lambda-h)^2}{h(h-2)^2(h-1)^3}W_h(\xi).
 \tag{5}
\]
For clarity, start with \(J_1P_{h-3}=W_{h-2}/(h-2)-r_{h-3}W_h/h\) and \(W_{h+1}(\lambda)=-h^2W_{h-1}(\lambda)\). Collect \(W_{h-1},W_h\) using the recurrence and \(\xi-2h-1=h(\lambda-2h+1)/(h-1)\). The coefficient of \(W_h\) then simplifies to the displayed one, since the remaining numerator is \((h-1)-(\lambda-2h+1)^2-2(h-1)(\lambda-2h+1)=h(h-1)-(\lambda-h)^2\).

Use the \(h\)-adic valuation with \(v_h(h)=1\), on an algebraic extension of \(\mathbb Q_h\) containing a conjugate of \(\lambda\). Eisenstein gives \(v_h(\lambda)=1/h\). Thus \(\xi\equiv1\bmod h\), \(W_h(\xi)\) is a unit, and the first term in (5) is integral. The numerator of the second term has valuation \(2/h\), because \(v_h(h(h-1))=1\) while \(v_h((\lambda-h)^2)=2/h<1\). Its full valuation is \(2/h-1<0\); it cannot cancel the first term. This proves the necessary coefficient nonvanishing at the actual real algebraic \(\lambda\), by embedding its irreducible root field.

Consequently \(a\in\mathbb Q(\lambda)\). It also belongs to the degree-\((h-1)\) splitting field by (3). The intersection is \(\mathbb Q\): \([\mathbb Q(\lambda):\mathbb Q]=h\) and the other degree divides \((h-1)!\). Thus (3) would give \(u+v\in\mathbb Q\), which is impossible. Indeed the ordinary Laguerre polynomial \(W_n\), \(n=h-1\), is irreducible (the canonical Laguerre irreducibility of Schur), so a rational pair sum would force the whole root set symmetric about its mean \(n\). With leading coefficients \(-n^2,\ n^2(n-1)^2/2,\ -n^2(n-1)^2(n-2)^2/6\), Newton's identities give the first three power sums \(n^2,\ n^2(2n-1),\ n^2(5n^2-6n+2)\). The third central sum about \(n\) is consequently \(n^2(n-1)(n-2)>0\), incompatible with symmetry. This excludes \(\xi\).

There is a useful nonvanishing extension without a composite-degree exclusion claim. For any odd prime \(q\mid h\), all nonleading coefficients of \(W_h\) are \(q\)-divisible from \(i!\binom hi^2\) (for \(i<q\) the binomial contains the factor \(h\)). Hence all \(q\)-adic roots have positive valuation. Their average is \(v_q(h!)/h<1/(q-1)\le1/2\), by the factorial valuation formula. Schur irreducibility gives an embedding of the real root field at some root with \(0<2v_q(\lambda)<v_q(h)\). Then the same (5) has an integral first summand and uniquely negative second valuation \(2v_q(\lambda)-v_q(h)\). Thus a \(\xi\)-candidate at any odd \(h\) forces the same field membership \(a\in\mathbb Q(\lambda)\); at composite \(h\) the needed intersection conclusion and the other-root pair-sum screen are not assumed.

## 4. Scope of the combined result

For odd prime \(h\ge5\), there is **no negative first late clock for any real negative diagonal** in the stated balanced minimum direct architecture. The candidate \(z=\lambda\) was excluded by literal merging and the ordinary floor; §3 excludes every other negative candidate independently of the Legendre ratio. This part does not require \(\lambda\) to be the largest normalized root. The [two-source sign argument](FIRST-CLOCK-SIGN.md) rules out a nonnegative first late abscissa without either a magnitude restriction or an extremal-root assumption. Together the two proofs exclude balanced orders 12 and 16 in the prime-degree family. The separate [prime-interval argument](PRIME-INTERVAL.md) covers balanced orders 18 and 20. The real negative-diagonal argument does not concern unrestricted stage minima, different early donor shapes or nonzero early output, actual late width above \(L(m)\), or a changed diagonal sign.
