# Gaussian low-active cases with one invisible strict SDIRK8 stage

At ten-stage strict SDIRK8 over a characteristic-zero field, suppose the only physical nonzero quadratic residual is stage one's, and its weight is zero. Use \(\boldsymbol h=(A-\gamma I)\boldsymbol g\) and assume \(B\boldsymbol h=0\). This packet excludes four active stages and five active stages with only four ordinary sites. Combined with the earlier [seven-active](../sdirk-eight-silent-one-row/README.md) and [six-active](../sdirk-eight-silent-one-six/README.md) results, the only remaining undetected single-invisible case has **five active stages at five distinct ordinary sites**. No assertion here about detected cubic defect or multiple invisible stages; the unrestricted bound remains **10–11**.

Use the literal normalized front clocks \(a=A_0\), \(b=B_0\), with time divided by the common nonzero diagonal \(\gamma\). Use \(\boldsymbol h\) scaled by \(\gamma^3\) and strict taps divided by \(\gamma\); common diagonal in these moment reads is one. Write \(p(z)=L_4(\gamma z)\) and \(d(z)=L_3(\gamma z)\), with \(L_j\) the shifted Legendre polynomials. The physical terminal clock \(c_{10}=1-\gamma\) is Gauss in these two cases, so \(\gamma\) is Gauss. The two nonzero-\(h\) literal front zero stages \(2,3\) are silent and give distinct \(a,b\). The only invisible predecessor has \(h=0\), and its incoming strict tap is zero at every active stage because \(h_i=g_1 A_{i1}\).

In either case, physical eight is silent: otherwise the reverse three-clock incidence for the actual normalized trailing three active stages would have all three clocks Gauss, already excluded. An active physical four with \(h=0\) would require the literal normalized cubic \(H_4(c_4/\gamma)=0\) at a Gauss node, impossible by the earlier Gauss replay.

## Five active, four ordinary

The actual active rows are \(5,6,7,9,10\); the physical silent zero besides \(2,3,8\) must be row four. Exactly one active clock is doubled, and there cannot be an extra canceled pair because four ordinary sites are required. The scalar cubic probes make every pure-four read zero at any singleton active clock. If row five were singleton, its clean actual \(Ah\) with the three strict clocks \(a,b,z=c_4/\gamma\) is already excluded by the exact earliest-Gauss test. Thus row five is one of the physical occupants of the doubled clock \(r\). The same test shows the pure-four active rank cannot be zero.

The pure-four rank on all quadratic-zero coordinates is three, whose active kernel now has dimension two. It is spanned by the independent \(\boldsymbol h,C\boldsymbol h\). Since \(p=L_4(\boldsymbol c)\) is zero on all active coordinates, on all quadratic-zero coordinates \(p(c_i/\gamma)=Q(c_i/\gamma)h_i/\gamma^3\) for an affine \(Q\). Its coefficients are determined by the two literal front values. At the actual silent row four, \(Q(z)H_4(z)-p(z)=0\). The true padded roots \(a,b\) divide this quartic exactly and are impossible physically (the unique modified row-four moment system would give a literal duplicate), leaving a monic quadratic. The [unit checks](five_on_four.py) preserve its degree and show \(z-a,z-b,p(z)\) are units. Thus the strict clock interpolation never collides with a Gauss node or a front clock.

At row five the three scalar moments give its strict taps uniquely at \(a,b,z\), from which the normalized actual \((Ah,\tau_4)\) is known. If row six is singleton at another Gauss clock, its four clean moments at \(a,b,z,r\) uniquely give all strict taps, and the resulting \(Ah\) is a unit, contradiction. If row six is the other occupant of \(r\), its strict tap \(\lambda\) to row five is free in the first three scalar moments; the first three taps must then be the actual row-five taps minus \(\lambda\) times the three-cardinal evaluation vector at \(r\). Its \((Ah,\tau_4)\) changes by \(\lambda\) times an explicit direction (the earlier active row five has \(h=0\)). The active pure-four rank is one, so its determinant with row five must remain zero. The determinant of the direction with row five is a unit, forcing \(\lambda=0\). With identical actual clocks, strict feeds, and diagonal, these would be literal duplicate rows. At \(1129,t=203\), there are eight front/diagonal phases, thirty-two duplicate-direction tests and ninety-six singleton tests.

## Four active

All four ordinary sites are Gauss, and each active row is clean through pure degree four because the cubic scalar probes detect all four actual active axes. By the earlier physical census, the active rows are exactly \(6,7,9,10\). The silent prefix after stage one is rows \(2,3,4,5\) at normalized clocks \(a,b,z,v\). Row four cannot repeat \(a,b\) by literal uniqueness. Write \(r=c_6/\gamma\), \(s=c_7/\gamma\), and \(\rho=d(s)/d(r)\). The values \(d(r),d(s)\) are nonzero. Every actual pure degree-five column on the active axes is on the \(d\) line, because the quadratically weighted probe space there has rank three.

### A copied physical prefix clock

If \(v\in\{a,b,z\}\), row six can see just the three strict scalar clocks \(a,b,z\); the clean cubic nodal evaluation gives
\[
 L_r((X-a)(X-b)(X-z))=0,\qquad
 L_y(F)=\int_0^y F(X)\,dX-F(y).
\]
This is a unit-slope linear equation for \(z\). At the fixed actual \(v\), the three scalar reads of physical row five fix its strict feeds at \(a,b,z\) affinely in the normalized \(h_5\), after its stage-one tap \(2h_5\) is removed. Therefore its pure-four row of
\[
 h,\quad Ch,\quad Ah,\quad \tau_4,\quad L_4(\boldsymbol c)
\]
is affine in \(h_5\). For the earlier value of \(h\) at the same physical clock, this formula is exactly the padded actual earlier row. Subtract that padded row from the rank-four test across the first four zero stages. The rank bound three forces \(h_5-h_{\rm old}\) times every derivative minor to vanish. At least one derivative minor is a unit in every orientation, so \(h_5=h_{\rm old}\) and the unique strict taps would make literal twins. The [copy replay](repeated_prefix.py) includes all Gauss first-active positions, both front phases and all three copied placements.

### Four distinct physical silent clocks

Interpolate the normalized four values of \(\boldsymbol h\) at \(a,b,z,v\) by a polynomial \(\mathcal H\) of degree at most three, and let \(D_4(X)=(X-a)(X-b)(X-z)(X-v)\). In row six the strict scalar moments on the silent prefix reproduce \(L_r\) through degree three. In row seven there is one genuine extra strict tap \(\lambda\) into the earlier active row six at \(r\), so its corresponding prefix functional is \(L_s-\lambda\operatorname{ev}_r\) through degree three. Define
\[
 K=L_s-\rho L_r-\lambda\operatorname{ev}_r .
\]
The active pure-four read \(Ah=0\) gives \(L_r(\mathcal H)=0\), \(L_s(\mathcal H)-\lambda\mathcal H(r)=0\), hence \(K(\mathcal H)=0\). The degree-five pure scalar clock residual \(\tau_5\) gives \(K(D_4)=0\): its values at rows six/seven are \(-L_r(D_4)\) and \(-L_s(D_4)+\lambda D_4(r)\), using the interpolation of \(X^4\) at the four silent clocks. The pure grade-five read \(ACh\) uses \(X\mathcal H\) modulo \(D_4\), and hence \(K(X\mathcal H)=0\). Subtracting \(r K(\mathcal H)\) removes the only genuine added tap:
\[
 (L_s-\rho L_r)((X-r)\mathcal H)=0 .
\]
This derivation remains valid if an active Gauss clock happens to equal a silent clock; the only distinctness needed in the interpolation is among the four physical silent clocks.

Together with \(\mathcal H(a)=h_a\), \(\mathcal H(b)=h_b\), and \(L_r(\mathcal H)=0\), the marked equation gives a \(4\times4\) unit solve for \(\mathcal H\), independent of the two unknown silent clocks. Then \(\lambda=L_s(\mathcal H)/\mathcal H(r)\) with unit denominator. Since \(H_4(z)=\mathcal H(z)\), the true difference \(H_4-\mathcal H\) has the two exact padded roots \(a,b\); the remaining factor is unit-slope linear, determining \(z\). Now \(K(D_4)=0\) is unit-slope linear in \(v\), determining the next silent clock and its \(h_5=\mathcal H(v)\). The true row-four and row-five strict taps are fixed by the three actual moments and these known \(h\)'s. The rank of the literal pure-four matrix \((h,Ch,Ah,\tau_4,L_4)\) on rows \(2,3,4,5\) must be at most three, yet at least one \(4\times4\) minor is a unit. At \((1129,926)\) all the pivots and a final rank minor succeed in all 48 literal orientations. [Replay](distinct_prefix.py).

## Replay and lift

Run `python3 check_low.py` with `sympy==1.14.0` and `python-flint==0.9.0`, together with the earlier sibling chart files. This is a fixed-monically-based reduction, not a search over \(\mathbb F_p\) tableaux. The Gauss algebra is obtained by its monic quartic, then the monic factors for ordered distinct sites after adjoining and dividing out earlier simple roots and \(1-\gamma\) as appropriate. The prime splits all these roots; the two choices of \(t\) name reductions of \(t^2=1/2\) in that same algebraic coefficient field. The 48 distinct-prefix cases have no skipped zero pivots. The copied-prefix linear pivot and five-active additional monic quadratic are checked in the same finite bases. Multiplication units and the final rank obstructions lift over characteristic zero without requiring the hypothetical tableau itself to reduce.

The [native receipt](../../lean/RKCert/ReviewedNative/SDIRK8SilentGaussianPrefix.lean) proves the ring-valued marked elimination and the guarded duplicate tap identity. They compiled in Lean/Mathlib 4.36.0 with standard axioms. The finite orientation and bridge from stage saturation are source-level proofs, not a single end-to-end Lean theorem.

In the last undetected five-distinct branch, the [two scoped cuts](../sdirk-eight-silent-one-five-cuts/README.md) exclude both extra silent cubic defects vanishing, or a vanishing reverse quadratic factor with an active eighth stage.
