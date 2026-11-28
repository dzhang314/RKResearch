# The nonzero-mass mixed calibration overlap cannot have one crossing pair

**Scope.** In the [nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md), suppose the two front calibrations have a mixed overlap \(a=e\) or \(h=d\), and exactly one ordinary pair meets both fronts. This excludes that chart over any characteristic-zero field. Together with the [two-cross exit](ERK11-MIXED-OVERLAP-TWO-CROSS-EXIT.md), it excludes both mixed overlaps in this atlas. It does not exclude the half-half overlap, four distinct calibrations, the six-active-pair branch, or 17-stage ERK11 generally. No reverse order eleven is assumed.

## 1. Exact one-cross chronology

As in the two-cross proof it suffices to work with \(a=e\), using reflection only on the polynomial equations. Then \(b=2-2a\), \(d=2a-1\), and \(h=a/2\). The unique triple is at \(a\), containing the two left plateau rows and the right half-plateau. The remaining three uncalibrated roots of the monic cubic cofactor \(Q\) are now labelled \(t,u,v\), with \(t\) the unique crossing pair. The left extras are \(\{t,u\}\) and the right extras \(\{t,v\}\). There are no other roles for these roots, since each front has two extras among the same three labels. The three inner physical rows 8,9,10 are the missing partner of \(h\), the missing partner of \(u\), and the missing partner of \(v\), in some order. There are two choices of the left sixth clock, two of the reflected sixth clock, and six inner permutations, for 24 chronologies. We need no order of field elements.

The exact clock-only first contact \(\Psi\) is the pair of physical rows 7 and 11 in the inverse anchored Gram:
\[
 \Psi=\ell_0r_0+T_4(a)\ell_1r_0+T_4(b)\ell_0r_1+
                  U_{4,4}(a,b)\ell_1r_1=0 ,
\]
with \(\ell_0=(a-t)(a-u),\ \ell_1=-tu,\ r_0=(t-d)(v-d),\
r_1=-(1-t)(1-v)\). The two small Gram coefficient arrays are in the eight-clock note.

## 2. A second, independent physical contact

Use \(z,x\) for the left sixth and seventh clocks, with \(\{z,x\}=\{t,u\}\), and \(w\) for the eighth clock. For a left model \(P\in X K[X]_{\le4}\) put
\[
 \begin{split}
 P_a(X)&=J[X^2(X-a)^2],\\
 D_y(P)&=a^5P(y)-30P(a)P_a(y),\\
 \Phi_L(P)&=(a-x)(a-z)P'(0)-xzP'(a).
 \end{split}
\]
The actual row 7 is a nonzero multiple of \(\Phi_L\), by the derivative-contact proof. Subtracting \(P(a)P_a/P_a(a)\) from \(P\) changes neither actual row 7 nor row 8, since the literal primitive of \(V_a\) vanishes through 8. At any noncarrier the adjusted model vanishes at the plateau and its anchored response correction is quadratic, \(T(C)F\), with \(T(a)=0\). Its values at \(h,z\) are \(-D_h(P)/(a^5F(h)), -D_z(P)/(a^5F(z))\). These are fixed by actual zero reads, with \(F(y)=y^2(a-y)/a\) at those calibrated clocks.

Define a denominator-cleared functional on the same models:
\[
 \begin{split}
 E_w(P)=(w-a)\big[&
  (w-h)(h-a)h^2(a-h)D_z(P)\\
   &-(w-z)(z-a)z^2(a-z)D_h(P)\big].
 \end{split}
\]
This equals \(T(w)\) times \(a^6(h-a)(z-a)(h-z)F(h)F(z)\), a nonzero factor. Indeed, write the quadratic interpolation on \(h,a,z\), with value zero at \(a\), and multiply by that denominator. The row-8 functional is therefore in \(\operatorname{span}\{D_w,E_w\}\); this does not require any calibration of its actual response \(F_8\). Define the reflected \(\Phi_R,D^R_{w'},E^R_{w'}\) at physical rows 11 and 10 in the clock \(Y=1-X\), using \(b\), reflected sixth/seventh clocks and \(w'=1-c_{10}\). The monomial bases are \(X^{i+1}\) and \((1-X)X^j\), so the latter uses the local forms \(Y(1-Y)^j\). The common middle inverse Gram pairs any distinct physical indices to zero; write \(\langle\ ,\ \rangle\) for its scaled pairing, with the factor 210 suppressed.

* If \(w=h\) or \(w=u\), there is an earlier occurrence \(i\) of this clock on the left, in row 3, 6 or 7. The ordinary pair responses \(F_i,F_8\) are different, because \(\mu_w\ne0\) and the first pool is zero. Both readings on the adjusted \(P\) have the form \(D_w(P)/a^5+F_iT(w)\) or \(D_w(P)/a^5+F_8T(w)\), respectively. Thus \(D_w\) lies in the span of actual rows 7 and 8, using the combination \(a^5(F_iL_8-F_8L_i)/(F_i-F_8)\); rows 3 and 6 are zero on all anchored lifts. Consequently \(\langle D_w,\Phi_R\rangle=0\). This covers 16 of the 24 chronologies.
* Otherwise \(w=v\). Consider the 3-by-3 matrix of pairings of \((\Phi_L,D_w,E_w)\) with \((\Phi_R,D^R_{w'},E^R_{w'})\). Its determinant must vanish. Otherwise the pairing of the two three-dimensional spans would be nondegenerate, whereas the two independent actual rows 7 and 8 on the left are orthogonal to the two independent actual rows 10 and 11 on the right. Two dimensions cannot lie in the annihilator of two dimensions in a nondegenerate three-dimensional pairing. Actual independence is from the invertible five-row read matrices. This covers the other eight chronologies without requiring a particular response slope or any additional pivot.

Call the scalar of the relevant case \(\Omega\). Both \(\Psi\) and \(\Omega\) are polynomial in the clocks with rational coefficients, regardless of coincident clocks in any later modular algebra. Only their deduction from a tableau uses the actual literal nonzero guards.

## 3. Finite free algebra and exact unit obstruction

Use the same \(D\), \(M=66D\ne0\), and integer cubic numerators \(r_0,r_1,r_2\) as in the two-cross proof: \(q_i=r_i/M\) for \(Q=X^3+q_2X^2+q_1X+q_0\). Exact arithmetic first constructs a polynomial \(N(a)\) of degree 108 as follows. Over \(\mathbb Z[a]\) use the monic cubic of \(T=Mt\),
\[
 T^3+r_2T^2+M r_1T+M^2r_0=0.
\]
For \(U=Mu\) the monic quadratic has root sum \(S=-r_2-T\) and product \(P=M r_1+T(r_2+T)\), with \(Mv=S-U\). The scaled contact \(M^4\Psi\) in this quadratic tower is \(A+B U\). Its quadratic norm is \(A^2+SAB+P B^2\), and taking the cubic norm gives the exact polynomial of degree 264. It divides exactly by \(a^6(a-1)^6D^{16}\) to a nonzero integer content times \(N(a)\), where \(N\) is taken primitive. These operations are recorded without floating point or a factorization assumption. On an actual chart \(a\ne0\), \(a\ne1\) (because \(b\ne0\)), and \(D\ne0\) by the moment pivot. Since evaluation at the actual roots annihilates the contact, it also makes the norm zero. Thus \(N(a)=0\).

Reduce this coefficient system modulo 101, not the unknown real or characteristic-zero tableau. The leading coefficient of \(N\) is a unit, so a scalar parameter algebra with \(N(a)=0\) is finite free of rank 108 after making \(N\) monic. In its mod-101 specialization the element \(M\) is a unit by Euclidean coprimality with the monic modulus. Thus multiplication by \(M\) has a unit determinant also over \(\mathbb Z_{(101)}\), and all coefficients of the **unscaled** monic cubic \(Q\) are defined over this localized integer parameter ring. Adjoin unscaled \(t\) by \(Q\), then \(u\) by its monic quadratic with \(s=-q_2-t,\ p=q_1+t(q_2+t)\), and put \(v=s-u\). This gives a fixed basis of rank \(108\cdot3\cdot2=648\) over \(\mathbb Z_{(101)}\).

The self-contained exact replay checks the following directly in \(\mathbb F_{101}[a]/(\overline N)\):
1. Write the unscaled first contact as \(A(t)+B(t)u\) and reduce its quadratic norm \(\nu(t)=A(t)^2+s(t)A(t)B(t)+p(t)B(t)^2\) modulo \(Q\). This reduced polynomial in \(t\) has degree two with unit leading coefficient.
2. The remainder of \(Q\) modulo \(\nu\) is linear with unit leading coefficient. Any zero of the first contact in a quotient then has \(\nu=0\) as well and forces a specific \(t=t_*\) in the scalar residue ring. The replay checks \(B(t_*)\) a unit; hence it forces \(u_*=-A(t_*)/B(t_*)\) and \(v_*=s(t_*)-u_*\).
3. With these root readings, every \(\Omega\) is a unit, by exact polynomial gcd with \(\overline N\). The replay checks 16 repeated-clock pairings and eight determinants.

Thus in the mod-101 finite free algebra modulo \((\Psi)\), the appropriate \(\Omega\) for any fixed chronology is a unit. Equivalently the image of the linear map \((x,y)\mapsto\Psi x+\Omega y\) is the entire algebra modulo 101. In fixed bases, some maximal minor of this map is therefore a unit in \(\mathbb Z_{(101)}\), so the image is the entire algebra also in characteristic zero. An actual characteristic-zero layout would give a unital evaluation at its \(a,t,u\) with both \(\Psi,\Omega\) zero, a contradiction. This is a lift of a finite free coefficient-algebra calculation, not specialization of tableau entries.

For \(h=d\), reflect the scalar clock system, exchanging the two fronts and widths and reflecting the two anchored model bases. All expressions defining the paid pairings have their reflected analogues because both seventh-boundary primitives are available through grade five and the inverse mixed Gram is symmetric. Apply the proof in that orientation to the reflected mixed overlap. This is not an appeal to ordinary reverse order eleven.

The [standalone Python replay](erk11-mixed-overlap-one-cross-exit/replay_mixed_onecross.py) performs the exact coefficient norm and finite ring unit checks. Exact Lean replay of this separate calculation is not claimed here.
