# No supported quadratic line at three distinct strict SDIRK8 quadratic zeros

**Result.** Suppose \(A,\boldsymbol b\) is a ten-stage strict SDIRK tableau of order at least eight over a characteristic-zero field. Write \(\boldsymbol c=A\boldsymbol1\), \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\), and \(U=\ker\operatorname{diag}(\boldsymbol g)\). If exactly three rows have zero quadratic residual, at three distinct clocks, then \(E_2\cap U=0\). In particular no all-active tableau has this zero pattern. A surviving exact-three-distinct case would have \(\dim(E_3\cap U)\in\{1,2\}\) and an off-zero silent stage. This proof alone does not exclude those silent cases, larger zero sets, or the zero-free case. The unrestricted interval stays **10–11**.

## 1. From supported \(E_2\) to an all-active scalar chart

Use the saturated flags \(E_j,F_j,W_j,Z_j\), \(C=\operatorname{diag}(\boldsymbol c)\), \(G=\operatorname{diag}(\boldsymbol g)\), \(B=\operatorname{diag}(\boldsymbol b)\), and \(M=CA-AC-A^2\). The [two-sided support identity](../sdirk-eight-two-zero-line/README.md) gives \(\dim(W_2\cap U_{\rm row})=3-\dim(E_3\cap U)\). Weighting \(E_2\cap U\) into this row space is injective: ordinary probes detect the scalar profile, and the pure line \(\langle\boldsymbol g\rangle\) has no nonzero supported vector. Hence \(d_2+d_3\le3\), writing \(d_j=\dim(E_j\cap U)\). If \(d_2>0\), a nonzero supported vector \(\boldsymbol v\) must have at least two nonzero coordinates at distinct zero clocks. Single-clock support at \(a\) would annihilate its trace by the four scalar probes against \((X-a)X^j\). Thus \(\boldsymbol v,C\boldsymbol v\) are independent in \(E_3\cap U\), giving \(d_2=1,d_3=2\).

The [finite chart](../sdirk-eight-three-zero-chart/README.md) shows that this branch is all-active, with seven distinct off-zero clocks and supported vector \(\boldsymbol v=r(2\boldsymbol c-\boldsymbol1)+\alpha\boldsymbol g\), where \(r(y)=y^2+ky+q\) and \(\alpha\ne0\). Its values at the three zero clocks are nonzero. Both actual time orientations have a clean grade-three pure space on \(U\), nonzero residuals at the second stage, and identical diagonal \(\gamma\ne0\); reflection replaces \(k\) by \(-k\).

In centered \(y=2X-1\), let \(I(y^j)=1/(j+1)\) if \(j\) is even, zero if odd. The monic cubic \(P_{\rm monic}\) of the zero clocks is reconstructed through \(I(rP_{\rm monic}y^j)=0\), \(0\le j\le2\). Set \(P=T P_{\rm monic}\), where
\[
                     T=-105k^2q-15k^2+175q^3+255q^2+105q+9\ne0 .
\]
The earlier diagonal identity gives \(180\gamma\mathcal A(k^2,q)-\mathcal B(k^2,q)=0\). The [replay](check_exclusion.py) reconstructs \(P\) by Cramer's rule and checks \(\mathcal A,\mathcal B\) from the signed moment formulas in the chart.

## 2. Actual chronological endpoint gates

The earliest zero only sees the diagonal when applying \(A\) to \(\boldsymbol v\). The clean grade-three read must also equal the primitive of \(r(2X-1)\) from zero. The centered difference, times twelve, is
\[
 H(y)=2y^3+(3k-12\gamma)y^2+(6q-12\gamma k)y+2-3k+6q-12\gamma q .
\]
The first zero is already a root of \(P\), so \(h(k,q,\gamma)=\operatorname{Res}_y(P,H)=0\). The same anchor holds at the reflected end; it does not depend on the second-row denominator.

For the second physical gap \(u\ne0\), the chart pays \(Du=U_0\), with
\[
 R=r(2\gamma-1),\qquad D=R+4\gamma^2,\qquad U_0=2R-2\gamma(4\gamma-2+k).
\]
If \(D\ne0\), each end has one of two alternatives:
* **A:** an off-zero arithmetic third row (the star would duplicate an off-zero clock). Write \(f=F/(2\gamma)\) for the polynomial arithmetic test from the chart.
* **Z:** a zero third row, with \(G=4U_0^3-12U_0^2D+3U_0 D^2+2D^3=0\). Its actual centered clock is \(z/D\), \(z=2\gamma(D+2U_0)-D\). Hence \(p_{\rm pin}=D^3 P(z/D)=0\).

Thus the systems are AA with \(f,h\) at both ends, AZ with \(f,h\) at the front and \(G,p_{\rm pin}\) at the back (up to reflection), or ZZ with \(G,p_{\rm pin}\) at both ends. No off-zero clock reconstruction is needed.

## 3. Exact elimination over characteristic zero

The [exact replay](check_exclusion.py) uses Python and python-flint 0.9.0. First handle exceptions:
* If \(D=0\), then \(U_0=0\), so \(k=2-8\gamma,q=8\gamma^2-8\gamma+1\) after possible reflection. Substituting into the diagonal and anchor gives coprime degree \(11,27\) polynomials in \(\gamma\).
* At \(k=0\), simultaneous zeros of \(\mathcal A,\mathcal B\) require \(T=0\). Otherwise substitute \(\gamma=\mathcal B/(180\mathcal A)\) and use \(f,h\) if an arithmetic end exists; else use \(G,p_{\rm pin}\). Their gcd in \(q\) is a unit after removing the nonzero factors of \(T\mathcal A\mathcal B\).
* If \(k\ne0\) and \(\mathcal A=\mathcal B=0\), their resultant in \(k\) is proportional to \(J_1^2J_2^2J_3^2\), defined below. In each \(q\) fiber, eliminating the leading quadratic term of \(\mathcal A,\mathcal B\) fixes \(x=k^2\) using a verified unit. The first two fibers force \(T=0\); in the third the simultaneous gate polynomials in \(\gamma\) have gcd one for all three chronologies. For AA and ZZ take even and divided-odd parts in \(k\). For AZ take norms \(p_e^2-xp_o^2\) of the necessary equations \(p_e\pm kp_o=0\).

In the remaining branches substitute \(\gamma=\mathcal B/(180\mathcal A)\), clear its denominator, and divide out factors known nonzero (from \(k,\mathcal A,T,\gamma,R,D,U_0\), the last three at both ends). In AA and ZZ, split into even and divided-odd parts and replace \(k^2\) by \(x\). Eliminate \(x\) in these cases and \(k\) in AZ. For each system take resultants of the first polynomial with the others, then their gcd in \(q\). The gcds, up to nonzero rational factors, are given by the powers in the table of
\[
\begin{aligned}
 J_1 &=35q^2-3,\qquad J_2=35q^2+30q+3,\qquad J_4=3q-1,\\
 J_3 &=1225q^8+9450q^7+24640q^6+25230q^5+9639q^4
                   -480q^3-1212q^2-360q-36 .
\end{aligned}
\]

| Ends | Projection powers \((J_1,J_2,J_3,J_4)\) | Common fiber gcd degrees before nonzero guards |
|---|---|---|
| AA | \(6,6,6,0\) | \(2,2,2,\text{—}\) |
| AZ | \(36,27,18,1\) | \(6,6,6,0\) |
| ZZ | \(30,30,30,2\) | \(5,5,5,0\) |

A common root forces each resultant to vanish even with a degree drop, by the evaluation-vector kernel of the fixed Sylvester matrix. The replay checks the complete projection products and runs exact Euclid in each \(\mathbb Q[q]/(J_i)\), checking every inverse used. In the \(J_4\) fiber the gcd is one; in the other fibers every factor of the common gcd divides the verified nonzero guard product after repeated exact division. No fiber has a permissible point. The identities specialize into any characteristic-zero field.

The [Lean endpoint receipt](../../lean/RKCert/ReviewedNative/SDIRK8ThreeZeroEndpointReceipt.lean) checks the cubic moment binding, the degree-three Sylvester common-root identity, and the guarded \(D=0\) contradiction with an explicit integer Bézout identity. It compiled on Lean/Mathlib 4.36.0 with only standard axioms. The multivariate eliminations and tableau-to-scalar reduction are the reproducible source proof, not one Lean nonexistence theorem.

## 4. Remaining exact-three-distinct ranks

Now \(d_2=0\), so \(F_3=GE_1\) vanishes on \(U\). If \(d_3=3\), each literal axis \(\boldsymbol e_i\) of \(U\) is in \(E_3\). Its scalar trace \(r_i\) is nonzero by cleanness and obeys \(I(r_i f)=b_i f(y_i)\) for all degrees at most four, hence \(b_i\ne0\) by moment rank. Using \(f=(y-y_i)y^j\), \(0\le j\le3\), gives that \((y-y_i)r_i\) is proportional to the centered monic fourth Legendre polynomial \(L_4=y^4-6y^2/7+3/35\). Thus the trace is its Gauss cardinal polynomial by the clean value \(r_i(y_i)=1\). The grade-\(3+4=7\) self-pair gives
\[
             b_i\gamma=\boldsymbol e_i^{\mathsf T}BA\boldsymbol e_i
                =I(r_i J r_i)=I(r_i)^2/2=b_i^2/2 ,
\]
where \(J\) is the integral from \(-1\) in centered time with derivative \(r_i/2\). Direct integration of the cardinal gives \(b_i=(y_i^2-11/21)/(4(y_i^2-3/7))\), an injective function of the square \(y_i^2\) on these roots. At most two distinct Gauss nodes can share the weight \(2\gamma\), a contradiction.

Also \(d_3\ne0\). If \(d_3=0\) then \(GE_3=F_5\) vanishes on \(U\), although \(F_5=\operatorname{Ann}(W_2)\) contains the third and fourth Legendre columns, whose polynomials have no common root. Finally, the weighted map \(E_2\to W_2\) is an isomorphism: ordinary scalar probes detect its trace, and some active off-zero coordinate detects the pure line by scalar rank four and only three zero rows. If every off-zero weight were nonzero, a supported \(W_2\) row would have a supported \(E_2\) preimage, impossible as \(d_2=0\); support rank would force \(d_3=3\) again. Thus \(d_2=0,d_3\in\{1,2\}\) and an off-zero silent stage are the residual possibilities.
