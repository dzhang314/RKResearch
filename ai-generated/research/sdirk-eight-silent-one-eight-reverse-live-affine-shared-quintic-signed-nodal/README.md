# Corrected shared-quintic ordinary hole: non-Gauss guard and signed nodal form

Use the [actual ordinary-hole setup and paid signed rule](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) in strict SDIRK8 at ten stages over a characteristic-zero field. There are nine distinct actual quadratic-zero clocks, eight ordinarily active and one ordinarily silent but reverse-live. The affine reverse numerator and genuine quintic mixed numerator share their root \(r\), which is actually ordinary. The actual normalized amplitude is zero at \(r\); its continued quartic has \(H(r)\ne0\). With shifted standard-normalized Legendre polynomials, write
\[
 H(X)=\alpha L_4(X)+\beta K_3(X,r),\qquad
 \alpha\ne0,\quad \beta=b_r H(r)\ne0,
\]
where \(K_3\) reproduces evaluation at \(r\) through degree three. Set \(I(X^j)=1/(j+1)\), \(I_r=I-b_r\operatorname{ev}_r\), and write
\[
 W_F(X)=I_{r,Y}\left((F(X)-F(Y))/(X-Y)\right).
\]
Let \(D_7\) be the **monic** nodal polynomial of actual ordinary nonhole clocks, not including the ordinarily silent stage \(\zeta\). The seven ordinary nonhole clocks pay \(I_r\) through degree seven; every one has the same actual nonzero \(D'_7(c_i)b_i H(c_i)=\lambda\), obtained by dividing only genuine ordinary nonhole factors \(c_i-r\). By the paid signed Bézout identity,
\[
 H W_{D_7}-D_7 W_H=\lambda\ne0.                         \tag{1}
\]
The following conclusions apply independently of actual hole position, early rank and ordinary rear phase. They are scalar restrictions, not a ten-stage exclusion.

## One exact identity

Write \(M_5=(X-r)L_4(X)\). Orthogonality gives \(I_r(X^jH)=0\) for \(j\le3\) and \(I_r(X^jM_5)=0\) for \(j\le2\). For the first remaining moments,
\[
 I_r(X^4H)=\alpha/630-\beta L_4(r)/70,\qquad
 I_r(X^3M_5)=1/630 .
\]
Indeed \(I(X^4 L_4(X))=1/630\), and \(X^4-L_4(X)/70\) has degree at most three, whose reproducing moment against \(K_3\) is exact. Since \(M_5(r)=0\), its signed moment is its ordinary polynomial integral. Write \(\delta_F(X,Y)=(F(X)-F(Y))/(X-Y)\). Thus
\[
 \begin{aligned}
 H W_{M_5}-M_5 W_H
 &=I_{r,Y}\big(\delta_{M_5}(X,Y)H(Y)-\delta_H(X,Y)M_5(Y)\big)\\
 &=70\, I_r(X^4H)-70\alpha\, I_r(X^3M_5)\\
 &=-\beta L_4(r).                                                   \tag{2}
 \end{aligned}
\]
No ordinary order condition beyond the previously paid scalar rule was used.

## True guard and full signed nodal scalar family

The paid nonzero constant in (1) gives \(\gcd(H,W_H)=1\). If \(L_4(r)=0\), then (2) gives \(H\mid M_5\). But \(M_5=(X-r)^2G_3\) with \(\deg G_3=3\). Since the continued \(H(r)\ne0\), \(H\) is coprime to \(X-r\), so \(H\mid G_3\), impossible. Thus **\(L_4(r)\ne0\)** in the actual coefficient field. This factor may be removed from an exact projection as a source-level guard, not merely by observing its modular residues.

Take \(\nu=-\lambda/(\beta L_4(r))\ne0\). Subtract (2) times \(\nu\) from (1), and use the same coprimality. This proves
\[
 \boxed{\quad D_7=H U_3+\nu(X-r)L_4(X),\qquad
   \deg U_3=3,\quad [X^3]U_3=1/(70\alpha),\quad U_3(r)\ne0.\quad}
\]
The last assertion follows from \(D_7(r)=H(r)U_3(r)\ne0\). One may use four linear unknowns (the lower coefficients of \(U_3\), and \(\nu\)), homogeneous peg and terminal equations, and no inverse of a divided-difference polynomial. At each actual ordinary nonhole peg \(\xi\), the equation is \(H(\xi)U_3(\xi)+\nu(\xi-r)L_4(\xi)=0\). It is **not** imposed at the purely reverse-live site \(z\).

Conversely for any cubic \(U_3\), \(W_{HU_3}=U_3 W_H\) by the \(H\) moments through degree two in the divided difference of \(U_3\). A polynomial in the boxed form therefore obeys (1) with constant \(-\nu\beta L_4(r)\). It also obeys \(I_r(D_7)=0\), by the moments through degree three and \(I_r(M_5)=0\). If this polynomial has seven distinct allowed ordinary roots, their cardinal masses for \(I_r\) integrate degrees through six by interpolation and degree seven by this last zero moment. At each distinct root \(\xi\), (1) then gives \(D'_7(\xi)b_\xi H(\xi)=-\nu\beta L_4(r)\ne0\). This converse concerns only the ordinary signed scalar rule, not reverse chronology or RK tableau existence.

Run `python3 check_signed_nodal.py` with `sympy==1.14.0`. The standalone exact replay checks the identity after multiplying by \(H(r)\), requisite moments, and the basis of all four cofactor actions. It reads no neighboring files and assumes no modular reduction of a tableau. The divisibility and chronology arguments are source proofs, not new native Lean claims.
