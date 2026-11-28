# The affine trace as a small linear remainder

This is a reusable necessary field condition, not needed for the chronological exclusions in [README](README.md). Keep the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) with an affine, nonconstant singleton graph \(R(t)=\alpha(t-\rho)\), \(\ell=1/\gamma\), and centered monic Legendre polynomials \(L_3,L_4\). Put \(Q_0=Q/B=L_3-(F/B)L_4\). The corrected [normalized trace](../sdirk-eight-all-dirty-seven-constant/README.md#the-trace-gate-and-its-normalization) is \(2\sum_i1/g_i=\ell\sum_i b_i/g_i\).

For fixed affine graph and doubled clock polynomial \(P\), this is **one linear equation in the three coefficients of \(A_2\), independent of \(B\)**. It can be evaluated by a polynomial remainder modulo \(L_4^2\), without factoring the Legendre quartic or excluding a common zero of \(P,R\).

First, at the four singleton labels the residuals are \(R(t)\), and their monic polynomial is \(H=L_4-R(A_2+BR)\). Since \(Q(\rho)=0\), consecutive Legendre coprimality gives \(L_4(\rho)\ne0\), hence \(H(\rho)\ne0\). At the doubles \(g_1g_2=-L_4/B\), \(g_1+g_2=-A_2/B\). Thus literal summation and the logarithmic derivative give
\[
 T_g:=\sum_i\frac1{g_i}
   =-\frac{H'(\rho)}{\alpha H(\rho)}
      +\sum_{d:P(d)=0}\frac{A_2(d)}{L_4(d)}
   =-\frac{L_4'(\rho)}{\alpha L_4(\rho)}
      +\frac{A_2(\rho)}{L_4(\rho)}
      +\sum_{d:P(d)=0}\frac{A_2(d)}{L_4(d)}.             \tag{1}
\]
All the denominators are nonzero, including if a doubled clock equals \(\rho\).

For the weighted trace, let \(k=BH_3\) where \(H_3=I(L_3^2)\) in the normalized average. The grouped Cauchy transform of \(\nu_i=b_i g_i\) is \(k/(P H)\). At paired \(d\) the signed \(\nu_i\)-average of the two \(g\)'s is \(R(d)\). From \(1/g=(A_2+Bg)/L_4\) there, the grouped \(b/g=\nu/g^2\) is the \(\nu\)-mass multiplied by \([A_2(A_2+BR)+BL_4]/L_4^2\) at \(d\). At a singleton it is the \(\nu\)-mass divided by \(R^2\). The rational function
\[
 Z(T)=\frac{k[A_2(A_2+BR)+BL_4]}{P H L_4^2}
   =\frac{k}{P H R^2}
       -\frac{H_3(L_4+R A_2)}{Q_0 R L_4^2}
\]
therefore has physical residues \(\sum b/g\) at roots of \(P,H\), except for the extra residues from the second term at any common \(H,L_4\) roots. In detail: the first expression shows the stated simple paired residue even when \(R\) vanishes at that D label. The second expression shows the singleton residue, possibly plus the extraneous second term at a common \(H,L_4\) root. At every \(L_4\)-root, neither \(R\) nor \(Q_0\) vanishes by Legendre coprimality and \(Q=P R\); the first term is regular there unless this is an actual singleton, in which case its residue is already part of the physical sum. The first expression has no other poles and has no residue at infinity. Summing coefficients of simple Laurent terms in a splitting field now gives
\[
 T_b:=\sum_i\frac{b_i}{g_i}
   =\sum_{\zeta:L_4(\zeta)=0}
      \operatorname{Res}_{T=\zeta}
      \frac{H_3(L_4+R A_2)}{Q_0 R L_4^2}.                 \tag{2}
\]

A compact algebraic evaluation of (2) needs no splitting field. In the polynomial quotient modulo \(L_4^2\), invert \(Q_0 R\), multiply by \(H_3(L_4+R A_2)\) and take the usual remainder \(N\) of degree below eight. The rational function in (2) and \(N/L_4^2\) have identical Laurent singular parts at those roots. Their residue sum is thus the coefficient of \(T^7\) in \(N\), since \(L_4^2\) is monic degree eight and \(N/L_4^2\) has no other finite poles. The exact necessary condition is \(2 T_g=\ell[T^7]N\). In particular it never divides by \(R(d)\) at a double, even if that graph-zero label corresponds to a double root of \(Q\).
