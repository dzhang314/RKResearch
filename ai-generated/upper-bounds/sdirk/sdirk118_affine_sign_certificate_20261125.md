# Fixed SDIRK(11,8): exact seed existence and affine calibration signs

**Source-level scalar certificate only.** This uses the fixed chart and the accompanying whole-box guard certificate. It does not evaluate the real roots or construct a tableau. The standalone script checks fixed rational bounds and endpoint signs; it does not contain a root search. The established scalar existence is distinct from a checked Lean chart or a native upper bound.

## Fixed rational input boxes, with exact existence

Use the following pairs of strictly certified bracket endpoints. Every entry in the table is an exact rational, not an approximate root supplied as a coefficient.

| Parameter | Lower | Upper |
|---|---:|---:|
| \(s\) | \(457148959716/2^{40}\) | \(457148959717/2^{40}\) |
| \(t\) | \(138977439915/2^{40}\) | \(138977439916/2^{40}\) |
| \(c_*\) (the larger root of \(B_*\)) | \(1270550/2^{20}\) | \(1270551/2^{20}\) |

- \(F(X)=X^3-9X^2+18X-6\) has opposite endpoint signs \((-,+)\) at the displayed \(s\) bracket. This is in the original \((13/32,14/32)\), on which the selected cubic is strictly increasing, so the real root by IVT is the same small seed.
- For **every** \(s\) in the fixed \(s\) box, \(q_s(Y)=Y^2-3Y+(1-Y)s\) has strict signs \((+,-)\) at the displayed \(t\) bounds. The box lies in \((1/8,13/100)\) and below \(s/3\). The smaller exact root exists by IVT and is the one required by the reverse seed. This uses the reduced quadratic from sdirk118_scalar_existence_audit_20261125.md, not a new normalized reverse chart.
- For **every** pair in these \(s,t\) boxes, put \(a=(1+s)/2,\ z=a+s,\ Z(X)=(X-1)(X-a)(X-s)(X-t)\), and \(\mu_j=z^{-1}I_z(X^jZ)\) for \(j=0,\ldots,3\). Here \(I\) is the zero-constant polynomial primitive and \(I_z\) evaluates it at \(z\). Set
\[
D_\mu=\mu_0\mu_2-\mu_1^2,\quad N_1=\mu_1\mu_2-\mu_0\mu_3,\quad
N_0=\mu_1\mu_3-\mu_2^2,\quad \Psi(X)=D_\mu X^2+N_1X+N_0.
\]
The fixed sign data certify \(D_\mu>0,\ \Psi(0)<0,\ z<c^-\), and \(\Psi(c^-)<0<\Psi(c^+)\). The moment solve gives \(B_*=\Psi/D_\mu\). IVT yields the exact larger root \(c_*\) in the displayed bracket, and Vieta gives the other root \(b_*=-N_1/D_\mu-c_*<0\). Both roots and all six sites are distinct. No square root or actual root value is required by this certificate.

The \(s,t\) boxes are subsets of the previously authorized coarse rectangle. The independent whole-box signs in sdirk118_guard_sign_certificate_20261125.md, with the separate moment pivot/node certificate, therefore give all four interior weight numerators and the residual \(J_0\) nonzero. Together with \(D_\mu>0\), this gives all six required nonzero weights at the selected exact parameters. There is no assumption of positive abscissae.

## Small expression for the actual affine endpoint signs

Use \(c=c_*, b=b_*\), \(\gamma=1/z\), \(x_1=\gamma s\), \(x_5=1-c/z\). Define \(J(X)=(X-s)(X-t)(X-1)\) and the two scalar polynomial averages
\[
\ell_j = \frac1z I_z\!\left[X^j(X-a)(X-c)(I J-J)\right]\quad(j=0,1).
\]
These involve only degree at most 7 and the coefficients \(s,t,c\), not the smaller root \(b\) or any evaluation tree. Put
\[
j_*(T)=(T-z+c)\bigl(\ell_0(z-T)-\ell_1\bigr),
\]
and let \(H_{\mathrm{sel}}(\gamma T)=(T-s)j_*(T)\) denote the **unscaled selector**. This is not the kernel cubic from the prior rank proof.

To verify its exact connection to the archived selector, the degree-seven quadrature integrates both relevant scalar products exactly. Use \(p_0=(X-x_1)(X-x_5)\), \(p_1=Xp_0\), \(K_4(Y)=J(zY)/J(b)\) and \(\lambda_i=\Lambda(p_i,K_4)\). Substitution \(X=1-U/z,\ Y=U/z\) gives
\[
\lambda_0=\frac{\ell_0}{z^3J(b)},\qquad
\lambda_1=\frac{\ell_0-\ell_1/z}{z^3J(b)},\qquad
P(\gamma T)=(\lambda_1p_0-\lambda_0p_1)(\gamma T)
          =\frac{(T-s)j_*(T)}{z^6J(b)} .
\]
In particular the same nonzero scale relates the two endpoint signs; do not mistake the sign of the unscaled selector for the sign of a particular normalized \(P\).

With \(r=s/3,\ B_s=(1-s)(3-s),\ \eta=(3+s)/(4(3-s))\), put
\[
L(T)=(B_s-1)(T-1)-\eta(T+1-2s),\qquad M_s=\eta B_s-3(B_s-1-\eta).
\]
Let \(\iota_j(T)\) be the affine interpolation of \(j_*(T)/(T-r)\) from \(1,a\). The audited affine response formula for \(H_{\mathrm{sel}}\) is
\[
E(T)=\frac{L(T)j_*(r)}{(1-r)(a-r)}-\frac{M_s}{3}\iota_j(T).
\]
The actual reduced response satisfies \(\widehat B_P(T)=E(T)/(z^6J(b))\). The sign test is **\(E(15/4)<0<E(4)\)** on the entire fixed \(s,t,c\) box. For the normalized choice \(P=\lambda_1p_0-\lambda_0p_1\), \(J(b)<0\), so its two individual reduced signs are reversed; their product is negative. Passing to the original \(\mathcal C\) also preserves the sign change, by the exact factorization
\[
\mathcal C(T)=-\kappa(\det V_0)(T-s)(T-1)(T-a)\widehat B_P(T)
\]
from the scalar audit. The code additionally evaluates both endpoints via the earlier **direct cleared response** \(\mathcal L_{H_{\mathrm{sel}}}\), before division by \((T-s)(T-1)(T-a)\), and gets the same strict unscaled signs. This is a check of the two algebraic expressions on the same input bounds, not a substitute for the identities.

Thus the chosen affine function is nonconstant and has a unique zero in \((15/4,4)\). The exact \(d\) is its coefficient ratio if needed; the script never calculates it. The original \(\mathcal C(d)=0\), automatically guarded forward/reverse pivots, and \(J_0\ne0\) follow via the separate source identities. This supplies the formerly missing **scalar existence package** at the mathematical level; the exact chart and diagonal-twin composition still need Lean instantiation.

## Reproduction and integer interval data

The matching standalone **sdirk118_affine_sign_certificate_20261125.js** was executed from full note readback. It uses closed outward integer intervals \([l/K,h/K]\), \(K=2^{64}\). Its arithmetic increases an endpoint bound only by exact floor/ceiling of a BigInt quotient. Addition/subtraction use direct bounds; multiplication and division use corner extrema, with division rejecting intervals touching zero. Coefficients are constructed by finite polynomial products, and each normalized primitive average uses \(z^{k+j}/(k+j+1)\) on the monomial of degree \(k+j\). Hence each output is a valid uniform rational enclosure for the corresponding exact expression. The strict sign assertions reject any enclosure touching zero.

Exact script output, with both integer endpoints divided by the reported common scale:
```text
common-scale 18446744073709551616
seed-cubic-lower -156996525 -156996523
seed-cubic-upper 28134407 28134408
reverse-quadratic-lower 36435625 51092216
reverse-quadratic-upper -16630308 -1973718
moment-determinant 21444555992759 21444556991322
larger-node-lower-minus-z 1623849679856861184 1623849679882027008
quadratic-at-zero -1954075334988 -1954074270433
larger-node-polynomial-lower -16404071 -12465253
larger-node-polynomial-upper 9914350 13853173
affine-15/4 -155803327669626 -132079553156373
direct-cleared-15/4 -4815081243479642 -3214978901469819
affine-4 105456769076090 132743982375427
direct-cleared-4 2696081155781849 5735992589834140
```
