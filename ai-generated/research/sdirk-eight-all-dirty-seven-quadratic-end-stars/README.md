# Two singleton pairs after doubled endpoints: quadratic star and shared-clock exclusions

Keep a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with all physical quadratic residuals nonzero and exactly seven distinct clocks. The graph \(R\) of singleton residuals is now genuinely quadratic by the [constant](../sdirk-eight-all-dirty-seven-constant/README.md) and [affine](../sdirk-eight-all-dirty-seven-affine-final/README.md) exclusions. Type D means a doubled physical clock label and S a singleton label. This note assumes the two physical endpoints have type D and each actual first-three prefix has type **D,S,S**, where the two orientations are original and genuine weighted mirror.

**Results.** Neither prefix can use a literal star third row, so both must be arithmetic. In addition, if the endpoint labels coincide and \(R\) is centered-even, the arithmetic/arithmetic case is also impossible. These exclusions retain signed weights and all common \(P,R\) roots; they do not exclude the remaining quadratic graphs or a ten-stage tableau overall.

## Odd projection from doubled endpoints

Normalize the common diagonal to one, let \(\ell=1/\gamma\), and use dimensionless centered coordinate \(v=(2x-\ell)/\ell\), with endpoint labels \(\pm e\) where \(e=(\ell-2)/\ell\). Write \(P\) for the cubic with the three D labels, and \(Q=P R=B L_3-F L_4\) in centered coordinates, as in the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md). Here \(F\) is affine nonconstant. Since both endpoints are D, \(Q(\pm e)=0\). If \(e\ne0\), \(J_3\) is odd and \(J_4\) even, so the intercept of \(F\) must vanish; \(J_4(e)\ne0\) by consecutive Legendre coprimality. If \(e=0\), evaluating \(Q(0)=0\) also makes the intercept vanish. Thus, up to nonzero rescaling,
\[
   Q(v)=v\bigl(5v^2-3-\zeta(35v^4-30v^2+3)\bigr),\qquad \zeta\ne0 .
\]
Whenever \(a,b\) are two distinct squared-root labels of the bracket, the two actual polynomial equations imply
\[
        35ab-21(a+b)+15=0,
\]
by cancelling \(5(a-b)\) from the cross difference of \(5a-3,5b-3\) and \(35a^2-30a+3,35b^2-30b+3\). Repeated squared roots are not discarded from the original shape.

## At least one star and the complete small root shapes

An actual star with gap \(u=x_2-1\) has clocks \(1+u,3-u\) and equal normalized residuals \(\kappa(u)/2\), where \(\kappa=1+2u-u^2\). Both rows are singleton, so the equality at different clocks fixes the axis of the genuinely quadratic **uncentered** graph at \(x=2\). Thus \(R(x)=r[(x-2)^2-S]\), \(r\ne0\), for some squared root gap \(S\); this identity is polynomial even if the roots do not split in the original field. In dimensionless coordinates the two graph roots sum to \(2-4e\).

- If \(e\ne0\), the D labels consist of \(\pm e\) and a third \(d\). If \(d=0\), the graph is even in centered coordinates; its star axis then forces \(\ell=4\), \(e=1/2\). In centered **unnormalized** \(t=x-\ell/2=x-2\), the D labels are \(0,\pm1\). Their squared labels give \(F/B=(49/37)t\), so \(Q/B=L_3-(49/37)t L_4\) has roots \(0,\pm1,\pm\sqrt{156/49}\). The graph has \(S=156/49\).
- If \(e\ne0\) and \(d\ne0\), the distinct D labels \(d,\pm e\) force all five different \(Q\)-roots \(0,\pm e,\pm d\), so the other two roots, belonging to \(R\), are \(0,-d\). Thus \(d=4e-2\), and the squared-root relation above yields
\[
          560e^4-560e^3-217e^2+336e-69=0,\qquad S=(\ell d/4)^2.
\]
- If \(e=0\), \(\ell=2\) and the graph axis \(x=2\) forces the two dimensionless graph roots to sum to \(2\). A repeated bracket root, or a zero squared root, would leave only distinct D labels \(0,\pm d\); the corresponding leftover \(R\) is centered-even and has root sum zero, so this is not a star. More generally choosing the two noncentral D labels from the same opposite pair also leaves even \(R\). Hence the two graph roots are different choices from the two distinct nonzero opposite pairs, with sum 2. If their product is \(k\), the squared-root relation gives \(35k^2+42k-69=0\) and \(S=1-k\).

Thus the literal star, not an unproved genericity assumption, removes all repeated/Hermite root cases from this shape: the even root \(156/49\), the split nonzero \(d\), and the exact quadratic in \(k\) give \(S\ne0\). The remaining proof still works via polynomial remainders at the graph roots, including field extensions.

## Two stars

The reflected star also fixes the graph axis in its own normalized clock at \(2\); in original coordinates this is \(\ell-2\). Hence \(\ell=4\), the even shape above with \(S=156/49\). The four observed S labels have centered clocks \(\pm\sqrt X,\pm\sqrt Y\), with \(X=(u-1)^2,Y=(u_{\rm r}-1)^2\) from the two star gaps. Distinctness and literal nonzero guards give \(X,Y\notin\{0,1,2,S\}\) and \(X\ne Y\). The graph scale \(r\) and reverse-to-original residual scale \(\lambda\) therefore satisfy
\[
 r=\frac{2-X}{2(X-S)},\qquad
 \lambda=\frac{(2-X)(Y-S)}{(X-S)(2-Y)} .
\]
Since \(S\ne2\), \(\lambda\ne1\) follows from \(X\ne Y\).

The actual singleton quartic is \(H(t)=h(t^2-X)(t^2-Y)\) with nonzero leading scalar \(h\), not presumed monic. From \(H=L_4-R(A_2+B R)\) and evenness of \(H,L_4,R\), the quartic fit \(C=A_2+B R\) is even. The doubled labels \(t=\pm1\) therefore have the same residual quadratic, with the two known endpoint roots \(1/2,\lambda/2\). In particular \(B=-4 L_4(1)/\lambda\). Evaluating \(H\) modulo \(t^2-S\) gives \(h=L_4(\sqrt S)/[(S-X)(S-Y)]\), while at \(t=1\)
\[
 H(1)=-B(R(1)-1/2)(R(1)-\lambda/2).
\]
The two differences simplify to
\((1-X)(2-S)/[2(X-S)]\) and \(r(1-Y)(2-S)/(2-Y)\). Substituting and cancelling the known nonzero factors gives \(L_4(\sqrt S)=L_4(1)(2-S)^2\). Here \(L_4(t)=t^4-(24/7)t^2+48/35\), and the actual discrepancy is \(174196/84035\ne0\). This contradiction uses no stage weights.

## One star and one arithmetic

Orient the star forward, and use \(t=x-2\). Its two singleton labels are \(\pm\sqrt X\). With actual reverse arithmetic gap \(v\), the other two singleton labels in original coordinates are at \(t_2=\ell-3-v,\ t_3=\ell-3-2v\). The actual phase gives reverse residual ratio \(q_{\rm num}(v)/[\kappa(v)D(v)]\), where
\[
 D(v)=-2+v+4v^2-v^3,\qquad
 q_{\rm num}(v)=(1+4v-4v^2)D(v)+4v^2(3v-2).
\]
Hence
\[
        q_{\rm num}(v)(t_2^2-S)-\kappa(v)D(v)(t_3^2-S)=0.
\]
The complete singleton polynomial is \(H(t)=h(t^2-X)(t-t_2)(t-t_3)\). Reducing at \(t^2-S\) makes the first factor the nonzero scalar \(S-X\). Let \(L_0+L_1 t\) be the remainder of \(L_4(t+2-\ell/2)\) modulo \(t^2-S\). From \(H\equiv L_4\) the two coefficient rows are proportional, yielding the degree-at-most-two gate
\[
              -(t_2+t_3)L_0-(t_2t_3+S)L_1=0.
\]
In the even \(\ell=4\) case \(L_1=0,L_0\ne0\), so \(v=2/3\), which is forbidden by the genuine nonzero arithmetic tap. In both split fields the exact gcd of the two scalar equations is one. The check uses the irreducible quartic or quadratic indicated above, not any real root or sign assumption.

## Two arithmetic prefixes at a shared D clock with even graph

Suppose \(\ell=2\), so the two literal D endpoints share \(t=x-1=0\), and \(R(t)=r(t^2-S)\) is centered-even. Let the actual arithmetic gaps be \(u,v\ne0\); the four S coordinates are \(u,2u,-v,-2v\). The odd coefficient of that quartic modulo \(t^2-S\) must vanish since \(L_4\) is even. It is proportional to \((v-u)(S-2uv)\). If \(u=v\), the known two singleton residuals in the two orientations imply the scale \(\lambda=1\), duplicating the physical endpoint pair \((t,g)=(0,1/2)\). Thus \(S=2uv\ne0\), which also handles the possible Hermite root by contradiction rather than skipping it.

For either arithmetic gap the literal residual ratio gives
\[
        q(u)(u-2v)=\kappa(u)(4u-2v),\qquad
        q(u)=q_{\rm num}(u)/D(u).
\]
The difference \(q(u)-\kappa(u)\) is nonzero: equality would make the nonconstant even quadratic take equal values at \(u\) and \(2u\), impossible for \(u\ne0\). Therefore \(v=f(u)\), \(u=f(v)\), with
\[
 f(u)=\frac{u(q(u)-4\kappa(u))}{2(q(u)-\kappa(u))}
     =\frac{4u^2+7u-6}{6u^2-16u+8}.
\]
The original scale is \(r=\kappa(u)/[2(u^2-S)]\) and \(\lambda=2r(v^2-S)/\kappa(v)\). At the shared D clock the two roots \(1/2,\lambda/2\) give \(B=-4L_4(0)/\lambda\). The monic singleton product has value \(S^2\) at zero and constant remainder \(S(2u^2+2v^2-5uv)\) modulo \(t^2-S\). The latter is nonzero because \(H\equiv L_4\), whose value at a graph root is nonzero. Thus also
\[
 \frac{L_4(\sqrt S)\,S^2}{S(2u^2+2v^2-5uv)}
  =H(0)=\frac{4L_4(0)}{\lambda}
                  (-rS-1/2)(-rS-\lambda/2).
\]
Substituting \(v=f(u)\) gives an exact degree-nine numerator. Its gcd with the degree-four numerator of \(f(f(u))-u\) is one. No forbidden denominator is added by using this rational-function simplification.

## Replay

Run `python check_double_star.py`, `python check_star_arithmetic.py`, and `python check_even_shared_arithmetic.py`. Tested with SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticEndStars.lean) checks three small ring identities on Lean/Mathlib 4.36.0; no end-to-end native theorem is asserted. All exclusions are over characteristic zero.
