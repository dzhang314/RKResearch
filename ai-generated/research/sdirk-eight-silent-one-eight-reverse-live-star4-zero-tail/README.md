# The centered star tail cannot vanish identically at a regular silent fourth

Consider the [constant nine-site numerator](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md) with eight ordinary distinct clocks, actual nonzero reverse read at the extra ordinarily silent stage and its separate clock, sole physical first quadratic-defect stage ordinarily silent, and genuine degree-five cubic profile. Work over a characteristic-zero field. On the regular star-front/star-rear chart with ordinarily silent **physical fourth**, the [centered tail](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md) is \(A+Bv^2=0\). This packet excludes the entire identically zero branch \(A=B=0\); the \(B\ne0\) chart is separate. The unrestricted bound remains **10–11**.

Let \(x=1-\gamma,m=1-2\gamma\), and for the actual cubic profile write
\[
 H=aL_3+bL_4+cL_5,\qquad
 H(m+\gamma v)=\sum_{j=0}^{5}h_jv^j.
\]
Here \(c\ne0\). Before dividing its forbidden padding the centered tail is
\[
 (1-v)H(m-\gamma v)-(1+v)H(m+\gamma v)+2v(2-v^2)H(x).
\]
If \(A=B=0\), this polynomial vanishes identically. The two top nontrivial coefficient equations are \(h_4+h_5=0\) and \(h_2+h_3+H(x)=0\), the constant odd coefficient following by their sum and \(H(x)=\sum h_j\). The first yields \(5b=(162\gamma-45)c\), since \(\gamma\ne0\). Inserting that into the second gives
\[
 5Q(\gamma)a+8P(\gamma)c=0,
 \quad Q=1-12\gamma+60\gamma^2-120\gamma^3,
\]
\[
 P=-5+114\gamma-1155\gamma^2+6270\gamma^3-17010\gamma^4+17640\gamma^5 .
\]
The exact gcd of \(Q,P\) is one; \(c\ne0\) therefore forces \(Q(\gamma)\ne0\) in this branch. The homogeneous profile is proportional to
\[
 H_g=-8P L_3+(162\gamma-45)Q L_4+5Q L_5 .
\]
For the two actual normalized star literal clocks \(A_0=2+2t,B_0=2-2t\), \(2t^2=1\), and amplitudes \(H_a=(A_0-1)/2,H_b=(B_0-1)/2\), the required literal agreement is
\[
 H_b H_g(\gamma A_0)-H_a H_g(\gamma B_0)
 =-36t(18\gamma-5)Q(\gamma)
 (1400\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1).
\]
The exact replay checks these coefficient and factor identities. Cancel only \(Q\ne0\) and the known scalar, leaving degree five in \(\gamma\).

Normalize \(H_g\) by the actual first literal amplitude \(H_a\). Its scale denominator \(H_g(\gamma A_0)\) is nonzero at any candidate, and is also tested as a unit on the entire reduced diagonal. The actual fourth equation is \(H(\gamma s)=H_4(s)\). Divide the two exact padded earlier roots \(s-A_0,s-B_0\), the true forbidden collisions, to obtain the full monic cubic. The true affine reverse root is the actual fourth clock \(q=\gamma s\). With \(w=v^2\), its two rear comparisons imply the even average
\[
 G(w)=(x-q)(h_0+h_2w+h_4w^2)-(2-w)(m-q)H(x)=0.
\]
The quadratic leading value is nonzero at a genuine candidate since \(h_4=-h_5\ne0\) and \(x\ne q\). It is tested as a unit over the full reduced fourth cubic before retaining the complete monic quadratic.

Use the ordinary five-peg nodal product
\[
 E(X)=(X-\gamma A_0)(X-\gamma B_0)(X-x)
         \big((X-m)^2-\gamma^2 w\big).
\]
The unordered pair is used without choosing a square root. The four degree-one through degree-four coefficients of \(H W_{EX^j}-EX^j W_H\), \(0\le j\le3\), give the same required nodal determinant at scalar precision seven. At \((1129,t=203)\), the degree-five diagonal retains its complete three components of degrees \(1,1,3\); the actual fourth cubic and gap quadratic retain all leading values in every component. The required determinant is a unit in each full monic tower, so the branch is impossible without an actual fifth condition or any claim of precision eight or nine.

Install sympy==1.14.0 and python-flint==0.9.0, and run **python3 check_star4_zero_tail.py** with the stated sibling helpers. The [Lean coefficient identities](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveStar4ZeroTail.lean) compile on Lean/Mathlib 4.36.0; the literal chronology and finite proof remain source-level.
