# Corrected actual hole seven, star front cubic fifth: zero sixth-clock slope excluded

Work in the [corrected affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) over a characteristic-zero field. The only quadratic defect is ordinarily and reversely silent physical one; the remaining nine clocks are distinct, with eight ordinarily active and the extra ordinary-silent \(\zeta\) actually reverse-live. The common root \(r\) of the affine and genuine quintic is ordinary, here **actual physical seven**; its true cubic amplitude is zero but \(H(r)\ne0\). The front is star and actual \(h_5=H_4(y)\) with \(y=c_5/\gamma\). This packet excludes exactly the zero-slope case of the literal sixth-clock equation below, all \(\zeta\) and all rear phases.

Use the [pure-four clock bridge](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole67-clean-bridge/README.md) and the [literal star cubic-fifth proof](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-cubic-closed/README.md) only through the fourth and fifth gates, not its hole-six equation. Put \(s=c_4/\gamma\), \(D(Y)=d_2Y^2+d_1Y+d_0\), and let \(\ell_L(Y)=\ell_0+\ell_1Y\), where \(\ell_0=4(1-2d_0)/3,\ \ell_1=8(d_2-70\gamma^4)\). The literal fifth's extra tap from stage four is zero when its amplitude is cubic, so actual \(D(y)=D(s)\ne0\). By distinctness \(y\ne s\) and coprimality of \(d_1,d_2\), \(d_2\ne0,\ y+s=-d_1/d_2\). Thus
\[
 H(\gamma Y)=H_4(Y)+\lambda (Y^2-4Y+2)(Y-s)(Y-y),\qquad \lambda\ne0 .
\]
Set \(p=sy\), so \(D(s)=d_0-d_2p\).

The actual sixth is **not** the hole. Set \(v=c_6/\gamma\) with true amplitude \(h_6=H(c_6)\), even if this is \(\zeta\). The general paid-sixth equation with cubic prior amplitudes is
\[
 9(L_4(\gamma v)-\ell_L(v)h_6)
 +D(s)\left(v^4-16v^3+72v^2-96v+24+(8v-56)h_6\right)=0.
\]
At \(h_6=H_4(v)\) the left side is \(9d_2(Y^2-4Y+2)(Y-s)(Y-y)\big|_{Y=v}\), using \(y+s=-d_1/d_2\). This is an exact polynomial identity; each predecessor factor is truly nonzero at sixth. Substitute the actual \(H(c_6)\) and remove that true product. The actual sixth clock therefore obeys
\[
 \lambda\big[(8D(s)-9\ell_1)v-56D(s)-9\ell_0\big]+9d_2=0.       \tag{1}
\]

## Full zero-slope exclusion

Write \(C_3=8\gamma^3H_4(X/\gamma)\), \(E_2=X^2-4\gamma X+2\gamma^2\),
\[
 8\gamma^3H(X)=C_3+\theta E_2(d_2X^2+\gamma d_1X)+\chi E_2,\quad
 \theta=8\lambda/(\gamma d_2)\ne0,\quad \chi=8\lambda\gamma p.
\]
If the slope in (1) is zero, then \(D(s)=9\ell_1/8\ne0\) and its constant part gives \(\theta\gamma(\ell_0+7\ell_1)=8\). In particular \(\ell_1,\ell_0+7\ell_1\ne0\). Also \(\chi=\theta\gamma^2(d_0-9\ell_1/8)\). Clear the true factor \(\gamma(\ell_0+7\ell_1)\) from the quartic representative. It now equals
\[
 \widehat H=\gamma(\ell_0+7\ell_1) C_3+
    8E_2\left(d_2X^2+\gamma d_1X+\gamma^2(d_0-9\ell_1/8)\right),
\]
a profile determined by \(\gamma\) alone. Its three paid moments \(I((X-r) X^j \widehat H)=0\), \(j=0,1,2\), are affine in \(r\), each of bidegree \((1,8)\) in \(r,\gamma\). Their exact pairwise \(r\)-resultants have degree sixteen in \(\gamma\) and their common monic gcd is \((\Pi/1400)^2\), where \(\Pi=1400\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1=\ell_1/2\). This forces \(\ell_1=0\), contradicting \(D(s)\ne0\). The gcd is taken only after all projections into the single variable \(\gamma\), and no leading drop, actual visibility, or rear is discarded.

Replay `python3 check_zero_slope.py` with `python-flint==0.9.0`, standalone. The [native scalar module](../../lean/RKCert/ReviewedNative/SDIRK8HoleSevenCubicSixthScalar.lean) proves the homogeneous zero-slope coefficient implication and visibility-free terminal combination, and the [Lean/Mathlib 4.36 transcript](lean-4.36.0-replay.txt) verifies both. The fixed-profile reconstruction and exact diagonal are source-level. This scope itself neither excludes the nonzero sixth slope nor changes the unrestricted **10–11** interval.
