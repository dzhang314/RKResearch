# Regular exceptional star-front actual hole six: early anchor rank loss excluded

Over a characteristic-zero field use the [corrected ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md): the affine reverse numerator and the genuine quintic mixed numerator share their actual ordinary zero at physical six, with \(H(r)\ne0\) in the continued quartic. The nine nonfirst physical clocks are distinct and the ordinarily silent clock \(\zeta\) is actually reverse-live. In this packet the front is star, \(y=c_5/\gamma=(3s-1)/2,\ s=c_4/\gamma,\ h_5\ne H_4(y)\), and the fifth slope \(U\ne0\) (see the [zero-pivot](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-zero-pivot-closed/README.md) and [finite-localization companions](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-regular-finite/README.md)). We exclude **the entire early anchor rank-loss case**, not the entire exceptional branch. All six \(\zeta=2,3,4,5,7,8\) placements and all actual rear phases are included since no rear condition is imported.

Write \(a,b=2\pm\sqrt2\) for the normalized first two distinct zero clocks, and \(h_a=(a-1)/2,\ h_b=(b-1)/2\), both nonzero. Their actual early profile equations read
\[
 \alpha L_4(\gamma a)+\beta K_3(\gamma a,r)=h_a,\qquad
 \alpha L_4(\gamma b)+\beta K_3(\gamma b,r)=h_b .
\]
Here \(H=\alpha L_4+\beta K_3\) as usual; the determinant of those two coefficient columns is the early anchor \(\Delta\). If \(\Delta=0\) and the equations hold, Cramer's two numerators vanish with no division. Equivalently both interpolation slopes are zero:
\[
 L_*=\frac{L_4(\gamma b)/h_b-L_4(\gamma a)/h_a}{b-a}=0,\qquad
 K_*=\frac{K_3(\gamma b,r)/h_b-K_3(\gamma a,r)/h_a}{b-a}=0 .
\]
Even if one whole profile column vanishes these equalities follow by consistency. Both are rational polynomials, independent of the ordering of the two star clocks by conjugacy. The replay computes their full exact forms. In particular
\[
 L_* = 2(1400\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1),\qquad \deg_r K_*=3 .
\]

In the case \(U\ne0\) the [finite-localization companion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-regular-finite/README.md) constructs the three paid moment minors \(B_{01},B_{02},B_{12}\) and the genuine hole-six polynomial \(T\), all of degree at most five in \(s\). Its construction uses literal \(h_6=0\), the actual \(y\), and \(\eta U=V\), not inversion of the early anchor. These four equations remain necessary in this early-rank-loss stratum.

Modulo 1009 the monic quadratic-clock-profile slope polynomial \(L_*/\operatorname{lc}(L_*)\) retains degree four and is irreducible. Over its field the exact \(r\)-parent \(K_*\) retains degree three and its monic normalization is irreducible. Over that entire degree-twelve residue field the four polynomials \(B_{01},B_{02},B_{12},T\) retain full \(s\)-degree five and their common gcd is one. In any actual characteristic-zero candidate, the degrees and leading units first make \(\gamma\) and \(r\) algebraic and integral at a prime over 1009 and then do the same for \(s\). Thus its scalar coordinates would reduce in the full computed fibers, contradicting the gcd. This argument uses no reduction of a hidden tableau or of an unlicensed denominator.

Replay `python3 check_early_rank.py` with `sympy==1.14.0` and `python-flint==0.9.0`. The file is standalone and checks the exact rational interpolation slopes, the full degree-preserving tower, and the four necessary polynomial gates. This is source-level arithmetic, not new native Lean verification. The residual exceptional star sixth hole with \(\Delta\ne0\) remains separate, and the unrestricted strict SDIRK8 interval remains **10–11**.
