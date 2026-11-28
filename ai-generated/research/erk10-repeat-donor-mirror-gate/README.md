# The older reflected-donor schedule is excluded in a horizon class

This concerns raw order
\((1,2/3,1/3,2/3,C,1-C,\ell_1,\ell_2,\xi)\):
the reflected partner of the first adjustable donor is its
**first receiver**, rather than a later receiver as in the
[successful rational family](../erk10-sixteen-rational-mirror-family/README.md).
In the regular doubled-clock prefix chart this older placement
fails for every rational horizon integral at 19 with
\(\theta\equiv5/2\pmod {19}\).
This includes \(\theta=5/2\), with no assumption on the
19-adic valuation of either rational radius. The conclusion
does not include the successful placement or other schedules.

## The remaining three sites must be symmetric

Let \(t=2X-1\) and use the normalized average on \([-1,1]\).
The first known mirrored pair is at \(t=\pm1/3\),
the donor pair is at \(t=\pm\sqrt U\), and the anchors are
\(t=\pm1\). Write the remaining monic cubic as
\(R(t)=t^3-\sigma t^2+\pi t-\tau\), and put
\(G(t)=(t^2-1)(t^2-U)\).
The only further scalar nodal moment is the average of
\(G(t)(t^2-1/9)R(t)\), and it must vanish.
The early repeated-clock condition forces the cardinal
integrals at the two \(\pm1/3\) sites to agree, so
the average of \(G(t)R(t)\) also vanishes. The evenness
of \(G\) gives two linear equations on \(\sigma,\tau\).
With \(J_i=\int_{-1}^{1} t^iG(t)\,dt/2\), their
determinant is, up to sign, \(J_0J_4-J_2^2\). This equals
\[
   \frac{32}{33075}(21U^2-14U+1).
\]
Its discriminant is 112, not a rational square. Thus
\(\sigma=\tau=0\), and the three distinct rational roots
are zero and a reflected pair.

## Pressure in the two possible alias shapes

Let \(V\) be the remaining normalized squared radius.
The pressure tests vanishing on the two latest adjustment
rows are \(f_4=X(X-1/2)((X-1/2)^2-V/4)\) and \(f_5=Xf_4\).
These are independent of the donor radius \(U\) because
its reflected partner is already the first adjustable
receiver. The unchanged fused terminal density from the
sibling family gives, after multiplying by
\(I=2V/15-2/35\), the respective moments
\[
  \frac{(2V-1)(7V-3)}{1058400},\qquad
  \frac{(3V-1)(7V-3)}{6350400}.
\]
Here \(I\ne0\) and \(7V-3\ne0\) because \(V\) is a
rational square. Clear the same factor \(7V-3\) in both.

The [replay](audit.py) uses the normalized polynomial
functional of the [canonical late-helper packet](../erk10-late-helper/README.md),
cancels the common \(\xi^2\) factor, and verifies the
remaining coefficients are integral at 19 as polynomials
in the horizon. If the alias is the center, the pressure
at \(\theta=5/2\) is a 19-unit times
\[
 45V^2+16V-13.
\]
If the alias is on the reflected pair, write its signed
radius as \(r\) so that \(\xi=(1+r)/2\) and \(V=r^2\).
The pressure is a 19-unit times
\[
 64r^5+372r^4-65r^3-187r^2-21r+13.
\]
Before specializing the horizon the degrees in \(V,r\)
are at most 2 and 5 respectively. The two unit
multipliers at \(5/2\) are \(-375/128,+375/128\).
Consequently reducing any 19-integral horizon in the
same residue class gives exactly the same two projective
nonzero tests. Primitive numerator-denominator coordinates
also cover poles of \(V\) or \(r\) at 19. The
[Lean check](../../lean/RKCert/ReviewedNative/ERK10MirrorScheduleMod19.lean)
certifies both homogeneous forms are nonzero at every
nonzero coordinate pair over \(\mathbb F_{19}\).
It does not assert all rational horizons are excluded.

    python3 -B audit.py
    sha256sum -c sha256.txt
