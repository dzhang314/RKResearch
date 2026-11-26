# A rational omitted-stride filter at the odd endpoint

For \(g\ge1\) surviving gaps at order \(p\ge2g+1\), the monic centered
gap polynomial P has the form \(Q_g+\alpha Q_{g-1}\):
orthogonality through tests of degree \(g-2\) follows from the
one-step moments. This section adds a source-free necessary
condition when the scale is **rational**. At odd saturation a
merely real scale is not shown rational; see the separate even
saturation argument for that distinction.

Take primitive integer stride labels \(k_i\) (divide by their
common positive gcd and absorb it into \(\lambda\)), so at least
one is odd. Let \(u_i=2\lambda k_i-1\) be the roots of P and
\(t=v_2(2\lambda)\). Then \(\alpha=-\sum_i u_i\).

* At most one root \(u_i\) is not 2-integral. In fact, if j≥2
  roots have negative valuations, the coefficient \(e_j\)
  has a unique term of least valuation, the product of
  those roots. Its valuation is strictly less than the smallest
  root valuation, whereas all coefficients of
  \(Q_g+\alpha Q_{g-1}\) have valuation at least
  \(\min(0,v_2(\alpha))\), which is at least that minimum.
* If \(t<0\), exactly one stride has \(v_2(k_i)<-t\).
  In addition the number with \(v_2(k_i)=-t\) is
  \((g-1)\bmod2\). To see the second statement, the unique
  nonintegral root has valuation t and so does α; reduce
  \(\alpha^{-1}P\) modulo 2. The exceptional root factor
  contributes a unit constant, and the other factors reduce
  exactly to \(Q_{g-1}\), with zero-root multiplicity
  \((g-1)\bmod2\).
* If \(t=0\), g must be odd and there is exactly one odd
  stride. Indeed odd strides give roots 0 mod 2, even
  strides roots 1. For even g the parity of α either gives
  the all-ones-root case (excluding an odd stride), or an
  irreducible \(u^2+u+1\) factor. For odd g the reduction
  has either zero or exactly one zero root. This follows
  from \(Q_n\bmod2=u^{n\bmod2}(u+1)^{2\lfloor n/2\rfloor}\).

In particular two or more odd primitive strides force
\(t\ge1\), equivalently \(v_2(\lambda)\ge0\). This is a
condition on the omitted-stride pattern and its scale, not
an estimate of the stage or even the occupied width.

## Especially simple all-odd filter

If all g primitive strides are odd and g≥2 then \(t\ge1\).
Moreover:
\[
 \begin{cases}
 g=2m:     & s_2(m+1)=2,\\
 g=2m+1:   & s_2(m+1)=1,
 \end{cases}
\]
where \(s_2\) counts binary ones. Thus many all-odd, nonconsecutive
patterns cannot even reach the odd endpoint. The same bitcount
condition holds for any stride pattern if \(v_2(\lambda)\ge1\).

For the proof, the parity of \(Q_g,Q_{g-1}\) gives
\[
 2Q_g(1)=P(1)+(-1)^gP(-1),\quad
 P(1)=2^g\prod_i(1-\lambda k_i),\quad
 (-1)^gP(-1)=(2\lambda)^g\prod_i k_i .
\]
When \(\lambda\) is even at 2, the first product has valuation g
and the second at least 2g. If \(\lambda\) is a 2-adic unit and
all strides are odd, the roles swap. Thus \(v_2(Q_g(1))=g-1\).
From the exact endpoint value in the saturation proof and
\(v_2\binom{2n}n=s_2(n)\) (expand the floors in factorial valuations),
\[
 v_2(Q_g(1))=
 \begin{cases}
 g+1-s_2(m+1),&g=2m,\\
 g-s_2(m+1),&g=2m+1.
 \end{cases}
\]
Equating gives the claimed filter.

More generally for a 2-adic unit \(\lambda\) and o odd strides,
the two endpoint products yield
\(v_2(Q_g(1))\ge g-1+\min(o,\sum_i v_2(k_i))\).
For odd g this already rules out mixed parity at unit scale;
for all g it combines with the exact popcount value.
All these conditions are necessary for this reduced moment
problem, not sufficient conditions for a true tableau.

Pure mathematics; no repository/source access, Lean, compiler,
gate, old interval, or fixed-pattern spanning analysis.
