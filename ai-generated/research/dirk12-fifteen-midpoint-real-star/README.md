# Direct real next-order failure from the unoriented nodal hull

Let \(Y=1-X\) be the reflected clock, \(S\) the monic hull of
the ten distinct live labels, and \(Q\) the actual scalar quadrature.
The two orientations of the repeated reflected root have the same
aggregate weights and hull. Both \((Y-1)^{12}\) and \(Y^2S(Y)\) are
monic of degree twelve. Their difference has degree at most eleven,
where \(Q\) is exact. The actual weighted evaluations of \(Y^2S\)
vanish (each live label is a root and each ghost has weight zero).
Since the integral of \((Y-1)^{12}\) is \(1/13\), the actual scaled
order-thirteen bush defect is therefore
\[
  13 Q\bigl((Y-1)^{12}\bigr)-1=-13\int_0^1Y^2S(Y)\,dY .
\]

For the isolated real \(x,f\) branch in the degree-216 field packet,
write \(S=P_*(Y)(Y^2-sY+p)(Y-u)\). If
\(n_i=\int_0^1Y^iP_*(Y)\,dY\), the enclosed integral is simply
\(n_5-(s+u)n_4+(p+su)n_3-pu n_2\). The directed rational replay
encloses the scaled defect in the open positive interval
\[
  (85680969483153,\;85680969483154)\,10^{-20}.
\]
The computation does not select an orientation, specialize at a
prime, or assume any degree-twelve scalar condition. It uses the
previous independent boxes for the actual real root parameters.

The reviewed Lean theorem
DIRK12MidpointStar.actual_star_defect proves the formula for the
actual reviewed rooted bush when the weighted roots, paid lower
moments, and scalar integral are supplied. The directed rational
enclosure itself is an exact Python receipt, not a Lean computation
here. The source and typed audit were replayed on Lean 4.36.0 with
matched Mathlib, with only the standard axioms. Run verify-star.py
with ai-generated/research as its argument to reproduce the real
interval check from the archived field data.
