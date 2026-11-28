# Four finite old-profile closures in live beta-zero DIRK11/13

**Result.** Over characteristic-zero fields, the live
normalized no-late invisible-six DIRK11/13 chart with
\((\alpha,\beta,\gamma)=(1,0,5)\) has no candidate in any
of these four old profiles: \(m=1\), \(m=Y^2\),
\(c_2s=c_0\) with \(rs\ne0\), and the lost \(F_n\)
ratio \(c_1+6s=0\). The mixed \(r=0\) profile
was already excluded by the
[slope-minus-one bridge and five-prefix proof](../dirk11-thirteen-invisible-six-alpha-one-slope-minus-one-beta-zero/README.md).
This does not exclude the remaining alternate old profiles
or improve the unrestricted real interval **13–14**.

## 1. True literal ingress at the fifth ordinary row

In the reverse prefix \(T,v,u,w,z,V,B\), \(B\) immediately
follows \(V\) and is the fifth ordinary row. The
[universal pivot](../dirk11-thirteen-invisible-six-alpha-one-beta-zero-universal-fifth/README.md)
forces \(d_B=0\) and live \(D_B\) with no old ratio or
separation assumptions. In particular \((ND)_B=0\),
since every preceding entry of the matched column is zero.
That proof uses the paid graded commutator before any arithmetic
with the old fit; it does not assume a fixed chronology of the
five late reverse ghost clocks.

Use the genuine affine first forward clean row \(J_b(t)=0\)
and the two actual reverse primitive rows \(H_V(t)=H_B(t)=0\)
from the [beta-zero carrier proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-beta-zero/README.md#1-two-literal-primitive-reads-without-a-middle-ghost).
Their derivation uses only the universal diagonal, paid old
primitive fits, and literal absence of a middle ghost. It
does not use direct \(F_n\), \(V\ne z\), a live old ratio,
or a nonzero leader of the affine row. In unscaled units and
in the common \(n\)-adjugate gauge,
\[
 U=\widehat M+tR,
 \qquad J_b(t)=\int_B^1(1-Y)U(Y)\,dY=j_0+j_1t .
\]
With \(H_C=h_{C0}+h_{C1}t+h_{C2}t^2\), two necessary scalar
rows on the same old clock algebra are
\[
 j_1^2h_{C0}-j_0j_1h_{C1}+j_0^2h_{C2}=0,qquad C=V,B .
\]
These are the homogeneous affine pins; even \(j_1=0\)
requires no division. The actual formulas for \(Q^\#\),
\(L^\#\), and \(H_C=U(C)(I Q^\#)(C)-C J_4(C)L^\#(C)\)
are the same as in that source. The choice to use an
unscaled reverse variable in this replay means the upper
endpoint is 1 in the reflected primitive.

## 2. Exact old profile fields and unit pivots

Write \(R=Y^3+c_2Y^2+c_1Y+c_0\).
The [old-profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md)
and [finite old fit proof](../dirk11-thirteen-invisible-six-alpha-one-live-cubic/README.md#4-exact-finite-clock-fields-and-rank-without-assuming-t-integral)
give the following necessary ordinary equations and exact
profile reconstructions before the middle count is used:

* \(m=1\) forces \(c_2=z=0\); \(m=Y^2\) forces \(c_1=z=0\).
* The mixed contact \(c_2s=c_0\), \(rs\ne0\), has
  \(c_2\ne0\), \(s=c_0/c_2\),
  \(r=(2c_0+c_1c_2)/c_2^2\), \(z=-c_2/4\), and
  \(12c_0^2+8c_0c_1c_2-6c_0c_2^3+c_1^2c_2^2=0\).
  Use the cleared old profile
  \(c_2^2Y^2+(2c_0+c_1c_2)Y+c_0c_2\);
  no residue rank divides by \(c_2\).
* The lost ratio \(F_n\) forces \(c_2=0\), \(s=-c_1/6\),
  and the old affinity becomes
  \(c_0(r^2-3s)+4rs^2=0\).
  Adjoin \(r_*=c_0r\) by the monic quadratic
  \(r_*^2+4s^2r_*-3s c_0^2=0\), retaining the full rank-two
  algebra even if it is not split or reduced.
  Use cleared \(m=c_0Y^2+r_*Y+c_0s\) and
  \(p=c_0r_*, q=-4sr_*-3c_0^2\) for \(z=p/q\),
  the actual live old scalar denominator. No lost \(F_n\)
  ratio is inverted.

Deflate the actual Jacobi pencil at \(V\) and let
\(F(B)=0\) be its ordinary quartic with coefficient leader
\(132J_4(V)\ne0\). Deflating at \(B\) gives the
cleared old coefficients \(C_i=132J_4(V)c_i\).
Use \(G(B)=C_2\) or \(C_1\) for the monomial and lost-ratio
profiles, and the cleared mixed equation for the contact.
The latter uses the primitive pseudo-remainder modulo
\(F(B)\), removing only rational constants and
\(J_4(V)^3\), live on the true ordinary clock.
Taking the exact resultant in \(B\) gives one non-forbidden
irreducible clock factor \(f\) for each profile:

| Profile | Clock-factor degree and constant | Removed exponent of \(J_4\) |
|---|---|---:|
| \(m=1\) | 12, 54123 | 2 |
| \(m=Y^2\) | 12, 16227 | 3 |
| \(c_2s=c_0\) | 48, 41521530286435 | 7 |
| lost \(F_n\) ratio | 12, 54123 | 2 |

The penultimate exact subresultant is linear \(h_1B+h_0\).
**proof.py** checks \(h_1\) is a unit in \(\mathbb Q[V]/f\)
by an exact inverse, and additionally computes the actual
ordinary \(\gcd(F,G)\) over that number field. Its monic
result is exactly \(B+h_0/h_1\) even after specialization;
every Gaussian/polynomial-division inverse is checked.
Consequently the lift of the distinguished ordinary \(B\)
does not discard a hidden leading-loss branch. At residue
level the script also checks the inverses of \(h_1,J_4(V)\)
and rebuilds the two exact synthetic divisions at \(V,B\).

## 3. Split-free pin exclusion

Evaluate the two necessary pins in the finite clock algebra.
The ordinary cases are dimension one over \(\mathbb Q[V]/f\);
the disappearance of the original \(F_n\) ratio retains
dimension two. The old \(m\) inverses for the formulas are
implemented by one common multiplication adjugate, not by
separate inverses or divisions on a candidate.

| Profile | Residue prime | Residue degree | Joint rank / exact dimension |
|---|---:|---:|---:|
| \(m=1\) | 103 | 4 | 1 / 1 |
| \(m=Y^2\) | 103 | 12 | 1 / 1 |
| \(c_2s=c_0\) | 101 | 2 | 1 / 1 |
| lost \(F_n\) ratio | 103 | 4 | 2 / 2 |

These are genuine reductions of the same finite-algebra
multiplication columns. The leading coefficient of \(f\) and
ordinary inverted formula denominators are units in the
selected residue, checked explicitly. Reduction can be taken
in the localization inverting those checked denominators;
no integrality is assumed of the unknown tableau or its
true carrier. Nonzero residue minors give full exact rank.
Thus the ideal generated by the two pins contains 1 in the
exact algebra, contradicting any field evaluation that kills
them. In this replay the first pin already attains each stated
rank once the old profile is fixed. The second corroborates
the literal opposite condition; no false rank-independence is
needed. The same residue check verifies full multiplication
rank of the affine leader, old adjugate scale, and \(q\),
though none is divided by in making the pin.

Replay using `bash verify.sh` with SymPy and python-flint 0.9.
This is an exact written and executable source proof. The
local coefficient/monic-scale adapter is Lean-checked in
the preceding universal pivot packet, not an end-to-end
kernel-checked DIRK lower bound.
