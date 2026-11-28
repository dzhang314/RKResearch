# The first ghost cannot share an old ordinary clock in the live direct Fn chart

**Result.** In the normalized no-late invisible-six DIRK11/13 chart,
assume a live reciprocal multiplier, \(\alpha=1,\ \beta=1\) or 2,
and the direct \(F_n\) old profile. The first reverse ghost clock
\(z\) cannot equal any of the old three ordinary clocks. There is
no extra nonzero-diagonal or ordering assumption on the field.
The remaining direct \(F_n\) cases are not excluded here.
Unrestricted real DIRK11 stays **13–14**.

Use the established old coefficients \(R=Y^3+c_2Y^2+c_1Y+c_0\)
and \(m=Y^2+rY+s\). The
[small-contact proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-small-contacts/README.md)
excludes \(r^2=3s\) and verifies that \(2r^2-9s\), \(r^2-6s\),
and \(\Delta=-c_2r^2+6c_2s+r^3-7rs\) are live on the
remaining direct chart, in addition to the original live \(r,s,c_0\).
In the same exact old coordinates,
\[
 R(z)=-\frac{s^2(2r^2-9s)(5r^2-24s)\Delta}
                 {(r^2-6s)^3(r^2-3s)}.
\]
Thus \(R(z)=0\) implies \(s=5r^2/24\), \(z=-5r/6\) and
\[
 H_r=5r^2-5c_2r+4c_1=0,\qquad
 F_r=100r^3-75c_2r^2+216c_0=0.
\]
**old-contact.py** independently verifies the complete rational factor
and those three substitution identities. No ordinary clock difference
involving \(z\) has been divided by.

The exact resultant in \(r\) is \(1000 W\), where
\[
 W=5832c_0^2-3240c_0c_1c_2+675c_0c_2^3+
       640c_1^3-150c_1^2c_2^2 .
\]
The penultimate subresultant is
\[
 5400c_0-500c_1c_2+(-2000c_1+625c_2^2)r.
\]
Both assertions are exact coefficient checks. The ordinary
\(B,V\) projection deflates the true nonendpoint Jacobi pencil
first at \(V\), then at \(B\), and clears its live leader
\(132J_4(V)\). The only nonconstant content removed after
pseudo-remainder in \(B\) is \(J_4(V)^3\). The exact ordinary
resultant is a nonzero constant times \(J_4(V)^7 f_{48}(V)\),
where \(f_{48}\) is irreducible of degree 48 with primitive
integer constant term \(349752339173169\).

The exact penultimate subresultant recovers the clock \(B\)
linearly over the full monic degree-48 rational algebra.
The displayed \(r\) subresultant recovers \(r\) there; all used
leaders and fitted inverses are units modulo 103 in the entire
monic residue algebra, and hence in the rational algebra.
This does not require \(z\) distinct from any old root.

Finally apply the three true matched, quintic and commutator
polynomials from the linked small-contact proof, using the exact
first-middle zero diagonal and live affine clock fit. Their carrier
degree caps are \(2,3,4\). The cap-five Macaulay map has rank
**288/288** over the entire degree-48 model modulo 103.
Thus the exact rational map contains 1; a field evaluation
annihilating the three actual gates cannot exist. This is a fixed
rank certificate and never reduces unknown candidate coefficients.

Run **python3 old-contact.py**, **python3 clock.py** and
**python3 rank.py** with SymPy and python-flint 0.9.
This is an exact written and executable source proof; the native
scalar adapter for the common gap-diagonal argument is separate.
