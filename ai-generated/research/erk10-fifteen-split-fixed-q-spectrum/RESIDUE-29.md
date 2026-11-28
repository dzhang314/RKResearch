# Nonlinear exclusion on an entire rational 29-adic class

In the rational split-host ordinary-pair width-eleven
chart, write \(c,g,R\) in the normalized reverse
ordinate \(y=1-x\). **No rational chart survives**
whenever these three numbers are 29-integral with
residues
\[
                         (c,g,R)\equiv (15,20,22)
                                             \pmod{29}.
\]
This does not assume \(a,b,d,e,\tau=de\) are
29-integral. It is a residue-class exclusion,
not a claim about all rational tail triples,
all coefficient fields, or an unrestricted
stage bound. The proof needs only the necessary
raw and nonlinear data common to both split
old hosts, not the fixed-\(q\) sufficiency construction.

## Why the coefficient reductions are uniform

Use
[the symmetric head solve](HEAD-SYMMETRY.md) and
[the true reciprocal filter](RECIPROCAL.md).
The center representative is
\((c,g,R)=(1/2,2/3,1/4)\),
where \(h=19/20,\ f=22/39\).
The two late reconstruction denominators
reduce to \(4,28\) modulo \(29\);
\(cL_4(c)\), \(f(f-c)\), and
\(\widehat A_0(1)\) reduce to \(20,2,2\).
All other elementary denominators in the
exact calculation come from these, nonzero clock
factors, or the small fixed moment denominators:
\(c,f,g,h,R\) reduce to \(15,8,20,14,22\),
so needed distinctness with \(0,1\), \(T_3(0)\ne0\),
\(P_3(0)\ne0\), and the other displayed inverses
are also units. The identity \(P_3(0)=JM(c)/(cL_4(c)\,c)\)
makes the \(P_3(0)\) check explicit.
Thus all the polynomial coefficients in the
cleared \(\tau\) scheme specialize uniformly
throughout the stated rational residue class.
In particular \(A(1)\ne0\) and the ordinary
singleton reciprocal-score guards apply.

The actual two-row pivot polynomial reduces to
\[
                        21\tau^2+22\tau+19
\]
modulo \(29\), projectively rootless.
For any rational \(\tau\), clear the common
square denominator to reduce it projectively.
This proves the pivot does not vanish even
for a nonintegral \(\tau\).
The split-head sum/product and \(D_7\)
coefficient formulas are therefore valid.

## The homogeneous degree bound

The pivot has degree at most two in \(\tau\).
With \(D_{\rm num}=\Delta D_7\), the coefficients
of \(D_{\rm num}\) have degree at most three:
the numerator head quadratic has coefficients
of degree at most two, and the inner
\(d,e\) quadratic is affine in \(\tau\).
For \(0\le j\le4\), the cleared coefficient
column \(\Delta^{j+1}\mathrm{rem}_{D_7}
(y^j\widetilde\mu)\) has degree at most \(3+2j\)
in \(\tau\).
One way to see this without a leading-coefficient
cancellation assumption is to write
\[
 \mu_j(y)=I_z\!\left[
 z(z-1)(z-c) z^j\frac{D_7(z)-D_7(y)}{z-y}\right].
\]
It is linear in \(D_7\)'s coefficients, and
\[
 \mu_j(y)-y\mu_{j-1}(y)
       \equiv I_z[z(z-1)(z-c)z^{j-1}D_7(z)]
                                                \pmod{D_7}.
\]
Hence the reduced \(y^j\mu_0\) differs from
\(\mu_j\) by a degree-at-most-\(j-1\) polynomial
whose coefficients are also linear in \(D_7\).
Its common denominator is \(\Delta\), proving
the claim after multiplication by
\(\Delta^{j+1}\).
The final column \(y\widehat A_0^2\) is
independent of \(\tau\).
Therefore every cleared six-row minor has
universal degree at most
\[
                          3+5+7+9+11=35 .
\]
This upper bound is uniform, not a degree
guess from the center representative.

## Only two minors are needed

Index the coefficient rows by \(0,\ldots,6\).
For the two minors omitting row \(0\) and
row \(6\), respectively, the exact residue
replay gives:

| Omitted row | Finite zeros modulo 29 | Leading coefficient at degree 35 |
|---|---|---|
| 0 | \(2,7,13\) | \(0\) |
| 6 | \(0,24\) | \(28\) |

There is no common finite root, and at the
projective point at infinity the second
minor is nonzero. If a rational tableau
existed, both exact minors would vanish
at \(\tau=de\) by the actual nonlinear
host-defect congruence. Clear a common
degree-35 denominator using a primitive
projective representation of \(\tau\);
the two homogeneous minors still vanish.
Reduction modulo \(29\) contradicts
the displayed finite or infinite check.
This does not replace an actual rational
root by an affine residue when its
denominator is nonunit.

## Replay and Lean

    python3 -B residue29.py | diff -u residue29-audit.txt -

The accompanying core Lean source checks
the projective quadratic pivot and the
two finite minor-polynomial evaluations
plus the infinity coefficient.
The rational-to-residue coefficient
argument and exact determinant arithmetic
are mathematical/replayed, not a native
end-to-end tableau proof.
