# Only the \(F_3\) fiber remains in the live cubic DIRK11/13 fourth-clean chart

**Result.** In the exact normalized live cubic chart of the
[fourth-clean packet](../dirk11-thirteen-invisible-six-cubic-live-fourth/README.md),
every profile must satisfy \(F_3(s)=0\), with the same notation
and genuine rooted-order hypotheses. Thus at most six profile
pairs \(s,r\) remain over any fixed ordinary clock configuration,
not eighteen. This removes the two auxiliary discriminant and
contact factors as independent escape branches. No unrestricted
numerical DIRK11 bound changes; the real interval stays **13–14**.

Use \(m=Y^2+rY+s\) with \(r,s\ne0\); all three old distinct
nonzero roots of \(R_3=Y^3+c_2Y^2+c_1Y+c_0\) have live \(m\),
and \(c_0\ne0\). The necessary two polynomials are the quadratic
\(\mathcal D(r,s)=c_0r^2+d_1(s)r+d_0(s)\) and the reduced
linear \(\mathcal A(r,s)=L(s)r+M(s)\) of the prior packet.
Their resultant in \(r\), up to the fixed live scalar from that
packet, is \(F_1(s)F_2(s)F_3(s)\).
The entire genuine affine-slope-\(-1\) chart is also already
excluded. The following argument works over any characteristic-zero
field once these normalized inputs hold.

## 1. The two exact alternatives and the derivative gate

Define \(r_c=c_2-c_0/s\). At \(F_2=0\), \(r_c\) is an exact
common root of \(\mathcal D,\mathcal A\). It is a forbidden contact:
\(F_2=(c_0^{-1}s^3) R_3(-c_0/s)\), and when \(F_2(s)=0\)
the monic \(m=Y^2+r_cY+s\) is the quadratic factor of
\(R_3\) left by this old root. Thus it zeroes on the other
two old roots. Moreover the three roots of \(F_2\) are the
three pair-products of distinct nonzero old roots, so
\(F_2'\) is nonzero at each candidate on that factor.

At \(F_1=0\), \(r_-=15r_c/16\) is an exact common root
of \(\mathcal D,\mathcal A\), even when \(r_-=0\).
If it were the actual \(r\), then \(r\ne0\) and the
two affinity coefficients
\[
 \ell_0 s=c_0 t,\qquad
 \ell_0+t(r-c_2)=r/12,\qquad t=\ell_1-1/4
\]
would give \(t=-5/4\), i.e. the excluded \(\ell_1=-1\).
The replay checks both claimed common-root identities by
substitution and exact remainder, with only live \(c_0,s\)
and rational scalar denominators.

The intersection \(F_1=F_2=0\) cannot be actual. If \(r_c=0\),
then \(c_2s=c_0\), so \(F_2=0\) implies \(s=c_1\) and
\(F_1=16s^3\ne0\). Otherwise \(r_c,15r_c/16\) are
two different roots of the quadratic \(\mathcal D\);
each is a forbidden actual root as just shown.

If \(F_1\) or \(F_2\) vanishes at an actual pair, its
forbidden root and the different actual root both solve
the same affine equation \(L(s)r+M(s)=0\). Thus \(L=M=0\)
at that \(s\). The formal resultant of a quadratic and a
linear polynomial, treated as the degree-two expression
\[
 c_0 M^2-d_1 LM+d_0 L^2,
\]
and its formal first derivative in \(s\) both vanish there.
All ordinary clock parameters are held fixed in this
differentiation. The exact product \(F_1 F_2 F_3\)
therefore has zero first derivative too. In the \(F_2\)
branch we have \(F_2'\ne0,F_1\ne0\), hence \(F_3=0\).
In the \(F_1\) branch we have \(F_2\ne0\), hence either
\(F_3=0\) or \(F_1'=0\). No derivative of a chosen candidate
root or a field ordering is invoked.

## 2. The repeated \(F_1\) exception

If \(F_1=F_1'=0\), the exact cubic discriminant has
\(c_0^2\) times the following other factor:
\[
 5832c_0^2-3240c_0c_1c_2+675c_0c_2^3
      +640c_1^3-150c_1^2c_2^2.
\]
Only \(c_0\ne0\) is discarded. Substitute the actual
Jacobi quartic and cubic deflation in \(B,V\), clearing
the live \(J_4(B)\) factor. The exact coefficient content
removed from the cubic pseudo-remainder has precisely
\(J_4(B)^3\); its resultant against the ordinary quartic
has primitive factors \(J_4(B)^7\) and a degree-48 factor.
The quartic is already a live Jacobi guard. This argument
does not presume that the \(V\)-projection or derivative
polynomials keep a leading coefficient at each exact clock.

In the whole degree-48 clock algebra modulo 101, the
ordinary quartic/cubic linear cofactor pivot for \(V\) and
the \(F_1,F_1'\) linear cofactor pivot for the repeated \(s\)
are units. With those substitutions, \(c_0 L(s)\) is
also a unit. But the only live alternate required \(L=0\).
This rules out the remaining repeated \(F_1\) exception.

Run `python3 replay.py` with SymPy. The source imports
the sibling fourth-clean projection and old-pair and constant
arithmetic; `--project`, `--old-pair`, and
`--arithmetic` can override scratch locations.
All exact denominators and removed nonconstant factors are
checked. The finite-free lift over \(\mathbb Z_{(101)}\)
is confined to the exact monic clock algebra, not any unknown
tableau, weight, or ghost. Each multiplication inverse is
verified in the full residue quotient before the lift.

Finally \(F_3\) has nonzero constant \(-3V^2c_0^2\),
thus degree at most three, not identically zero even when
its leader vanishes. The quadratic \(\mathcal D\) contributes
at most two \(r\)'s per \(s\), giving the stated six-profile
bound. These are not realized tableaux.
