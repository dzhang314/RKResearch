# Two alternative first-active clock schedules

This packet concerns the **noncentered, second-active Christoffel
site** in the
[seven-distinct-active, two-zero-weight clock atlas](../strict-sdirk7-two-ghost-mass/README.md).
It supplies two exact arithmetic-suffix finite controls, two
unbounded rational endpoint exclusions, and several exact
first-clock-one fiber exclusions. No rational tableau or global
arithmetic exclusion is asserted. The separate
[reflection obstruction](../strict-sdirk7-mass-reflection/README.md)
does not use these controls.

## Removing the extra forward tap equation

Normalize the diagonal to one. Put \(x=z-e\) for the forward
clock of the second active site and \(x_a\) for the first.
The two forward profiles are
\[
 q(X)=(2-t)X+t-1,\qquad h(X)=(X-1)(X-1-t).
\]
Let \(J\) denote antiderivation from zero in this section.
Because the visible cubic vanishes at \(e\), the second row's
single strict tap to the first active site must simultaneously
pay \(Jq(x)-q(x)\) and \(Jh(x)-h(x)\). Two useful rational
schedules make one of those equalities automatic.

1. **Second helper clock (H2).** Set
   \(t=(2/3)(x^3-6x^2+9x-3)/M(x)\) with
   \(M(x)=x^2-4x+2\), and choose \(x_a=1+t\) instead
   of the earlier \(x_a=1\).
   Then \(Jh(x)=h(x)\) and \(h(x_a)=0\).
   The first pivot \(q(x_a)=1+2t-t^2\) is nonzero rationally,
   and the two-profile minor is nonzero for \(x\ne0,1,3\).
2. **Zero first \(q\)-profile.** Fix instead
   \(t=2(x^2-3x+1)/M(x)\) and
   \(x_a=x(x-2)/(2(x-1))\).
   Then \(Jq(x)=q(x)\) and \(q(x_a)=0\);
   these identities are native. For \(x\ne0,1\), \(q(x)\ne0\)
   and the other row pivot \(h(x_a)\ne0\), because the two
   roots of \(h\) have \(q\)-values \(1,1+2t-t^2\).
   The same two-profile solve can therefore start with \(h\).

Both prescriptions use rational operations wherever their
listed guards hold. A rational clock core must still pay
the mass, three terminal reads, fourth affine read, and seven
distinct nonzero weights. These formulas do not supply the
missing core on their own.

The two literal \(\mathbb F_{19}\) controls in this directory
have the following data. The \(e\) column is physical reflected;
the first active is the first entry in the displayed list.

| Schedule | \((z,u,e,c,t)\) | Active reflected clocks | Eighth-bush residual |
| --- | --- | --- | --- |
| H2 | \(14,5,16,14,2\) | \(11,16,12,14,9,5,1\) | 6 |
| Zero \(q\)-profile | \(15,7,5,4,17\) | \(0,5,12,4,13,7,1\) | 6 |

H2 has \(c=z\) in the finite control. The zero \(q\)-profile
has first reflected clock zero. Both native tableaux check all
85 order conditions, their two-zero mask, the strict unit
diagonal and exact failure at size eight. The standalone tree
replay independently checks every order condition. The following
arithmetic exclusions concern the corresponding rational endpoint
cuts, so these controls cannot be taken as rational lifts.

## Endpoint exclusions and first-clock-one fibers

Put \(r=1/m=2/z,\ \eta=(e-m)/m\), using the atlas kernel \(g\)
and its representer \(H\) in the normalized coordinate
\(r Y-1\). The polynomial necessary equation for another
distinct first root at normalized \(\alpha\), with fourth root
at normalized \(\gamma\), is the Bezoutian evaluation
\[
 \frac{H(\alpha)g(\gamma)-g(\alpha)H(\gamma)}{\alpha-\gamma}=0 .
\]
This is quadratic in \(\alpha\) and in \(\gamma\) separately.
The scripts use its elementary coefficient sum
\[
 \sum_{i>j}(H_i g_j-g_i H_j)
      \sum_{k=0}^{i-j-1}\alpha^{\,i-1-k}\gamma^{\,j+k}
\]
and clear both rational substitutions homogeneously.
The clock equation is \(H(\eta)=0\).
The unknown fourth slope is nonzero on any valid rational
noncentered chart by the
[global arithmetic pivot receipt](../strict-sdirk7-mass-arithmetic-at-five/README.md).

For the **H2, \(c=z\)** cut use \(\gamma=1\) in the
Bezoutian and also impose \(rN-2D=0\) in the affine fourth
equation \(c=N/D\).
The two exact resultants in \(\eta\), obtained by pairing
the opener with each of these equations, have bidegrees
\((27,18),(36,48)\) in \(u,r\).
After removing only allowed nonzero scales, their gcd is
constant. This proves the whole stated H2 endpoint cut empty
over \(\mathbb Q\), not just at a fixed \(u\).

For the **zero \(q\)-profile, first reflected clock 0**
cut, \(x_a=z\).
Thus \(r=4(x-1)/(x(x-2))\), \(\eta=(2-3x)/(x-2)\), and
\(\alpha=-1\). The smallest prohibited values are excluded
directly by the clock and normalization assumptions:
\(x\notin\{0,1,2\}\).
The resultant in \(u\) has degree 192 in \(x\), with
factor degrees \(9,27,36,84\) and multiplicities \(2,2,1,1\).
The factors are projectively rootless modulo \(11,13,11,37\)
respectively. This cut also has no rational point.

For the earlier **first active forward clock 1** schedule
use \(\alpha=1-r\).
The full \(\eta\)-projection, after legal saturation, has
bidegree factors \((36,42)\) and \((9,6)^2\) in \(u,r\).
Only the projection and the following exact rational fibers
are certified, not rational points of the full curve:
\[
 u=-2,-1,0,4,5,6,7,8,9,\qquad x=2,4,5,9.
\]
For a fixed \(u\), the projected factors in \(r\) have degrees
6 and 42. For a fixed \(x\), those in \(u\) have degrees
2, 27 and 66. Every indicated fiber is projectively rootless
over \(\mathbb Q\), as checked by exact integer factorization
and listed small primes in the replay. None of these is a
height-bounded search. The finite noncentered chart above and
the broader arithmetic problem remain live outside these cuts.

## Replay

    python check-controls.py
    python check_fibers.py --u -2 -1 0 4 5 6 7 8 9 --helper 2 4 5 9 --full
    python check-endpoint-cuts.py --q --h2

The finite tree replay uses standard Python; the elimination
uses python-flint 0.8 and SymPy 1.14.
Build
[SDIRKSevenChristoffelAlternativeF19](../../lean/RKCert/Research/SDIRKSevenChristoffelAlternativeF19.lean)
and run the [typed audit](proof-audit.lean) with stock Lean 4.36.0.
The polynomial eliminations are independent arithmetic proofs,
not native HasOrder wrappers. The two finite order proofs are native.
