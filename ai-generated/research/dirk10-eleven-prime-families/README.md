# Eleven stages are optimal for DIRK10 in 32 prime and prime-power families

An exact order-ten lower triangular Runge–Kutta tableau with eleven
stages exists over each of the following prime fields, and also over
the corresponding rings of \(p\)-adic integers:

\[
\begin{gathered}
59,73,127,149,191,199,283,373,419,461,467,521,563,601,739,761,\\
773,811,829,857,863,919,947,967,1031,1171,1193,1319,1409,1481,1487,1499.
\end{gathered}
\]

The [reviewed stage floor](../../lean/RKCert/ReviewedNative/DIRKOrderTenSaturation.lean)
shows that 11 is minimal over every field. A nonzero commutative unital
ring maps to a residue field and the denominator-cleared rooted
identities descend; hence the same floor applies to such rings. In
particular 11 is the exact minimum in every nonzero commutative ring
of characteristic \(p^e\), \(e\ge1\), for any prime on the list, and
in any finite characteristic supported on the list. The result does
not rule in or out eleven stages at primes not listed. It does not
change the real minimum of 11 or the rational minimum of 12.

## Finite-field replay

The [seed packet](seeds.json) stores the parameter \(k\), an ordered
triple of suffix roots, a cleared order-eleven failure and the front
derivative at each prime. The [replayer](replay.py) reconstructs all
32 tableaux by the full 79-variable linear solve from the
[real-algebraic construction](../causal-profile-reduction/dirk-order10-eleven-real-algebraic.md),
using modular field arithmetic. It checks the root conditions,
every needed modular division, all 79 pivots and all residual rows.
For each literal tableau it tests all 1,205 rooted conditions twice:
once with unordered child multisets and once by normalizing binary
root-attachment words. It also checks that the eleventh-vertex star
has nonzero scaled defect. No floating point is used.

The smallest example is \(p=59\). Both that literal matrix and a
compatible lift modulo \(59^2\) are supplied in the seed packet. The
replayer checks their full reduction compatibility and all rooted
conditions. Their cleared eleventh-order residuals are 11 and 1604,
respectively, which remain units in their rings.

## Why every prime-power exponent works

Let \(p\) be listed. The checked derivative of the front cubic is a
unit modulo \(p\). Its root lifts to \(\mathbb Z_p\) by the simple-root
form of Hensel's lemma: at each step, if \(F(k_j)\equiv0\bmod p^j\),
choose the unique digit \(d\bmod p\) such that
\(F(k_j)+p^j d F'(k_j)\equiv0\bmod p^{j+1}\).
The result is compatible and the derivative stays a unit.

The rational formulas for the exterior clocks and the affine
correction use only denominators nonzero at the chosen residues.
The normalized suffix cubic is consequently defined over
\(\mathbb Z_p\). Its three residue roots are simple: the replay
checks that the unnormalized degree-five polynomial has a nonzero
leading coefficient and five distinct roots, two of them the removed
exterior roots. Lift the three simple suffix roots in the chosen
physical order by the same digit construction.

The lifted parameters define a homomorphism from the published
18-dimensional rational quotient algebra into \(\mathbb Q_p\).
The algebraic solve and the full rooted identities from that
construction therefore hold over \(\mathbb Q_p\) at this
specialization. Its displayed system is integral at the lifted
parameters, since every requested explicit scalar divisor was a
unit in the residue computation. Rank 79 modulo \(p\) gives a
square subsystem whose determinant is a unit in \(\mathbb Z_p\).
This subsystem has a unique solution over \(\mathbb Q_p\), and its
adjugate formula shows that solution is integral. It is exactly the
solution transported from the rational tower, so it satisfies the
remaining linear rows and every rooted identity as well. This is
why a nonsingular subsystem suffices here; it is not an assumption
that solving a few rooted residuals lifts an arbitrary overdetermined
solution. Its reduction is the checked field tableau, and hence its
next-star residual is a unit at every exponent.

For each \(e\) the reduction modulo \(p^e\) maps into every ring of
characteristic \(p^e\), preserving all order conditions and the unit
defect. The ordinary Chinese remainder isomorphism on the prime
power factors of a finite characteristic gives the mixed-prime
claim; the tableaux have the same size and the same star test fails
by a unit in all nonzero components. The prior [finite 419 lift](../causal-profile-reduction/dirk-order10-zmod419.md)
is distinct; this argument supplies an infinite 419 family as well
as the other 31 primes.

From this directory, run:

    python3 -B replay.py --emit /tmp/dirk10-prime-tableaux.json
    cmp tableaux.json /tmp/dirk10-prime-tableaux.json
    sha256sum -c sources.sha256

The finite arithmetic and full real-algebraic tower identities have
separate exact replays. The 32-prime transfer and its Hensel argument
are mathematical proofs. The [separate native CRT certificate](../dirk10-eleven-prime-crt-native/README.md) proves exact minimality for every characteristic dividing its fixed modulus, including all 32 primes, 59², and their mixed divisors. It does not formalize the general Hensel step.
