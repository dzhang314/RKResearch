# No single factorial-localized tableau in the six aligned mirror branches

The six regular one-evaluation branches of the
[deterministic rational family](../erk10-sixteen-rational-mirror-family/README.md)
are exhausted over \(S=\mathbb Z[1/210]\). Exactly one choice
has paid stage clocks and paid scalar masses. Its protected old
endpoint coefficient has a forced pole at 17, independent of the
late tap choice and the old repeated-clock weight split.
This does **not** exclude nonaligned mirrored methods, different
dense prefixes, or sixteen-stage factorial-only ERK10 in general.

## S-unit restrictions on the horizon

Set \(N=12\theta^2-45\theta+40\),
\(F=15(\theta-2)^2\), and \(v=\theta N/F\).
The source and clock geometry is the one in the linked family:
the protected old normalized clocks are \(0,e,1,2,2,v,v\),
the old pure endpoint is at \(\theta\), and the homothety
to physical clocks is \(\xi/\theta\). The protected sixth row
uses the unique old clock-one column with entry \(v^2(v-1)/3\)
before this homothety. This entry belongs to the actual dense
prefix, not to the late adjustable block. The regular guards
are as in the family; in particular \(\theta=0,1,2\)
and degenerate prefix collisions do not form part of this claim.

The six formulas for the new alias are

| Case | Anchor a | Anchor b |
| --- | --- | --- |
| 0 | \(1/2\) | \(1/2\) |
| 1 | \(F/(2N)\) | \(\theta/4\) |
| 2 | \(F/(F+N)\) | \(\theta/(\theta+2)\) |

Fix an unpaid prime \(p>7\). The following arguments use the
actual stage clocks or protected coefficients, and cover
rational poles at \(p\) as well as finite residues.

* If \(\theta\) has a pole, then \(v\) has a pole of the same
  order: the leading ratio is \(4\theta/5\). In case 1b the
  alias itself has a pole. In every other case the alias is a
  unit (limiting constants \(1/2,5/8,5/9,1\)), so the scaled
  protected entry \((\xi/\theta)v^2(v-1)/3\) still has a pole.
  Thus \(\theta\) is integral at \(p\).
* If \(p\) divides \(\theta-2\), then \(N(2)=-2\) is a unit,
  \(v\) has twice the resulting pole order, and \(\xi\)
  is either a unit or has exactly twice the positive
  valuation of \(\theta-2\). The protected entry again has
  a pole. Thus \(\theta-2\) is a unit at every unpaid prime.
* For cases 0a, 0b, 1a, 2a, a positive valuation of
  \(\theta\) would leave \(\xi\) a unit, with residue
  \(1/2,1/2,3/4,3/5\) respectively. The old physical
  clock \(\xi/\theta\) would then have a pole.
* For case 1b the same conclusion follows from a scalar
  weight instead. Its aggregate early mass at squared
  normalized radius \(1/9\) has a primitive integer
  numerator with constant \(-2^{21}3^7 5^2\), and
  integer denominator with zero constant. These are the
  *reduced rational-function coefficients*, not an
  inference from an uncanceled expression. A positive
  valuation of \(\theta\) therefore gives a mass pole at
  every unpaid prime. The exact extraction is in
  [mass_guard.py](mass_guard.py).
* In case 2b use \(\theta+2\) instead: if it has positive
  valuation, the numerator of \(\theta/(\theta+2)\)
  is a unit, giving an alias pole.

Hence in the first five branches \(u=\theta/2\) and \(1-u\)
are \(S\)-units. In case 2b the corresponding pair is
\(u=(\theta+2)/4\) and \(1-u\).

## Complete finite exhaustion and the protected weight

The complete solution count for \(u+(1-u)=1\) with prime set
\(\{2,3,5,7\}\) is 63 up to the signed reciprocal symmetries.
See [von Känel and Matschke, Theorem 1](https://www.math.u-bordeaux.fr/~bmatschke/reportVonKaenelMatschke3.pdf)
and their [full article](https://arxiv.org/abs/1605.06079); the authors credit de Weger for the first six prime sets. The [authors’ data description](https://bmatschke.github.io/solving-classical-diophantine-equations/#data-for-s-unit-equations).
The audit independently enumerates 63 positive coprime triples
\(a+b=c\), \(a\le b\), then takes
\[
 a/c,\ b/c,\ c/a,\ c/b,\ -a/b,\ -b/a.
\]
The result is all 375 signed first coordinates. Completeness
uses the published theorem, not the program’s enumeration
cutoff.

In each of the six branches the replay tests all these horizons.
When the remaining evaluation is also placed on the fourth
test root, both evaluation values are blind. The two fused
terminal integrals would then have to vanish simultaneously;
the replay checks that they do not. It also checks that the
linear geometry condition never leaves a free undetermined
clock. On the distinct linear branch, the only choice with
paid clocks and every paid scalar mass is case 0b at
\(\theta=5/4\), with raw clocks
\[
 (1,2/3,1/3,2/3,5/7,1/5,2/7,4/5,1/2).
\]

At this choice the normalized old clock \(v=10/27\) and the
scale is \(2/5\). In the old pure endpoint row the starter
has zero mass: its second-stage residual is the sole
nonzero component, and the order-three moment kills it.
The four remaining distinct clock masses are those at the
physical clocks \(0,2/5,4/5,4/27\), integrated up to \(1/2\).
Testing \(X(X-4/5)(X-4/27)\) therefore forces the mass at
\(2/5\) to be
\[
 \frac{\int_0^{1/2}X(X-4/5)(X-4/27)\,dX}
 {(2/5)(2/5-4/5)(2/5-4/27)}
 =\frac{5875}{26112}.
\]
This is a single protected physical entry (or the same sole
active mass if the zero-weight starter shares the clock).
Its numerator is prime to 17 and its denominator is divisible
by 17. No late tap or repeated-clock split changes it.

The [native scalar receipt](../../lean/RKCert/ReviewedNative/ERK10MirrorFactorialGate.lean)
derives this forced mass from three actual scalar moment
equalities and checks the unpaid divisibility. Lean 4.36 was
checked. The use of the external S-unit completeness theorem
and the exact parameter enumeration are not claimed as an
end-to-end Lean formalization.

## Replay

    python3 -B audit.py
    python3 -B mass_guard.py
    sha256sum -c sha256.txt

The first replay uses the standard library. The second uses
exact SymPy rational function arithmetic.
