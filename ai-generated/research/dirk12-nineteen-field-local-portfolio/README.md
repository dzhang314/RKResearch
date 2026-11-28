# Nineteen-stage order-twelve DIRK over every admissible field and local ring

Four literal rational tableaux now give **nineteen stages and
exact order twelve over every field and every nonzero commutative
local ring in which \(12!\) is a unit**. They also give the same
stage bound over every nonzero commutative ring of finite
characteristic inverting \(12!\). This is an arithmetic portfolio,
not a single tableau defined over \(\mathbb Z[1/12!]\).

The first member is the verified
[nineteen-stage rational two-port witness](../dirk12-nineteen-rational-two-ports/README.md).
The three new members use the same \(10+11-2\) actual stage
architecture, with different scalar grids and old donor ratios.
They solve their literal reverse fit in rank 51 and verify
both full raw row merges with zero shifts. The last two use
integer scalar nodes chosen for good reduction at 13 and 19.
Large, signed, or repeated clocks across unmerged parts do
not affect the ordinary rooted order definition.

## Exact checks and local coverage

Let \(D_i\) be the least common denominator of all literal
entries in member \(i\). For all four:

- An independent standard-library replay checks the **7,813**
  rooted shapes through order twelve, on integer-scaled stage
  vectors rather than relying on the construction.
- The two reduced numerators of the scaled thirteenth bush
  and tall defects are coprime, and their denominators divide
  powers of \(D_i\). If \(D_i\) is a unit in a nonzero ring,
  the two defects cannot both vanish. This remains true if
  one particular defect does vanish after specialization.
- \(A_{00}=0\). The second genuine diagonal is respectively
  \(9/616,1/112,621/1414,35/136\). Each numerator and denominator
  divides its own \(D_i\), so the second diagonal is a unit
  whenever its tableau is used.

The exact common denominator gcd is
\[
 \gcd(D_a,D_b,D_c,D_d)=61963646976000\mid (12!)^3.
\]
In particular for any prime \(p>12\) at least one literal
denominator is prime to \(p\). At 13 and 19 specifically,
\(D_c\equiv11\pmod{13}\) and \(D_d\equiv17\pmod{19}\).
Those two full rational constructions use pivot elimination
with denominators staying units at the indicated prime. There
is no transfer claim from an unknown finite-field method.

In a local ring \(R\) with \(12!\) a unit, the residue field
has characteristic zero or \(p>12\). In characteristic zero
all nonzero integers reduce nonzero. Otherwise the gcd
guarantees some \(D_i\) reduces nonzero. An element with
nonzero residue is a unit in the local ring, so this gives a
literal nineteen-stage method over \(R\) itself, not merely
over its residue field. This includes all admissible fields,
and no field ordering is needed.

If \(R\) has finite characteristic \(n>1\), decompose it
along the prime-power factors of \(n\) by the usual Chinese
remainder idempotents. For each factor ring use a member
with \(D_i\) prime to its characteristic prime; such an
integer is a unit there by integer Bézout. Combine the
nineteen-stage entries and weights componentwise. The rooted
equations and the distinct diagonals hold on every
component. The two fixed-order-thirteen defects generate
the unit ideal componentwise, hence also in the product.
This proves exact order rather than only the paid moments.

The argument does not allow gluing over an arbitrary
mixed-characteristic ring. In particular the gap to the
[single 20-stage factorial-only witness](../dirk12-twenty-factorial-two-ports/README.md)
remains for that broader coefficient claim. These are upper
bounds, not minimum claims over every field. The real
minimum of fifteen is unrelated to this denominator cover.
This arithmetic packet does not yet have an end-to-end
Lean replay.

## Reproduction

All three new literal files and their scalar inputs are
explicit. The optional output-directory switch gives a
fresh byte-comparable reconstruction. From this directory:

    python3 -B build.py
    python3 -B verify.py
    sha256sum -c sha256.txt

The verifier reads the first fixture in its immutable sibling
directory and does not import the construction. Each of the four
rooted replays and both target-prime checks run in one command.
