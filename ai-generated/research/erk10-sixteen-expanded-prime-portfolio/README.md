# Algebraic-prefix sixteen-stage ERK10 over twelve prime families

The [guarded construction at 17](../erk10-sixteen-17-power-lift/README.md)
also works over every power of **19, 23, 31, 47, 53, 61, 79, 83, 107, 109,
and 113**. Each row of [seeds.json](seeds.json) gives a compatible
family with the same algebraic prefix and a unit eleventh-bush
defect. It includes an alternative family at 17. The 19 and 23
families here use a different prefix from those in the
[four-prime rational-prefix packet](../erk10-sixteen-small-prime-portfolio/README.md).

Together the two constructions give a sixteen-stage upper bound over
any nonzero commutative ring annihilated by a positive integer whose
prime factors lie in the following set (or with any one of the
listed primes nilpotent):
**11, 13, 17, 19, 23, 31, 47, 53, 61, 79, 83, 107, 109, 113**.
They apply individually over the corresponding p-adic integer rings
and fields. For mixed finite characteristic, combine the literal
prime-power tableaux by the integer Chinese remainder theorem before
transferring to the ring. The normalized order-eleven defect is a
unit in each component and therefore in every nonzero target ring.
No rational or real bound changes.

## Replay and scope

Each input row stores the prime, the omitted terminal equation index,
the parameters at the prime and its square, the two normalized bush
defects, and the residue pressure Jacobian determinant. Parameter
order is theta followed by x1 through x8, with x0 fixed at 1. The
first pressure is 3 theta² minus 15 theta plus 20. The lift columns
are theta, x3, and x5, in that order. At 23 the nonsingular five-row
terminal solve omits equation 0; all other seeds omit equation 2.
The residual pressure is precisely the omitted row, so its vanishing
enforces all six original equations in either schedule.

The construction uses the [same marked-source order
argument](../erk10-sixteen-17-power-lift/README.md#why-the-equations-imply-the-ordinary-order-conditions)
with fixed denominators and the recorded unit pivots. Every pivot
remains a unit in its residue class. The finite differences computed
modulo the square determine the residue Jacobian of the guarded pressure
map, since its denominators are units; its invertibility gives a unique
correction in the three chosen variables at each subsequent exponent.
The residue bush defect is nonzero and stays so. The seed list does not
assert that these are the only prime families.

From this directory:

    python3 -B rebuild.py --exponent 3 --emit /tmp/rk-erk10-extra
    python3 -B verify.py /tmp/rk-erk10-extra
    (cd /tmp/rk-erk10-extra && sha256sum -c "$OLDPWD/literal-sha256.txt")

All 36 generated tableaux have an independent direct replay of the
1,205 ordinary rooted-tree conditions and the unit next-order defect;
the prime-power coefficients also reduce compatibly. The arithmetic
audit records the guarded solve pivots and derivatives. The independent
checker generates non-plane rooted trees as child multisets and does
not import the construction or its tree verifier. The guarded
all-powers result is a mathematical Hensel argument, not an end-to-end
Lean theorem.
