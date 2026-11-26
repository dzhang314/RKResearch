# Exact finite check for the 60-stage method of order 18

The [tableau](../tableau-18-weighted.json) has exact order 18 with coefficients in any nonzero commutative ring in which 18! is a unit. This receipt checks the actual split at centered clock −1/3, the signed adjoint identity, every scalar moment, the complete finite rooted closure and forward error tests, and the literal fold from 99 virtual to 60 physical rows. Two actual size-19 defects have an integer combination equal to one. Neither the ordinary conditions nor the next-order witness requires an inverse of 19.

From this directory:

~~~sh
python3 check.py .. . 18
~~~

The checker uses only the standard library. It is not a Lean certificate. The [59-stage variant](../order-18-localized-59/README.md) needs four additional primes to be invertible and uses this receipt to verify that it retains the original forward and reverse charts.
