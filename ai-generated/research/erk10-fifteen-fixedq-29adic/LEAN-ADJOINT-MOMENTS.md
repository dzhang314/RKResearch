# Exact native actual mixed quadrature moments

ERK10FixedQ29AdicAdjointCore is the finite integer beta/Jacobi coefficient
receipt; ERK10FixedQ29AdicAdjointMoments transfers it to the actual raw
cardinal/cofactor vectors under the prescribed local characteristic-29 chart.
Here Y is the reverse clock and X=1-Y is the physical forward clock.

* actual_beta_pair: the nominal two primitive pairings agree for i>0,
  k+i <= 8.
* actual_cofactor_mixed_zero: the u pairing against Y^k X^i vanishes for
  k+i <= 7.
* actual_jacobi_mixed_zero: the w pairing of the fixed Jacobi J against X^i
  vanishes for 1 <= i <= 4.

Compile Core then Moments using Lean 4.36.0 with the checked physical/order
objects on LEAN_PATH. The attached transcript reports only standard Lean
axioms. These are actual scalar moments; they do not by themselves prove
the globally transposed word operator or the final three order-edge receipts.
