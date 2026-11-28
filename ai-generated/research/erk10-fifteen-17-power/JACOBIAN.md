# Portable kernel receipt for the 17-adic Jacobian

ERK10FifteenHenselJacobian.lean defines the five published
scalar geometry equations themselves using modular polynomials
and the paid inverse table modulo \(17^2\). The following
are checked by Lean kernel evaluation:

- base_residual: the actual residual vector modulo \(17^2\),
  \((0,136,187,102,272)\), whose entries are divisible by 17;
- geometry_jacobian: all six actual finite-difference columns
  after division by 17 modulo 17;
- jacobian_minor_unit: the selected five-column determinant
  is \(10\bmod17\).

The geometric equations have coefficients prime to 17 in their
denominators. Thus finite differences modulo \(17^2\) give
their true formal derivatives at the base residue.
The native file checks the finite arithmetic only. The Hensel
induction and reconstruction of the full family are proved
mathematically in [the main packet](README.md).

The receipt uses Lean Core and was replayed successfully on
4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 with standard axioms.
