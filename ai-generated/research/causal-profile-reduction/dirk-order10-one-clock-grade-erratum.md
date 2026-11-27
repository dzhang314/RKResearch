# Degree-budget correction for the DIRK10 one-clock branch

The ordinary DIRK10 stage interval remains **11–12**. The diagonal,
gap-two and active signed-inventory results do not use this step.

A physical row where the grade-five pure defects vanish integrates
input polynomials only through degree four (`C(5)`). To integrate a
degree-five polynomial one must also account for the order-six defect.
In the one-clock normal form its terminal-direction contribution is
not known to vanish solely because the row is grade-five pure.

The original one-clock, constant one-off and nonconstant one-off notes
used a degree-five nodal polynomial, or a nodal quartic multiplied by
the clock, as if that row had `C(6)`. The corresponding finite scalar
certificates retain their literal hypotheses and check their stated
equations, but these equations were not proved for the proposed
tableaux by that argument. In particular the old general assertion
that an active one-physical-dirty-clock candidate needs two distinct
off-Lobatto clocks should not be used. The all-fixed nonconstant
branch with zero terminal affine coefficient was not decided by that
analysis. A revised one-off argument must use only paid degrees or
explicitly account for the degree-six defect.

The [replacement proof](dirk-order10-paid-one-off-repair.md) uses degree-four
forward tests in the constant branch and reconstructs the exceptional
clock from an actual reflected suffix in the nonconstant branch.
It excludes exactly one off-Lobatto clock in both branches. Zero
off-Lobatto clocks were initially excluded only for a constant cubic
defect or a nonzero terminal affine coefficient. A [separate
degree-four prefix proof](dirk-order10-all-fixed-prefix-exclusion.md)
now rules out the all-fixed case even with zero terminal affine
coefficient, and even if every dirty row has zero output weight.
The finite scalar checks are Lean-checked separately from the
mathematical reduction from actual tableaux.
