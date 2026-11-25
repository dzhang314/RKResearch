# ERK16 weak-four quartic reductions

Editable proof notes with exact rational checks, 25 November 2026. This is a reduction package, not a complete exclusion and not a verified Lean module.

1. [Uniform first-clock crossing](01-crossing.md). Maps the checked weak-four structural sources to the six stopped laws and the weighted degree-14 quadrature (raw degree 15). Proves the actual reverse first clock $a$ exceeds the actual forward first clock $d$, including possible exterior marks. Also rules out two outward secondary stops when Q has just three strict unit roots.
2. [Root counts and parity](02-first-root-count.md). Both first intervals contain at least three strict unit Q roots. The two first tests then identify the weighted left and right residual tails. Opposite signs exclude a fourth Q root outside the strict unit interval, including the possibility that it is at zero.
3. [Exterior secondary clocks](03-exterior-secondary.md). A one-root outward weighted average bounds the full exterior range; a signed density positive on affine squares and exact rational Gram comparisons rule out either secondary clock being exterior.

**Surviving shape.** Q has four simple strict unit roots $r_1<r_2<r_3<r_4$. The actual first clocks satisfy $d<r_2<r_3<a$, and both secondary clocks lie strictly between 0 and 1. Any sole exterior Z mark can only be a reverse first clock $a>1$ or a forward first clock $d<0$. The all-interior and possible exterior-first families are not excluded here. No additional moments or diagonal assertions are premises of these three reductions.

**Exact checks.** Run `python3 checks/run_all.py` from this directory. This uses only the Python standard library and checks the displayed rational reference polynomials, sign brackets, localizer Gram forms, and numeric inequalities. The chronology, polynomial exactness, rank arguments, and sign-class logic are carried by the editable mathematical derivations, not by the Python code or a Lean compiler. Root selection may be carried out in an ordered algebraic extension, and all reported clock inequalities concern the original labels.

**Conventions.** All four marks are numerical reflected clocks. $a,c$ are the last and next-to-last in physical contrast chronology; $d,h$ are the first and next-to-first. Distinguish the quartic fitting polynomial $Q$, the nodal product $Z$, and their degree-eight product $F=QZ$ from the auxiliary fit named $P$ in native source. Integrals mean oriented formal-primitive evaluations, not analytic completion.
