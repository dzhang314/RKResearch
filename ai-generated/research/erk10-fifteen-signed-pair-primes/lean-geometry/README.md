# Kernel checks for the 130 signed-pair geometry seeds

On each of Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1,
the kernel checks all 130 cases in 13 batches, with no Mathlib
dependency and no native_decide. Each case checks:

- primality by trial division for its archived prime (all below 3600);
- pairwise distinctness of the nine scalar sites modulo that prime and
  unit inverses for the denominators used;
- all five polynomial geometry residuals vanish modulo p at the
  archived seed and modulo p² at the archived lifted seed;
- the exact nonzero residue of the fixed-d 5-by-5 Jacobian determinant,
  with each column formed by a finite difference of size p modulo p².

For polynomials over integers with denominators prime to p, these
finite differences divided by p give the derivative columns modulo p.
This scalar check does not formalize Hensel's lemma, the reconstruction
of a tableau, or the 1,205 rooted tests. The separate exact replay in
the parent directory covers the actual tableaux at p and p².

From this directory:

    LEAN=/path/to/lean sh check_lean.sh
    sha256sum -c sources.sha256

To regenerate the 13 literal declaration files, run
`python3 -B generate_batches.py /path/to/output`. The generator reads
the two published sets of literal data. The generic checker is not
generated from them.
