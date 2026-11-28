# The fixed-mesh cubic decoder fails even over the rationals

This is the final rational branch of the [fixed ten-site cubic decoder](../dirk10-cubic-decoder-ten-mesh-obstruction/README.md) with the six literal opening rows and the three port copies. The [reverse-leading reduction](../dirk10-cubic-reverse-leading-automatic/README.md) makes its low reverse ansatz automatic in auxiliary coordinates. The earlier gate left 54 chronology classes with rational parameter \(t=2/3\), although their literal midpoint coefficients were not factorial-localized. Here all those branches are excluded even over \(\mathbb Q\), by keeping the two possible literal orders of the last two nonports (108 cases). The result still does not exclude different meshes, different first reflected donors/openings, nonconsecutive ports, or arbitrary twelve-stage rational DIRK10 tableaux.

## Two additional necessary actual contexts

Use the actual rooted discrepancy identity of the previous packet. Write \(F=X(X-u)(X-p)(X-r)\), \(D_\eta=\boldsymbol\eta-EQ_\eta\), \(\mathbf h=K\mathbf W_3-\mathbf W_4/4\), \(\mathbf k=K\mathbf U\). It already gives
\[
 \mathbf h,\mathbf k \perp EF,\ E(XF),\ D_\eta.
\]
Let \(d_*\) be the size-five bush, with actual discrepancy \(d_{*,H}-E\Pi d_{*,L}=EF\).
The one-unary-parent order context for \(d_*\), with four extra leaf factors, gives
\[
       \langle K\mathbf W_4-\mathbf W_5/5,EF\rangle=0 .
\]
This is the \(j=4\) case of the exact discrepancy identity, at actual total order ten.

For the other new test, take the size-seven combination obtained from \(A d_*\) by one additional sibling leaf at its root. Its actual high deviation is
\[
      \mathbf x\odot (EJ\rho_*+\boldsymbol\eta v_*+T EF).
\]
Use the one-unary-parent identity on this combination at \(j=2\), again total order ten. Its decoded discrepancy has degree at most six and zero constant, and \(XJ\rho_*\) likewise. Thus \(\mathbf U\) annihilates both. The injection term is annihilated by \(\mathbf U\perp\mathbf x\odot\boldsymbol\eta\), from the actual size-seven dark context proved earlier. The only remaining term is
\[
             \langle K(\mathbf x\odot\mathbf U),EF\rangle=0 .
\]
These are necessary equations from actual trees, not additional sufficient simplifying conditions.

## Exact rank accounting

There are six physical reflected nonports, including the terminal. The first two rows are forced by the two leading actions; the third pays all three leading actions with its three weighted Vandermonde pivots. On physical rows with index \(i=3,4,5\) in zero-based reflection, freely taking taps in columns \(3,\ldots,i\) gives \(1+2+3=6\) allowed variables, with the first three taps solved linearly against them. The three later auxiliary rows of \(K\) are gauge only. The test vectors on the left sides of the eight required equations vanish at those three ports. This parameterization therefore spans every possible physical \(K\) obeying the first three actions, with no assumption of sparsity beyond chronological triangularity.

The six tests from \(\mathbf h,\mathbf k\) and the two additional necessary tests form an affine \(8\)-equation system in those six variables. After row-wise clearing and primitive reduction, all 108 extended integer matrices have a nonzero \(7\times7\) minor: choose seven rows and reduce modulo 13, 17 or 19. Thus the coefficient rank is six and the augmented rank is seven over \(\mathbb Q\); no assignment can satisfy the necessary order equations. No nonlinear or numerical root checks enter.

## Replay

With Python 3 and SymPy:

    python3 -B check.py --emit /tmp/dirk10-cubic-rational-ranks.jsonl
    cmp exact-ranks.jsonl /tmp/dirk10-cubic-rational-ranks.jsonl
    python3 -B generate-lean.py /tmp/DIRK10CubicRationalTopArithmetic.lean
    cmp /tmp/DIRK10CubicRationalTopArithmetic.lean \
        ../../lean/RKCert/ReviewedNative/DIRK10CubicRationalTopArithmetic.lean
    sha256sum -c sources.sha256

The [per-chronology record](exact-ranks.jsonl) preserves the integer minor, row indices, residue prime, residue matrix, and the nonzero determinant residue. The core Lean module checks all 108 residue nonsingularities by division-free modular elimination. The rooted reduction above remains mathematical, not a native theorem excluding DIRK methods.
