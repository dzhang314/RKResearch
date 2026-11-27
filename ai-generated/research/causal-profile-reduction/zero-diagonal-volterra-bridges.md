# Chronological zero-diagonal bridges for the Volterra kernel

Let \(A\) be lower triangular, \(c=A\mathbf1\), \(C=\mathrm{diag}(c)\),
and \(R=CA-AC-A^2\). This is an exact local improvement to the
[zero-diagonal nullity budget](local-nullity-nodal-cut.md), not a new
unrestricted stage lower bound. It does not require the clock values to be
distinct, the weights to be nonzero, or the order to be ten.

## The test

For three successive rows with outer diagonal entries zero and middle
diagonal \(d\), write the clocks as \(x,y,z\), the two consecutive taps
as \(u,v\), and the direct first-to-last tap as \(w\). Compute
\[
D=(z-x)d^2w+uv\{(y-x)(z-y)-d(z-x)\}.
\]
There is no division and no assumption on \(d\). This is the determinant
of rows 2,3 and columns 1,2 of the actual local \(R\):
\[
 \det\begin{pmatrix}u(y-x-d)&-d^2\\
       (z-x)w-vu&v(z-y-d)\end{pmatrix}=D .
\]
In particular, if \(z=x\) then \(D=-uv(y-x)^2\). In any field, a live
two-hop excursion to a different clock and back therefore earns a
pivot regardless of the middle diagonal and direct tap.

On a prefix of length \(n\), mark each zero diagonal at index \(i\) if
either (i) the next stage exists, also has zero diagonal, and
\(a_{i+1,i}(c_{i+1}-c_i)\ne0\), or (ii) the stage two steps later
exists, has zero diagonal and the displayed minor is nonzero.
If there are \(z_0\) zero diagonals and \(h\) **distinct marked starts**,
then over any field,
\[
                  \dim\ker R_{[1,n]}\le z_0-h.
\]
Indeed restrict a kernel vector to the unmarked zero sites. If all its
recorded values vanish, consider its first nonzero coordinate. It cannot
have nonzero diagonal (the pivot there is \(-a_{ii}^2\)). At a one-step
mark the next row forces that coordinate to vanish. At a two-step mark,
eliminating the middle coordinate in the next two rows gives
\(D v_i=0\); the right endpoint has zero diagonal so no later coordinate
enters. Thus no first nonzero coordinate exists. Distinct starts are
paid simultaneously, even when different bridge windows overlap. The
same reasoning applies to a counted principal segment with its
original clocks fixed; do not recompute clocks after truncation.

For instance, where a separately established RK equality-case argument
gives \(\dim\ker R\ge3\), any positive mark requires at least four
zero diagonals. In the exactly-three-zero branch, all the displayed
admissible minors must vanish. This statement explicitly needs the
*kernel* lower bound; merely knowing that there are at least three zeros
is not sufficient. No maximal-rank or generic-tap assumption is used.

**Lean scope.** [VolterraZeroBridge.lean](../../lean/RKCert/ReviewedNative/VolterraZeroBridge.lean)
defines causal matrix action by its exact finite row sum. Its kernel
test is `kernel_zero_of_free_zero`; rank-nullity translates that
trivial-kernel restriction to the displayed dimension inequality.
The file checks on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 with no
external dependencies. The division-free minor identity holds over
commutative rings, but the nonzero-pivot argument is stated over fields.
