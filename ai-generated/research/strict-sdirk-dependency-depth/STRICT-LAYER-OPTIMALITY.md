# The exact stage count for strict adjacent layers

Consider explicit Runge–Kutta methods whose nonzero entries connect
only consecutive layers and whose output weights are supported on
the last layer. Over the real algebraic numbers, the minimum number
of stages for order \(p\ge1\) in this class is
\[
  \left\lfloor\frac{(p+1)^2}{4}\right\rfloor .
\]
In particular it is 110 at order 20. This is a minimum for the
stated architecture, not a lower bound for unrestricted explicit
Runge–Kutta methods.

**Lower bound.** Count layers backwards from the output by \(h\).
The [square beta-Hankel test](QUADRATIC-ADJACENT-LAYER-WIDTH.md)
forces at least \(\lceil(p-h)/2\rceil\) distinct stage clocks on
every layer \(0\le h\le p-1\). Summing the widths gives the
displayed count. The lower bound also holds over any nonzero
commutative ring under the denominator-cleared rooted-tree
conditions.

**Attainment.** Take precisely \(n_h=\lceil(p-h)/2\rceil\) stages
on each layer \(h\). Use \(n_h\)-point Gaussian quadrature for
the weight \((1-x)^h/h!\) on \([0,1]\) to choose the stage clocks
and quadrature weights on that layer. The first physical layer
(\(h=p-1\)) has just one stage, with clock zero; only the constant
moment is needed there. The
[endpoint construction](STRICT-ENDPOINT-COUPLING.md) gives actual
adjacent blocks with those row sums and with all paid moments
\[
\frac{\mathbf b\cdot\bigl((\mathbf 1-\mathbf c)^{\odot k}
                     \odot A^h\mathbf c^{\odot a}\bigr)}
     {k!\,a!}
=\frac{1}{(h+k+a+1)!},
\qquad h+k+a+1\le p.
\]
All construction steps use only these real algebraic nodes and
field operations, so the coefficients lie in a finite real
algebraic extension of \(\mathbb Q\).

**Why the endpoint moments suffice.** At these widths the endpoint
tests imply two identities: an adjacent block integrates
polynomials of degree below a threshold pointwise, and a tilted
output weight row can be passed through the block to the previous
physical layer. In a rooted tree within the remaining order budget,
at most one branch lies above the pointwise threshold. The other
branches give an exact polynomial factor. The tilted readout moves
the one remaining branch to the previous layer, and induction
settles it there. The [full rooted-tree proof](ENDPOINT-TO-ROOTED.md)
spells out the threshold and the order budget.

The construction has exactly \(p\) strict layers, so \(A^p=0\).
The \((p+1)\)-vertex tall condition fails. Thus the constructed
method has order exactly \(p\).
