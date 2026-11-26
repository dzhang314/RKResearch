# Optional endpoint weight family for the seven-stage tableau

This is an algebraic retuning of the last row and endpoint weights,
separate from the exact tuple of [the symbolic certificate](SEVEN-STAGE-SYMBOLIC.md).
It does not change the first six rows or the selected certificate fixture.

Pad the row $\mathbf a_5$ to six donor coefficients and put
$$
 \mathbf r\coloneqq\frac{\mathbf a_7-\mathbf a_5}{120}
       =(-3/20,\,3/4,\,0,\,-13/40,\,-1/120,\,-4/15).
$$
It annihilates the first six coordinates of $\mathbf 1$ and
$\mathbf c$. For any unit $v$ in the coefficient ring set
$$
  b_7=v,\qquad b_5=11/120-v,\qquad
  \mathbf a_7=\mathbf a_5+\mathbf r/v .
$$
All other rows and weights remain unchanged. Stages 5 and 7
still have clock $1$, and the total weight there is unchanged.

For a fixed rooted tree of order at most six, regard its output
coordinate on a row supported in the first six stages as a
function of the row. At the row $\mathbf a_5+T\mathbf r$, its
root product is affine in $T$: a factor can vary only for a
child of order at least three, and two such children would give
rooted order at least seven. Write the affine expression as
$M_t+T N_t$. The combined stage 5 and 7 readout then equals
$$
 (11/120-v)M_t+v(M_t+N_t/v)=(11/120)M_t+N_t .
$$
This proves the same paid identities as for $v=1/120$.
The tall-seven tree has just one root child, so its root
readout is affine as well; its unit defect is unchanged.
Other order-seven outputs need not remain fixed.

For example $v=1/12$ makes $b_5=1/120$ and changes the
last row to
$$
       (-1/20,\,0,\,9/4,\,21/10,\,-1/10,\,-16/5).
$$
This is an optional algebraic variant, not the literal tuple
used by the separate exact enumeration.
