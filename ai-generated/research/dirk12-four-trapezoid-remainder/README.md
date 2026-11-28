# Moving the four reverse trapezoids without changing their degree-eleven gate

This isolates transferable linear ingredients for a 19-row, order-twelve
DIRK construction over \(S=\mathbb Z[1/12!]\). It does not provide a
completed width-19 tableau. The 20-row single-tableau endpoint is unchanged.

Use 13 distinct scalar nodes comprising the origin, terminal clock 1,
and eleven proper sites \(P\). Four proper sites \(H\) are the early
literal weighted reverse trapezoids, and the seven others form \(C=P
\setminus H\). The exact scalar weights are \(\mathbf w\), known
through degree eleven, with arbitrary terminal score subject to that
condition. Put \(y=1-x\), \(\mathbf W_j=\mathbf w\odot\mathbf y^j\),
and \(c_x=[x\prod_{p\in P\setminus\{x\}}(x-p)]^{-1}\).
The paid weighted cubic profile \(\mathbf G\) has zero terminal entry
and annihilates powers \(x^1,\ldots,x^8\); equivalently \(G_x/c_x\)
on the proper sites is quadratic. A literal reverse trapezoid at \(h\)
requires \(G_h=w_h(1-h)^3/6\).

The divided difference of degree three of the four target ordinates
\(w_h(1-h)^3/(6c_h)\), on the actual four nodes of \(H\), is exactly
\[
 \frac16\sum_h w_h h(1-h)^3\prod_{t\in C}(h-t)
   =\frac16\int_0^1 X(1-X)^3\prod_{t\in C}(X-t)\,dX.
\]
The left equality cancels the actual \(H\)-node gaps in the
cofactor, and the scalar quadrature gives the right equality:
the degree-eleven polynomial vanishes at both endpoints and all
seven sites outside \(H\). Consequently the four-trapezoid fit
depends **only** on \(C\). Changing the terminal weight cannot
repair or break this gate. Neither can moving all four head nodes,
provided the seven-site remainder is fixed and the node gaps are
still legitimate.

Put \(\boldsymbol\Delta=\mathbf G-\mathbf W_3/6\). It is zero at
the terminal and four trapezoid rows and has the unique remaining
projection
\[
 \Delta_x=-\frac{1}{6x}\int_0^1 X(1-X)^3 \ell_x(X)\,dX
 \quad(x\in C),
\]
where \(\ell_x\) is the cardinal polynomial on \(C\). In fact
\(\sum_x \Delta_x x^j=-j!/(j+4)!\) for \(1\le j\le8\).
The first seven conditions interpolate; the eighth is precisely the
nodal-integral gate. These signed \(\Delta_x\) depend on neither
the four moving clocks nor the terminal score.

## A paid continuation criterion

Here all node differences, including gaps to 0 and 1, are \(S\)-units,
the terminal and all four trap scores are \(S\)-units, and two of the
remaining sites have \(S\)-unit \(\Delta_x\). Place those two immediately
after the four traps in reverse order, before the two other unmerged
sites and then the final three reverse sites \(u,z,r\) to be merged.
This criterion concerns the weighted reverse linear system. The old
bank must still have paid literal entries, the Jacobi injection, and the
three actual causal row copies.

Set the literal weighted lower-triangular reverse operator \(\mathit K\)
to the four trapezoids on the first four proper rows. The pointwise
lower rules are
\[
 \begin{split}
 K\mathbf W_0&=\mathbf W_1,\quad K\mathbf W_1=\mathbf W_2/2,\\
 K\mathbf W_2&=\mathbf W_3/3+\mathbf G,\quad
 K\mathbf W_3=\mathbf W_4/4+(3/2)\mathbf y\odot\mathbf G,\quad
 K\boldsymbol\Delta=\mathbf y\odot\boldsymbol\Delta/4.
 \end{split}
\]
These are paid for every later row by setting the provisional literal
diagonal to \(y_i/4\), then using four earlier unit scored donors to
solve the ordinary four moments. Their weighted Vandermonde is a
unit, and the first four donors have \(\Delta=0\). This also gives
\(K\mathbf G=\mathbf y\odot\mathbf G/2\).

The first seven reverse donor coordinates (terminal, four traps,
two chosen next sites) give a unit \(7\times7\) read matrix for
\(\mathbf W_0,\ldots,\mathbf W_4,\boldsymbol\Delta,\mathbf x\odot
\boldsymbol\Delta\). Its determinant, up to sign, is the unit
weighted Vandermonde on the first five coordinates times
\(\Delta_5\Delta_6(x_6-x_5)\). Consequently at every row numbered
at least 6 (0-based) one can independently set the two remaining
responses \(K\mathbf W_4\) and \(K(\mathbf x\odot\mathbf G)\)
without changing the lower rules.

For the Jacobi three-copy chart the full paid top test space may be
taken as all polynomials of degree at most six with \(f(0)=f(z)=0\)
and \(f(u)=\eta(u)f(r)\). The evaluations at rows 6, 7, 8 and \(r\)
split this four-dimensional space over \(S\): divide by \(X(X-z)\)
at these four sites and at \(u\), then use the five-node cardinal
decoder. Thus corrections in just those four rows may satisfy
both top pairings for the whole test space over \(S\). From this
point there is no unaccounted Vandermonde division in the weighted
reverse solver. This does not assert that any chosen mesh satisfies
the unit-score or literal old-bank assumptions.

## Two exact, movable remainders

For 13 consecutive sites \(j/m\) containing 0 and 1, retain the
Jacobi merge \(z=1/2\) in the remainder and require at least one other
remainder site to have \(H_{\rm Jacobi}(r)\) an \(S\)-unit. Of the
4,221 eligible (mesh, four trap sites) combinations, exactly two
satisfy the nodal gate, each on \(j/12,0\le j\le12\):
\[
 \begin{split}
 C_A&=\{1/12,1/4,1/3,1/2,2/3,3/4,5/6\},\\
 C_B&=\{1/12,1/4,1/3,1/2,7/12,3/4,11/12\}.
 \end{split}
\]
The unit \(\Delta\) coordinates are respectively
\(\{1/12,2/3,3/4,5/6\}\) and
\(\{1/3,7/12,11/12\}\). The exact scaled moment data and replay are
included; a small core Lean receipt independently checks the
sixteen equalities on all four listed versions. The general
identities and paid linear prototype above are not claimed as a
native Lean tableau.

A tempting stronger condition, making all three effective head
moments zero so the four scores can be a single unit cofactor
vector, would require an anchored nine-node degree-eleven quadrature
over \(S\). The separate characteristic-13 anchored scalar support
bound rules that out. The movable remainder criterion itself
requires only the single displayed nonzero-weight nodal relation, so
it remains viable.
