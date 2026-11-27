# Redesigned real SDIRK15 seed with an early movable port

A different lower triangular common-unit-diagonal real-algebraic
prefix has a genuine **size-eight pure row at stage 14**. After one
more physical stage its size-seven decoder is short by exactly
one polynomial direction. This is a new forward seed, not an
order-15 method and not a reduction of the fixed 34-stage tableau.

## Actual old data and the signed displacement

Use the minimum dense size-six Laguerre cache, with physical
widths $(1,2,3,3,2,1)$ and the selected roots from the replay.
Its matrix is closed under earlier predecessors. Write $D_6$ for
the complete size-six decoder, $F_4$ for the reconstructed
fourth polynomial chart on actual rows, $J$ for integration
from zero, and $W_k=k!(J-I)^k1$. Let $L_k$ lift a low-mode
polynomial by adding just the missing high $W$-modes so it
vanishes at the actual selected layer-$k$ roots.

At size seven the first-excess polynomial space $U$ is spanned by
$W_6$, $Q_6=L_6(W_4)$, $L_6(L_5(W_2))$, and the lift at layers
five and six of the low part (modes $W_0,W_1,W_2$) of $L_4(W_0)$.
Indeed the full ordinary chart error band and the paid cache show
that the only newly missing coefficient at successive cache
layers 4, 5, and 6 is respectively $W_0,W_2,W_4$.
All physical observations at size seven still agree with their
nominal chart counterparts before the omitted-mode reconstruction,
because every child fits the paid size-six cap. Degree and cache
origin distinguish the four lifted directions, and the usual
first-excess rank lower bound is four.

For the next stage, the physical predecessor covector
\[
 \mathbf h=\tfrac14[W_3](D_6-F_4)-\tfrac{25}{6}[W_5]D_6
\]
kills all old trees through size five. In the archived
[second-band formulas](../sdirk-nonhomogeneous-kernels/LAGUERRE-ORDINARY-TWO-THREE-SLOT.md),
the size-seven coefficient on $Q_6$ is the raw vector $S_5$;
its size-seven leading coefficient on $W_6$ is $e_7$.
They satisfy
\[
 S_5-25e_7=\mathcal U(S_4/4-25e_6/6),
\]
where $\mathcal U$ is unary grafting. The coefficient row above
really produces $S_4/4-25e_6/6$ on size six: $[W_3](D_6-F_4)$
produces $S_4$, and $[W_5]D_6$ produces $e_6$. Earlier sizes
give zero, by the same band. Accordingly, adding
$\tau\mathbf h$ to a physical $\mu_yD_6$ receiver at $y$,
with $\mu_y=E_y(J-I)$, leaves that receiver actually pure
through size six. Its first-excess size-seven response is
changed by exactly the scalar functional
$r=\operatorname{coeff}_{Q_6}-25\operatorname{coeff}_{W_6}$
on $U$, times $\tau$. Only a unary child of size six sees
the new input; the separate self diagonal uses smaller
pure children. This is the
[native null-perturbation lemma](../../lean/evidence/sdirk15-movable-port-20261127/README.md).
No product of several bad children is being neglected.

## Exact physical steps

On the four-dimensional space $U$, choose $(v,y,\lambda,\tau)$
so that
\[
 \mu_v|_U=\lambda (E_y+\tau r)|_U .
\]
In the quotient by $r$ on the dual this is a two-equation
real problem in $v,y$. An exact 1024-bit dyadic replay checks
a strict contraction for the original two equations, separates
the scalar normalization, and obtains
$v\approx4.257993558105895$, $y\approx2.509346539325319$.
The nonsingular polynomial system has an isolated real-algebraic
solution. We then:

1. Append physical row 13 at $y$ with strict input
   $\mu_y D_6+\tau\mathbf h$.
2. Let $\boldsymbol\eta_y=e_{13}-E_yD_6$ be its observed contrast.
   On all size-seven residual polynomials it pays $E_y+\tau r$.
   Append physical row 14 with strict input
   $\mu_vD_6+\lambda\boldsymbol\eta_y$ and its own unit diagonal.
   It is exactly pure through size eight at the actual clock $v$.
3. Append physical row 15 at clock two using $\mu_2D_6$.
   This is individually exact through size seven. The three
   observations at the new rows restrict independently to $U$.
   Use any regular three-column section to return their model
   correction after $D_6$; the missing direction $Q$ is the
   one-dimensional common kernel. In particular $Q(v)=0$ and
   $\mu_vQ=0$.

The replay rebuilds all fifteen actual strict rows and independently
checks all 200 rooted profiles through size eight at row 14.
Its exact Sylvester test also shows that this **fixed** 14-row
stem cannot directly append a distinct second size-eight port:
the two shifted polynomials of its remaining two-dimensional
size-seven residual share the known root $v$, and the
quotients are coprime. The residuals really are all the
available kernel directions at that cut, because the physical
old size-six span is full and their two new measurements are
the actual residual functionals just constructed.

## Consequence for the 33-stage bridge

The size-eight residual of the 15-row decoder, together with
$Q$, has exact rank seven, hence fills the degree-at-most-seven
polynomials vanishing at $v$. This opens the inexpensive
stage count $15+12+7-1=33$ if one finds a different reverse
bank, but also supplies a necessary test. On a nine-site
grouped bridge with the one forward port and two disjoint
reverse terminal means, and with the whole $Q$ column paid,
the degree-seven hull vanishing at the nonterminal sites is
an available test. It leaves only the mixed two-terminal
primitives, just as in the
[order-13 coupled obstruction](../real-sdirk13-coupled-one-defect/README.md).
A full rank-five reverse top residual (all degree-six polynomials
vanishing at those two means) is therefore incompatible.
A quite different reverse rank, or a different architecture,
would be needed. No order-15 improvement is claimed.

## Exact replay

```sh
join="$PWD/../real-sdirk13-joined-interface"
work="$(mktemp -d)"
python3 "$join/refine_ports.py" "$work"
python3 check_stem15.py "$work"
```

The reuse of the helper module is for its generic dyadic interval
routines only. This stem uses independently enclosed Laguerre
roots and its own candidate centers. All inclusions and rank
checks use directed integer arithmetic, and the analytical
profile proof above is separate from residual enclosures.
