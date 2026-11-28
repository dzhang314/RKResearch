# The fixed-horizon dirty relay cannot repeat a visible late clock

At relative FSAL horizon \(\xi=1\), relay \(w=2/3\), keep
the actual degree-four [dirty-relay decoder splice](../erk10-dirty-sixth-distinct-tail/README.md)
and append six strict rows. Consider an order-ten rational output
supported on the origin and high rows. This packet excludes exactly
one repeated **visible** late clock (one off \(0,1,w\)) with no
additional late collision. With the
[distinct](../erk10-dirty-sixth-distinct-tail/README.md) and
[invisible collision](../erk10-dirty-sixth-invisible-collision/README.md)
packets, it exhausts the architecture at these fixed two horizons.
It does not exclude general rational ERK10 or different relay horizons.

## Actual source rank for arbitrary six-stage seeds

The rooted source-span argument is not confined to the sample seed.
For any rational six-stage genuine order-five prefix,
the [rank-four theorem](../erk10-rank-three-port-one-label/README.md)
gives true size-five defect space \(F_5=\ker b\cap\ker E_o\),
with the two constraints independent by the nonzero first moment.
If its marked covector \(bC\) killed \(F_5\), then
\(bC\in\operatorname{span}(b,E_o)\), so all nonorigin active
weights would have the same clock. This contradicts even
scalar degree-four precision. Thus \(C\boldsymbol u\) for some
\(\boldsymbol u\in F_5\) gains one actual size-six pure direction
in the five-dimensional nonorigin low space. At the FSAL, the
ghost and the relay this marked direction is zero, because all
three stages still pay local derivative size five.

The genuine size-six ghost supplies one more independent direction:
some true size-six pure difference is nonzero there. Neither FSAL
nor relay has size-six defects, since they are locally pure
through size six. Consequently \(F_6\) has rank six, with pure
coordinates exactly the five low nonorigin rows and the ghost.
This forces zero output on those six physical stages in every
order-ten continuation using the same pure-through-six cross-feed,
so the indicated output support can also follow from actual order.
The first nine actual profile coordinates at size at most five
have full rank from the two independent missing-model probes at
ghost and relay; see the [causal relay geometry](../erk10-dirty-sixth-relay/README.md).
Equivalently one can assume this full grade-five profile rank as
part of the decoder architecture.

For true profiles through size six the joint coordinate/model
space now has dimension \(6+\dim F_6=12\) by the six bush
directions. Subtracting the exact degree-four decoder on the
nine actual coordinates eliminates all defects at sizes ≤5,
so the size-six residual polynomial image has dimension \(12-9=3\).
Its polynomials vanish at \(0,\xi,w\) by actual local purity.
All size-six source trees have immediate children of size ≤5,
just as required by the marked proof.
With the next three bushes, this gives precisely the same source
spans \(Q\mathcal P_j\), \(Q=X(X-1)(X-w)\), as in the literal
distinct-tail packet. Thus the fixed-horizon exclusion also
applies independently of the initial six order-five coefficients.
The ghost can use any admissible pure-through-five clock whose
causal relay supports the stated exact decoder.

## Last two slots and the aggregate moment tests

There are five visible scalar sites, exactly one of them repeated
in the six late physical rows. The anchored degree-nine scalar
lower bound says each visible site has nonzero aggregate weight.
The ordinary marked tests annihilate
\(Q\mathcal P_{5-j}\) for \(j=0,1,2,3\) on the
\(j\)-clock-weighted reverse residual, precisely as in the
invisible collision packet. They therefore force *aggregate*
\(D(1),D(2)\) at each visible site, and respectively a constant
or affine barycentric pressure for the third/fourth read.
These statements do not require exactness separately at the two
physical repeats or require either individual split nonzero.

The latest nonzero late weight cannot be at a singleton:
its own \((1-c_i)b_i\) would be nonzero with no later weighted
tap. It is therefore at one of the repeated rows at clock \(v\).
Let \(x\) be the latest singleton. It must have a later nonzero
weight from the repeat (otherwise its aggregate \(D(1)\) fails).
Its only later possible nonzero weight is at \(v\).
The two exact moment equations force \(x=2v-1\).
Both repeated rows cannot follow \(x\), since then their
aggregate reverse equations would see only their internal tap,
forcing \(v=1\), contrary to visibility. Thus one repeat at \(v\)
lies before \(x\), the other is the last physical row and actually
has nonzero weight. Write \(y,t\) for the prior two singletons
in reverse order. All possible later donor clock sets at \(x,y,t\)
are still \(\{v\},\{x,v\},\{y,x,v\}\):
an extra occurrence of \(v\) changes only the per-clock aggregate.

## Eliminate every rational visible repeat

As in the invisible case, set \(F\) to the hull of the visible
sites and \(\mu_u=\int_0^1 QF/(X-u)\) at a singleton.
The donor tests at \(x,y,t\) give
\[
\begin{split}
 \Lambda&=-\mu_x I_x((X-v)^2)
         =-\mu_y I_y((X-x)(X-v)), \\
 D(x)&=3v\Lambda,\quad
 D(y)=(x+v)\Lambda-\mu_y I_y(X(X-x)(X-v)),\\
 D(t)&=(y+x+v)\Lambda-\mu_t I_t((X-y)(X-x)(X-v)),
\end{split}
\]
where \(I_u(f)=\int_u^1 f\).
The last three must lie on an affine function of the singleton
clock. The formula uses only truthful scalar donor supports,
not any free-tap ansatz.

Write \(F=(X-x)(X-v)(X-y)V\), \(V\) monic quadratic with root
\(t\) and the earliest singleton root. The two exact scalar nodal
moments \(\int QF=\int XQF=0\) are linear in the lower
coefficients of \(V\). In the singular case, both Cramer numerators
would vanish. Eliminating \(y\) between the determinant and either
numerator gives no rational \(v\): all their factors have small
projectively rootless prime receipts, as in the linked packet.
Thus Cramer's rule recovers \(V\) in every rational chart.

Reduce the affine pressure at \(x,y,t\) modulo \(V(t)\) and
eliminate \(t\) exactly; simultaneously impose the equality
defining \(\Lambda\).
The latter numerator, after removing the known forbidden
\(y-x\), has bidegree \((7,2)\) in \((v,y)\).
The \(t\)-resultant numerator, after removing a power of
\(y-x\), has bidegree factors \((6,2)\) and \((14,8)\).
Eliminate \(y\) with each. These two final resultant numerators
have degrees of distinct factors \(6,14\) and \(6,24,36\).
All have explicit projectively rootless prime reductions
(see [exact audit](exact-audit.txt)); there is no rational \(v\).
All factorizations are computed exactly, with the full singular
case included. No bounded search for the clocks is used.

More than one repeat/collision would leave at most seven
anchored sites and already fails the scalar degree-nine gate.
The visible repeat, invisible collision, and no-repeat results
therefore close this normalized single-ghost relay architecture,
even allowing other stage-weight signs, zero weights at anchors
and arbitrary rational scalar meshes. A different \(w\) or \(\xi\),
more than one dirty high mechanism, or a different low-to-high
cross-feed is not excluded here.

## Replay and scope

    python -B audit.py

This note contains the literal rooted and moment reduction. The symbolic
elimination and the prime reductions have exact Python replay; no Lean
verification of the visible-repeat calculation is claimed here.
