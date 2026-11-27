# Exact ERK9 in fifteen stages over every factorial-unit local ring

Two explicit rational tableaux of width fifteen now cover all
nontrivial **local commutative rings** in which \(9!\) is a unit,
and also all nontrivial **finite-characteristic commutative rings**
paying that factorial. No field, positivity or completeness is
needed for these statements. This is a two-tableau result, not a
single tableau over \(\mathbb Z[1/210]\), and does not replace the
sixteen-stage bound over arbitrary factorial-unit rings.

## Exact input and replay

The first tableau and its complete rational/integer audit are
[separate](../erk9-fifteen-rational-moment-splice/README.md).
For the second take the same rational prefix and the same
eight-site construction, now with
\[
 (\xi,v,w,z)=(-3/2,1/4,-1,-5/9),\qquad t=26083/35353,\qquad h_w=0.
\]
The [second literal tableau](second-tableau.json) is strictly
explicit with fifteen distinct physical rows and passes all 486
rooted order conditions. The independent replay reads only the
literal coefficients and computes with integers throughout after
one common denominator scaling.

Write \(D_1,D_2\) for the two literal common denominators. The
replay verifies the exact arithmetic
\[
 \gcd(D_1,D_2)=10450944000\mid (9!)^3 .
\]
The second witness has tenth tall and bush defects
\(-2945609/320\) and \(71019553/1282889664\).
Their cleared numerators are coprime. The same is true of the
tenth bush and the shallower tree obtained by attaching the
seven-vertex bush to the root of the three-vertex bush. That
tree has cleared defect
\(-24755745567906941/5885687017987200\).
Thus exactness of each witness separately survives every unital
specialization in which its own common denominator is a unit.
In particular, in characteristic 11 the second witness retains
a nonzero tenth tall defect even though its tenth bush vanishes.

## Coefficient-domain conclusion

In a local ring with \(9!\) a unit, the displayed gcd is a unit.
The two denominators cannot both belong to the maximal ideal,
since then their integer Bézout combination, this gcd, would
belong to that ideal. Thus at least one of the two literal
tableaux is available. Its rooted equations and compensated
next-order defect specialize without change.

If the characteristic is a positive integer \(N\), split the
coefficient ring by the idempotents supplied by the ordinary
integer CRT for the prime-power factors of \(N\). On a
\(p\)-primary factor, \(p\ge11\) because \(9!\) is a unit, and
at least one of the denominators is prime to \(p\) and hence a
unit. Apply that literal tableau on that factor, and join the
equal-width tableaux coordinatewise in the product ring.
The order equations are polynomial identities, so they hold in
the product; an order-ten equality in the product would imply
it on every nonzero factor, contradicting exactness.

These are mathematical specializations of exact integer
certificates, not claims of a verified native Lean portfolio.

    python3 replay.py
    sha256sum -c source-sha256.txt
