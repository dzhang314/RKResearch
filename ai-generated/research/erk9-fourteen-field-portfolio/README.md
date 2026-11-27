# Two exact fourteen-stage ERK9 tableaux cover fields of characteristic zero or greater than 11

The [primary rational signed-triple witness](../erk9-fourteen-rational-triple/README.md) and the distinct [complementary two-pair witness](tableau.json) form a portfolio. For every field of characteristic zero or prime characteristic \(p>11\), **at least one** of them gives exact order nine in fourteen strict explicit stages. This is a choice between tableaux, not a single universal tableau. No fourteen-stage existence or nonexistence is asserted in characteristic 11.

## Exact coefficients and specialization

The [Lean-certified primary witness](../erk9-fourteen-native-upper/README.md) has denominator
\[
       D_1=2^8 3^9 5^3 7^2\,11\cdot13\cdot19\cdot47
          =3941167085856000 .
\]
For any nontrivial commutative ring in which \(D_1\) is invertible its order-nine conditions hold and the ten-vertex bush has normalized defect \(-1/2160\), so it does not have order ten.

The complementary rational tableau uses denominator
\[
\begin{aligned}
 D_2&=2^7 3^7 5^2 7^2\,11\cdot17^6\cdot23\cdot67\cdot223\cdot331\cdot1879\cdot2267\\
    &=44115870234031229210137015593600.
\end{aligned}
\]
The independent exact integer replay verifies all 486 rooted conditions through nine. Each cleared identity is a polynomial identity over the integers, so it holds after specialization wherever \(D_2\) is a unit. Its tenth tall defect is \(-5080814508937/11095570160\). In characteristics 13, 19 and 47, respectively, \(D_2\) is invertible and this actual defect is \(11,13,36\), all nonzero. Thus these three characteristics are covered by the complement; all other allowed field characteristics are covered by the primary.

The same reasoning works over every nontrivial **local** commutative ring in which \(11!\) is a unit. If \(D_1\) is not a unit, the residue field characteristic must be one of \(13,19,47\). Then both \(D_2\) and the complementary tall defect are units, as their reductions are nonzero. No such conclusion is asserted for arbitrary non-local rings in which neither \(D_1\) nor \(D_2\) is a unit, and the factorial-only arbitrary-ring bound is not replaced.

## Construction and the limit of this scalar mesh

The complementary tableau has the same six canonical opening clocks \(0,1/10,1/5,3/10,3/4,4/5\), and new weighted sites at \(1,-3,3/17,1/2,3/5,5/6\). Its actual reverse high order is \(1,A,B,A',B',C,D,E\) with \(A=-3,\ B=3/17,\ C=1/2,\ D=3/5,\ E=5/6\). Both pair weights split equally; all order conditions are for ordinary ERK, not a positivity-constrained subclass. The scalar rule is interpolatory and exact through degree eight. The two-pair signed transpose construction is the same as the [real-algebraic two-pair model](../../upper-bounds/real-algebraic/erk14-order9-six-opening-two-pair/README.md), with a different rational clock mesh and lower scalar precision. The cubic pressure parameter is \(7293/29618\); the last free old donor tap is \(-237572/451575\). The scripts reconstruct the literal coefficients, then separately check all 486 tree identities and both true order-ten failures (bush and tall).

For perspective, the finite replay also checks that no scalar degree-eight quadrature modulo 11 can be supported on seven sites **including 0 and 1 as nodes**. Any smaller such set can be padded by zero-weight sites. For each of the \(\binom{9}{5}=126\) possibilities, the seven-node hull \(Q\) and \(XQ\) cannot both have zero formal integral. This explains why this seven-node architecture cannot furnish the missing characteristic, but does not exclude other tableaux in that characteristic.

## Reproduce

From this directory:

    python3 -B construct.py
    python3 -B verify.py
    sha256sum -c sources.sha256

Both scripts require only the Python standard library. The complementary order check and finite-field residues here are exact independent arithmetic, not an assertion of a second end-to-end Lean certificate.
