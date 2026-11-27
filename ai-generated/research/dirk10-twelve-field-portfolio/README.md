# Two rational 12-stage DIRK tableaux cover all admissible field characteristics

The [first tableau](../dirk10-twelve-rational-three-ports/tableau.json) and [second tableau](tableau-alternate.json) are two literal unequal-diagonal 12-stage methods. Each has exact order ten over \(\mathbb Q\). Their common stage-and-weight denominators are
\[
 \begin{aligned}
 D_1 &= 101588047290852467338246934187117072000,\\
 D_2 &= 27200218281512417863777752865356303988517513768290967792990592000 .
 \end{aligned}
\]
The independent replay checks the actual lower triangularity, distinct stage rows, unequal diagonals, and **all 1,205** rooted conditions of **each** tableau, with integer denominator clearing. No floating-point step is used.

This supplies a 12-stage exact upper bound over **every field of characteristic zero or prime characteristic \(p\ge11\)**. More generally it holds over every nonzero commutative **local** ring with \(10!\) invertible, and over every nonzero commutative **finite-characteristic** ring with \(10!\) invertible. It does not claim that 12 is minimal in every field, nor a 12-stage upper over arbitrary rings where \(10!\) is a unit. The known rational minimum is 12 and the real-algebraic minimum remains 11.

## The second literal method

Use the same [three-merge rank-one construction](../dirk10-twelve-rational-three-ports/README.md), with centered pair and terminal parameters
\[
           a=1/2,\qquad c=1/4,\qquad b=\frac{3c^2-2}{6c^2-3}=\frac{29}{42}.
\]
The opening stages are at
\[
     (0,1/7,1/4,1/2,51005/77864,13/84,3/8).
\]
The reverse weighted sites are
\[
     (1,3/4,1/4,71/84,5/8,3/8,13/84,1/2);
\]
the origin's weight again goes on the old zero row. The final three reflected sites correspond to the literal protected chronology \(u=1/2,q=13/84,r=3/8\). The one available forward causality equation gives \(p=51005/77864\). The last-four hull gate holds since \(6bc^2-3b-3c^2+2=0\). The actual constructor separately checks all 31 reflected words, all three full row identities, and coefficientwise equality with the JSON export. The repeated clock \(1/4\) in the completed tableau belongs to two **distinct** actual rows.

## Exact failure at order eleven

The first tableau has normalized eleventh-bush defect \(1/2488320\), a unit after inverting \(D_1\). For the second tableau, the normalized eleventh-bush defect is \(19891/520224768\). Another actual size-eleven tree, with three leaf children and one seven-vertex bush child, has tree factorial \(77\) and normalized defect \(-3253/247726080\). Both denominators divide \(D_2^2\). The exact identity
\[
                         -907(19891)-5546(-3253)=1
\]
shows that the two next-order conditions cannot both hold in **any nonzero ring inverting \(D_2\)**. Consequently this second tableau itself has exact order ten on its full denominator localization, even where the bush fails to detect order eleven. The shape checker independently evaluates both tests.

For the coverage proof the stronger unit-bush version is sufficient:
\[
             \gcd(D_1,D_2)=\gcd(D_1,19891D_2)=2^7 3^5 5^3 7 .
\]
The only primes larger than seven dividing \(D_1\) are \(11,17,19,151,173,607,653,1063,1499,1553\). The [exact residue replay](audit.log) reports a nonzero \(D_2\) and a nonzero normalized eleventh-bush defect in each of these fields; for example, the latter is \(10,16,2\) at \(11,17,19\) respectively.

## Where the coverage transfers

- **Fields or local rings.** In a nonzero local ring with \(10!\) a unit, the characteristic of its residue field is zero or a prime at least eleven. If \(D_1\) is nonzero in that field, \(D_1\) is a unit in the ring and the first choice works. Otherwise the gcd calculation makes both \(D_2\) and \(19891\) units, so the second choice works. In either case the normalized next-bush defect is a unit. This includes arbitrary extensions of any of the covered prime fields.
- **Finite characteristic.** If the ring's characteristic is \(n>1\), coprime to \(10!\), partition its prime powers into two factors \(n_1,n_2\): \(n_1\) has the primes not dividing \(D_1\), and \(n_2\) the primes dividing \(D_1\). Chinese remaindering along the corresponding ideals splits the ring into the two factors of characteristic dividing \(n_1\) and \(n_2\). Use the first tableau on the first factor and the second tableau on the second factor, ignoring a trivial factor. The normalized order equations hold componentwise. The normalized next-bush defect is a unit on each nonzero factor, hence a unit in the product. The physical width remains twelve.
- **General rings.** A nonzero ring may invert \(10!\) without inverting either whole tableau denominator or admitting the indicated idempotent split, for example \(\mathbb Z[1/210]\). Local choices alone do not build a single tableau there. There is no unconditional transfer to such rings.

## Exact replay

From this directory, with both portfolios under ai-generated:

    python3 -B audit_portfolio.py
    python3 -B build.py --emit /tmp/dirk-twelve-alternate.json
    cmp tableau-alternate.json /tmp/dirk-twelve-alternate.json
    python3 -B build.py --which base --emit /tmp/dirk-twelve-base.json
    cmp ../dirk10-twelve-rational-three-ports/tableau.json /tmp/dirk-twelve-base.json
    sha256sum -c sources.sha256

Both programs use only the Python standard library. The independent audit reads the two literal matrices; it does not rely on the constructor's modular scout, word proof or row redirects. The previous [first-tableau Lean certificate](../dirk10-twelve-native-upper/README.md) already proves its exact order on its denominator localization. The alternate numerical and coefficient-domain proof is recorded here separately from any kernel receipt.
