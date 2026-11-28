# Exact exclusion of the normalized α=0 live cubic DIRK11/13 chart

**Result.** The normalized invisible-six, no-late-ghost, cubic
\(\alpha=0,\tau\ne0\) chart has no characteristic-zero tableau, for
all three surviving chronology counts \(\gamma=3,4,5\). Here \(\alpha=0\)
means no ghost before the fourth ordinary reverse stage; \(\gamma\)
counts the initial forward ghosts, and \(\beta=6-\gamma\) counts the
ghosts between ordinary reverse stages four and five. All assumptions
are those of the [compact projection](../dirk11-thirteen-invisible-six-cubic-compact-projection/README.md)
and the linked signed rooted-order ingress. In particular the coefficients
may lie in any field of characteristic zero, and no sign assumptions
on weights or taps are used. This does not claim an exclusion for other
\(\alpha\), for all thirteen-stage DIRK11 tableaux, or for all
characteristics. The real stage interval is still **13–14**.

Together with the earlier \(\tau=0\) alpha-zero cubic exclusions this
closes the cubic alpha-zero branch within this normalized census.
The calculation uses two independently necessary constraints in
each chronology; a vanishing projected norm is never assumed to come
from the actual profile.

## 1. Generic paired branch: a second exact clock projection

Write \(A,F,D_A,C,U,Q\) as in the compact projection, so \(A/D_A,F/D_A\)
are the actual two first reverse gap readout polynomials,
\(C=F-YA\), and \(Q\) is the four-regular effective quintic fit.
Here \(U,Q\) can each be scaled by a nonzero common coefficient
factor. Their common moment proportionality and divided wedge are
unchanged. Let the ordered first two gap ghosts be \(z,w\).
The [paid divided crossings](../dirk11-thirteen-invisible-six-cubic-live-prefix-third/README.md)
give \(C(z)=0\) and require \(z,w\) to be distinct actual roots of
\[
 a+bY+cY^2=F(Y)-z A(Y),\qquad c\ne0.
\]
Thus \(c(z+w)=-b,\ czw=a\). The divided \(U,Q\) crossing, multiplied by
\(c^2\), is the compact quadratic \(H(z)\) proved in the companion
scalar module. It is the quadratic expression in the six coefficient
wedges in the compact-projection notebook.

For completeness the independent **unmarked** divided commutator
equation has a direct polynomial form. Set
\[
 \begin{aligned}
 d_A &= A_1 c-A_2b,\\
 d_U &= U_1c^2-U_2bc+U_3(b^2-ac),\\
 A_w^\# &= (A_0c-A_2a)c-(b+zc)d_A .
 \end{aligned}
\]
These are respectively \(c\) times the divided derivative of \(A\),
\(c^2\) times the divided derivative of \(U\), and \(c^2 A(w)\).
The last identity follows by replacing \(w^2\) by
\((-a-bw)/c\) in \(A(w)\). Then at the actual ghost pair
\[
 R(z)=U(z)D_A A_w^\# - U(z)A(z)d_A c + A(z)^2 d_U=0.
\]
Indeed multiply
\(U(z)r_0(w)-U(z)r_0(z)D_{r_0}(z,w)+r_0(z)^2D_U(z,w)=0\)
by \(c^2D_A^2\), with \(r_0=A/D_A\). Only actual distinctness
is used in the original divided crossing; no residue ghost clocks
need remain distinct. The third ghost and fourth-prefix extra reads
are not needed for this conclusion.

Use the nominal Sylvester determinants of \((C,H)\) and of
\((C,\operatorname{prem}(R,C))\). A joint root gives a determinant
zero even if an intermediate leading term drops. The second
pseudo-remainder is valid at every actual root of \(C\);
the cubic leader is live by the earlier
[first-gap proof](../dirk11-thirteen-invisible-six-cubic-live-first-gap-drop/README.md).

The rank-12 monic profile norm of the first determinant has exact degree
**17,296** (after listed coefficient contents) and squarefree degree
**3340**. Exact guard gcds leave a degree-3120 cofactor and the
degree-220 support in **pair-guard-support.txt**. All stripped contents
have radicals dividing that support times \(B-1\), and \(B=1\)
is not an ordinary nonendpoint site. The exact primitive cofactor
has leading coefficient \(18\bmod 103\). Reducing the exact upstream
coefficients and the unstripped second determinant in its
degree-preserving residue yields the displayed Bézout witness.
By the same monic-factor argument as in the compact projection,
no characteristic-zero root can lie in the 3120 cofactor. This is an
exact projection over \(\mathbb Q\), not a pointwise 103-adic restriction.

## 2. Closing both exact specialization supports

The five-prefix support and paired support each have eight exact
irreducible factors with degrees \(4,4,16,24,24,28,60,60\).
The first seven factors are identical, in the recorded FLINT factor
order; the last degree-60 factors are different. These facts are
checked against the frozen primitive integer polynomials, not by
matching modular degree patterns. For each support:

- Factor 0 is \(J_4(B)\), forbidden by Jacobi coprimality.
- Factor 1 forces \(T_5(0)T_5(1)=0\), so an ordinary site would be
  an endpoint. This is checked before dividing by \(J_4(B)\).
- Factor 3 divides the exact projected norm of the ordinary quartic
  derivative; if it vanished, one of the ordinary roots would repeat.
  The actual full ordinary hull has five distinct nonendpoint roots.

For the other factors, let \(K_f=\mathbb Q[B]/f(B)\), the **exact**
field for the particular irreducible formal base factor. The profile
algebra \(A_f=K_f[v,\sigma]\) is the specified monic \(4\times3\) tower,
of dimension 12 over \(K_f\). For paired ghosts adjoin the scaled first
gap variable \(Z=C_3 z\) with its monic cubic: the algebra then has
dimension 36. The actual phase provides a nonzero evaluation homomorphism
out of the appropriate algebra, and sends the two necessary scalar
equations \(E_1,E_2\) to zero.

The guard choices in the following table are actual nonzero quantities,
not assumptions that they are nonzero at every formal conjugate.
Each guard has **exact norm zero in \(K_f\)**, verified by exact division
of the source guard projection by \(f\). Thus multiplication by a
profile guard has rank at most 11. If the guard belongs to the lower
rank-4 ordinary-clock algebra, that rank is at most 3 there and at
most 9 after adjoining \(\sigma\). These exact upper ranks multiply
by 3 after adjoining the monic ghost variable.

| Factor index and degree | \(\gamma=5\) guard, rank | \(\beta\ge2\) guard, rank | Residue factor degree at 103 |
|---|---|---|---:|
| 2, degree 16 | \(F_3\) leader, 9 of 12 | \(F_3\) leader, 27 of 36 | 4 |
| 4, degree 24 | \(IP(v)\), 11 of 12 | \(IP(v)\), 33 of 36 | 1 |
| 5, degree 28 | ordinary-layer \(F_3\) discriminant, 9 of 12 | same, 27 of 36 | 1 |
| 6, degree 60 | old \(m\) determinant, 11 of 12 | same, 33 of 36 | 1 |
| 7, degree 60 | carrier \(U(L)U(LB)\), 11 of 12 | \(a(v)C_3\), 30 of 36 | 1 / 3 |

For the final paired factor the two profile guards \(a(v)\) and \(C_3\)
are independently singular over the *same exact field*. Their
stacked multiplication map on the profile algebra is injective,
verified by full residue rank 36 on a field extension of degree three
at 103. Consequently their two nonzero kernels are disjoint; each
lies in the kernel of multiplication by the product. Its exact rank
is at most 10 at the profile layer and 30 after the ghost adjunction.
This accounts for the rank loss that remains if only \(a(v)\) is used.

For every row, let \(g\) be the listed guard or guard product. The
images of multiplication by \(gE_1,gE_2\) are inside the image of
multiplication by \(g\). The replay finds joint rank **equal to**
the exact upper rank in the table, using the indicated irreducible
residue factor at 103. It measures ranks over \(\mathbb F_{103}\)
as the displayed rank times the residue extension degree. One
nonzero residue minor proves the corresponding lower rank over
\(K_f\); there is no inference of an exact upper bound from a
residue rank. Hence the two images span the entire exact guard
image. Evaluation at any putative actual solution kills both
images, so kills \(g=g\cdot1\). This contradicts its actual liveness.
No inverse is applied across the false guard components. The
\(F_3\) discriminant and cubic leader are live by the earlier
[discriminant](../dirk11-thirteen-invisible-six-cubic-live-discriminant/README.md)
and [leader](../dirk11-thirteen-invisible-six-cubic-live-f3-degree-drop/README.md)
cases, and \(C_3\) by the first-gap proof. The carrier factors are
live at the genuine fifth ordinary and origin clean sites.

## 3. Reproduce

Use Python 3 and python-flint 0.9.0. The complete paired exact
first pass writes a temporary text polynomial of about 300 MB;
the smaller degree-3120 cofactor is about 8 MB. Only its hash
and the small arithmetic certificates are shipped. The source works
sequentially; concurrent copies unnecessarily increase memory.

From this directory use the commands in the compact notebook to
reproduce its exact five-prefix guards and Bézout packet. Then:

    compact=../dirk11-thirteen-invisible-six-cubic-compact-projection
    d=$(mktemp -d)
    mkdir "$d/first" "$d/guards" "$d/proof"
    python3 rank.py --p 0 --trace-guards --write "$d/guards"
    python3 "$compact/project.py" --p 0 --chart pair --first-only --write "$d/first"
    python3 divide-guards-first.py "$d/first/pair-quintic.txt" \
        --guards "$d/guards" --ledger "$d/first/ledger.txt" --out "$d/pair.txt"
    python3 check-pair-support.py "$d/pair.txt" "$d/pair.guards" "$d/first/ledger.txt"
    python3 "$compact/project.py" --p 0 --chart pair --no-extra \
        --verify-over "$d/pair.txt" --verify-prime 103 --write "$d/proof"
    cmp pair-bezout-103.txt "$d/proof/pair-commutator-bezout.txt"
    bash run-guard-ranks.sh "$d/guards"

The optional faster guard-removal helper uses each modular valuation
only as a **proposal**, then performs and checks every actual
division over the integers. The slower exact squarefree-first
method in the compact notebook independently reproduces the same
primitive cofactor and support. The companion Lean modules check
the symbolic marker identities and both Bézout witnesses.
The finite rank calculations are exact source arithmetic certificates;
there is no claim that the whole normalized DIRK exclusion is a
single Lean theorem.
