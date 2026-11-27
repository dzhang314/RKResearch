# The balanced four-pair ERK10 chart is impossible

This finishes the all-live, independent-quadratic-defect, balanced
four-pair branch of the [14-stage equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md).
Work over **any characteristic-zero field**. No ordering of the
actual tableau's field, weights or clocks is assumed.
The [seven–seven proof](ERK10-BALANCED-SEVEN-SEVEN.md) placed the
four dirty pairs across the two halves and located clean stage
clocks \(0,u,w,y,v,1\) in chronological order, with \(w\) at row 7
and \(y\) at row 8. Its degree-four aliases \(V_L,V_R\) are supported
on the right and left clean sites, respectively. Their nonzero
polynomial models \(P_L,P_R\) both reduce to \(D\bmod G\), where
\(D\) is the monic four-dirty-clock hull and \(G\) is the genuine
quadratic defect shape.

**Conclusion:** this balanced branch contains no actual fourteen-stage
order-ten tableau. The independent *unbalanced* nine-dirty/five-clean
branch, the dependent-defect branch, and zero-weight charts remain
separate. This does not yet improve the unrestricted 14–15 interval.

## Two literal linear seam tests

Write \(G_{\rm raw}\) for the actual quadratic with \(d=G_{\rm raw}(c)\)
on dirty rows, and \(G=G_{\rm raw}/\operatorname{lc}(G_{\rm raw})\)
for its monic normalization. Normalization does not change the
residue ring, nor \(P_L=D-G_{\rm raw}Q_L\) and \(P_R=D-G_{\rm raw}Q_R\):
the interpolating \(Q\)'s can be scaled inversely.
Let
\[
                T=G_{\rm raw}(c)-d .
\]
It is an actual grade-two vector with model \(G_{\rm raw}\), supported
only on clean rows.

The grade-four vector \((C-v)(C-1)T\) can be nonzero only on the
three left clean rows and on row 8. On the other hand \(A V_L\)
is zero through row 8, since \(V_L\) is zero on rows 1–7
and \(A\) is strict. Thus their actual Hadamard product is zero.
The paid product costs \(5+4=9\), giving, after cancelling the
leading coefficient of \(G_{\rm raw}\),
\[
          \int_0^1 (J P_L)(X)G(X)(X-v)(X-1)\,dX=0.        \tag{1}
\]
In the genuine reversed method \(A^\star V_R\) vanishes from
row 7 onward. The grade-four vector \(C(C-u)T\) is zero on
all dirty rows and on the only earlier clean rows, 1 and the
row with clock \(u\). This actual product is zero as well.
Converting the reflected model back to the physical clock gives
\[
          \int_0^1 (\bar J P_R)(X)G(X)X(X-u)\,dX=0,\qquad
                              \bar J P(X)=\int_X^1P .    \tag{2}
\]
These are not integrations of an invented midpoint tableau;
each is a paid product of actual numerical stage profiles.

## A shared two-dimensional residue and its exact matrix

Let \(R=D\bmod G=r_0+r_1X\). This is **one common, nonzero**
element of the two-dimensional \(K\)-space \(K[X]/(G)\).
If it were zero then \(G\) would divide \(D\), which splits
into four different dirty clocks where \(G\) is nonzero.
The left model \(P_L\) is a linear multiple of
\(q_L=X(X-u)(X-w)\); the right model \(P_R\) is a linear
multiple of \(q_R=(X-1)(X-y)(X-v)\).
Both \(q_L,q_R\) are units modulo \(G\), by the six clean
noncontacts. For each residue the two model polynomials are
therefore obtained *uniquely* by multiplying by those cubics
after inverting their residue-multiplication matrices.
Consequently (1) and (2) are two **linear equations on the
same pair** \((r_0,r_1)\), not independent unknown residues.

All coefficients of this two-by-two matrix depend only on the
clean chronology. Explicitly, write \(G=X^2-h X+g_0\),
\(\eta=1-v\); the two already paid first-clean primitive tests
give
\[
 h=\frac{3u^2-3\eta^2+8\eta-6}{4(u+\eta)-6},\qquad
 g_0=\frac{4hu-3u^2}{6}.
\]
The denominator is nonzero because its zero would be
\(u-v=1/2\), excluded by the half-shift Lobatto Bézout gate.
For a monic cubic \(q=X^3+q_2X^2+q_1X+q_0\)
and \(g_1=-h\), the vector of \(1,X\)-coefficients of \(q\bmod G\)
is
\[
 (a,c)=(q_0-g_0q_2+g_0g_1,\ q_1-g_1q_2+g_1^2-g_0).
\]
The next column is that of \(Xq\bmod G\),
namely \((b,d)=(-g_0c,a-g_1c)\).
Invert this two-by-two matrix to get the lift of each of the
basis residues \(1,X\). If \(l,r\) are coefficient vectors,
\[
 M(l,r):=\int_0^1(Jl)(X) r(X)\,dX
                =\sum_{i,j}\frac{l_i r_j}{(i+1)(i+j+2)} .
\]
Use \(M\) directly in (1); in (2) use
\(\int (\bar J P_R)Q=\int (JQ)P_R\).
These formulas are the direct arithmetic of the companion.

## Every algebraic clock ordering has nonzero determinant

With the four internal real Lobatto roots numbered increasingly,
the exact determinant sign table is:
- positive: 1234 1243 1324 2134 2143 2341 2413 2431 3421
  4123 4213 4231 4312 4321;
- negative: 1342 1423 1432 2314 3124 3142 3214 3241 3412 4132.

The first check in [ERK10BalancedSeamDeterminants.lean](ERK10BalancedSeamDeterminants.lean)
establishes disjoint ordered rational brackets in \((0,1)\) with opposite
quartic signs at both endpoints of each interval. Each contains exactly one
root of \(L=42X^4-84X^3+56X^2-14X+1\) by real continuity and the
degree-four root bound. The other twenty-four checks evaluate the
matrix formulas above with **directed integer interval arithmetic**.
For fixed unit \(2^{160}\), addition is exact, multiplication takes
the four endpoint products and rounds outward, and a reciprocal is
only used on an interval strictly separated from zero. Its lower
and upper bounds are the scaled reciprocals of the high and low
endpoints, rounded down and up. Each checked determinant interval
is strictly separated from zero. This proves the stated nonzero
determinants exactly, without floating-point or numeric-root
assumptions. The closed-integer checks use kernel evaluation and
do not depend on any axioms. The interval enclosure reasoning and
the rooted seam proof are mathematical.

Finally, if the given coefficient field is not ordered, its
subfield generated over \(\mathbb Q\) by \(u,w,y,v\) is still a
splitting field of \(L\). All four complex roots of \(L\) are real,
as the four disjoint real brackets already show. The splitting
field therefore has an embedding into \(\mathbb R\) sending the
four distinct chronological clocks to one of the 24 listed
permutations. The coefficients of both rows of the tested matrix
belong to this splitting subfield, since the monic \(G\) has the
displayed formula. A determinant nonzero in its real image is
nonzero in the original field, even if \(D\), its remainder and
the other stage data do not embed into \(\mathbb R\).
The two homogeneous equations now force \(R=0\), contradiction.
