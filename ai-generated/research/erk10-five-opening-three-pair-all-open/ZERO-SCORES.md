# The three-pair exit allows arbitrary physical zero scores

The [three-pair all-open exclusion](README.md) remains true with **no
nonvanishing condition on the physical scores**. Only the three pair
masses \(W_a,W_b,W_c\) must remain nonzero. This addendum uses the same
raw \(K=B^T\) observer spaces and does not invert a zero score.
The grade-one vector used below is
\(\boldsymbol v=K\boldsymbol w-\boldsymbol w\odot\boldsymbol y\).

A physical high row with \(w_i=0\) and zero row \(K_{i,*}\) is inert:
its value in every raw reverse observer vector is zero, including
\(\boldsymbol w\). Delete it from all words, from \(B\), and from the
clock data. Every word test and the scalar precision condition remain
true, since no later forward row used that stage. If \(\dim D_4=3\),
this is impossible: after deletion, the remaining nine high rows
still have at least two distinct nonzero forward clocks, and the
same rank proof gives \(\dim D_4\le 9-5-2=2\). Restricting the defect
space to the remaining rows is injective, so its dimension did not
decrease.

## No grade-four leakage

Assume \(D_4\subseteq S\), so the cubic effective-tap determinant
from the main proof applies. If two or three opening scores are zero,
the first closed group \(z\) has at most one nonzero-ordinate scalar
donor weight available: if it has just one at \(p\), its moments
require \(z=3p/2\) from \(Y,Y^2\) and \(z^2=2p^2\) from \(Y,Y^3\),
contradicting \(p\ne0\). If it has none, its \(Y\) moment already
fails.

If exactly one opening score is zero, it must be at the **first
closed** label \(z\): a zero-score opener at \(j\) or \(k\) would
make the corresponding column of the two-closure determinant
identically zero. The other two available donors have nonzero scores.
By applying \(K((\boldsymbol y-z)\odot\boldsymbol u)\) as in the
main proof, both of their \(\boldsymbol u\) entries must vanish.
This is impossible: the chronological first opener with nonzero
score has \(u_p=-w_p p^2/2\ne0\), and is not the zero-score opener
\(z\). The no-zero-opener branch is proved in the main note.

## Leakage: two general observations

Assume \(D_4\not\subseteq S\), so \(\dim(D_4\cap S)\le2\).
A mode at a label means a nonzero vector supported at its two
opposite positions, irrespective of the physical scores.

1. If \(D_4\cap S\) contains two separate pair modes, then
   \(\dim D_4=3\). In particular \(w_0\ne0\): otherwise the initial
   \(y=0\) row is itself inert and the preceding deletion argument
   applies. Any third-label entry in any grade-at-most-three
   vector must vanish, since that vector lies in \(S\).
2. Suppose grade at most three supplies the two modes at \(a,b\),
   and \(w_{c_1}\ne0\). At \(c_1\) the first two primitive moments
   are exact. For either \(a,b\) with nonzero opening score,
   normalize its mode to that score; the mean tap is forced by
   comparing its \(K\)-image to the value at \(c_1\), exactly as in
   the main proof. If that opening score is zero instead,
   the effective *scalar* tap into its open copy is identically
   zero at \(c_1\) and at all compared groups until that label is
   closed. At least one of the two effective scalar taps at \(c_1\)
   is nonzero by its first primitive moment; its respective
   \(K\)-image is a valid third basis vector. The remaining
   \(c^2\ell+2cT,c^3\ell+3c^2T,c^4\ell+4c^3T\) calculation is
   unchanged and excludes the first two closures.

## Leakage: exactly one zero opener

If the zero opener is \(c_1\), then \(a_1,b_1\) are live and
\(u_{a_1}\ne0\).
If \(\boldsymbol u\) is active at \(b\), its marks supply the two
\(a,b\) modes (a third active label is impossible).
If \(b\) is inactive, its first-primitive equation forces a nonzero
tap on \(a_1\), so \(h_{b_1}\ne0\). If \(c\) were active in
\(\boldsymbol u\), its two \(a,c\) modes and \(h_{b_1}\ne0\)
would violate the pair dimension. If \(c\) were active in
\(\boldsymbol h\), the profiles \(\boldsymbol h,\boldsymbol y\odot
\boldsymbol h\) would supply both \(b,c\) modes (its \(a\) pair
is zero); again impossible. Thus \(a,b\) are the two individual
modes, and \(u_{c_1},g_{c_1},v_{c_1}\) all vanish. The first two of
these kill the actual \(K_{c_1a_1},K_{c_1b_1}\) by the invertible
two-label moment matrix, since \(a,b\) are live and \(w_{c_1}=0\).
The last kills \(K_{c_1,0}\), because \(w_0\ne0\) by observation 1.
The zero opener is inert, contradiction.

If the zero opener is \(b_1\), then \(u_{a_1}\ne0\).
If \(u_{b_1}\ne0\), \(\boldsymbol u\) and its mark supply
the \(a,b\) modes and observation 2 applies. If \(u_{b_1}=0\),
the equation \(K_{b_1a_1}w_{a_1}a=0\) kills \(K_{b_1a_1}\),
so \(h_{b_1}=0\). If \(u_{c_1}\ne0\) we already have the
\(a,c\) modes. Otherwise \(u_{c_1}=0\) forces
\(K_{c_1a_1}w_{a_1}a=w_{c_1}c^2/2\ne0\), because \(b_1\)
is score zero. Hence \(h_{c_1}\ne0\), and \(\boldsymbol h\)
is supported only at \(c\). Again we have the \(a,c\) modes.
Now \(v_{b_1}=0\) forces the endpoint tap zero, so \(b_1\) is
inert and observation 1 applies.

If the zero opener is \(a_1\), then \(u_{a_1}=0\), but
\(u_{b_1}=-w_{b_1}b^2/2\ne0\). If \(u_{c_1}\ne0\) we have the
\(b,c\) modes. Otherwise the zero first-primitive discrepancy at
\(c_1\) forces the nonzero tap \(K_{c_1b_1}w_{b_1}b=w_{c_1}c^2/2\).
It follows that \(h_{c_1}\ne0\), so \(\boldsymbol h\) supplies the
\(c\) mode, and \(\boldsymbol u\) the \(b\) mode. Then \(v_{a_1}=0\)
makes \(a_1\)'s only prior tap onto the endpoint zero. Again the
zero opener is inert.

## Leakage: two or three zero openers

All three cannot have zero score, because the first closure
could not pay its nonzero grouped \(Y\) moment. If just one
opening score is nonzero at \(p\), the first closed group
must be \(z=3p/2\) from its exact \(Y,Y^2\) means. Its effective
tap onto \(p_1\) is \(z^2/(2p)\ne0\). Since \(u_{p_1}=-w_p
p^2/2\), its exact group mean for \(K\boldsymbol u\) requires
some other first copy \(r_1\) to have nonzero \(\boldsymbol u\)
entry. The two labels \(p,r\) thus give separate modes, and a
third mode is impossible. Let \(q_1\) be the other zero opener.
It has \(u_{q_1}=h_{q_1}=v_{q_1}=0\). If \(p_1\) precedes
\(q_1\), then \(u_{q_1}=0\) kills that tap, as \(p_1\) was the
only possible earlier donor with nonzero \(w_i y_i\).
If \(r_1\) precedes \(q_1\), then \(h_{q_1}=0\) kills that
tap, as \(u_{r_1}\ne0\), the tap on \(p_1\) is already absent,
and \(u_0=0\). Finally \(v_{q_1}=0\) kills the endpoint tap.
Thus \(q_1\) is inert, contradicting observation 1.

These arguments allow arbitrary zeros among the three closing
copies, singleton rows, and endpoint. Zero *total mass of a
pair* is a different case and is not included here.
