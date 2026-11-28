# The old affine slope minus one is impossible in the live direct Fn chart

**Result.** In the normalized invisible-six no-late DIRK11/13
profile with live reciprocal multiplier, \(\alpha=1\),
\(\beta=1\) or \(2\), and the direct \(F_n\) old profile,
the old affine slope \(\ell_1=-1\) is impossible over
characteristic-zero fields. No nonzero diagonal assumption
is needed. This does not exclude the remaining direct
profile, or the separately defined \(F_1\) profile.
The unrestricted real DIRK11 interval stays **13–14**.

We use the
[old-profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md)
and the three exact gates of the
[small-contact proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-small-contacts/README.md).
In particular the literal first middle ghost and its
live affine fit are the ones justified by the
[gap-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md).
Here \(R=Y^3+c_2Y^2+c_1Y+c_0\), \(m=Y^2+rY+s\),
\(P=Ym\), \(P_0=YR\), \(z\) is the first-gap ghost,
and \(V,B\) are the fourth and fifth regular reverse
clocks. The old denominators \(r,s,c_0,c_2,c_1+6s\)
and the old \(m\) values are live.

## 1. The exact slope contact

In the actual affine identity \(IP=\ell P+\delta P_0\),
\(\ell_1=-1\) would mean \(\ell=-(Y-z)\) and
\(\delta=5/4\). Comparing coefficients after cancelling
the polynomial \(Y\) gives
\[
 c_2=16r/15-4z/5,\qquad c_1=6s/5-4zr/5,\qquad
 c_0=-4zs/5 .
\]
In particular \(16rs=15(c_2s-c_0)\). Combining it
with the true direct \(r=6c_2 s/(c_1+6s)\) gives
\[
 H_2(s)=2c_2s^2+(30c_0-5c_1c_2)s+5c_0c_1=0 .
\]
Its exact resultant with the old \(F_n\) is
\(32c_0c_1c_2^3 W\), where
\[
\begin{split}
 W={}&24300c_0^3-7560c_0^2c_1c_2+90c_0^2c_2^3\\
     &+864c_0c_1^3+465c_0c_1^2c_2^2-80c_1^4c_2 .
\end{split}
\]
The exact coefficient identity is checked before any
ordinary pencil specialization.

If \(c_1=0\), the direct formula gives \(r=c_2\);
\(H_2=0\) gives \(s=-15c_0/c_2\).
The literal \(F_n=0\) then gives \(270c_0+c_2^3=0\)
after cancelling the live factors \(s,c_0,c_2\).
Projecting the two ordinary tests separately gives,
up to nonzero constants,
\[
 J_4(V)^3 f_{12}(V),\qquad J_4(V)^6 f_{36}(V),
\]
with irreducible factors of degrees 12 and 36.
They are coprime, and \(J_4(V)\ne0\). Thus \(c_1=0\)
cannot occur here.

## 2. The remaining exact degree-60 field

For \(c_1\ne0\), \(W=0\). The exact clock construction
deflates \(T_5=(J_5+\mu J_4)/132\) first by \(Y-V\),
then by \(Y-B\), using \(\mu=-J_5(V)/J_4(V)\).
All original ordinary quintic roots are distinct
and neither endpoint. Clearing the quartic leader,
substituting into \(W\), and taking the pseudo-remainder
removes only content proportional to \(J_4(V)^6\).
The leader and this content are both live on the actual
chart. The resultant then factors into \(J_4(V)^8\)
times a single irreducible degree-60 factor \(f_{60}\)
with primitive constant coefficient \(-201158165054107372869\).

Use the exact linear penultimate subresultant to
recover \(B\) over the monic degree-60 algebra.
Likewise the penultimate linear subresultant of
\(F_n,H_2\) recovers \(s\), and then the exact
old direct formula gives \(r\). Both subresultant
leaders and all subsequent used denominators are
units in the entire residue algebra at 101, checked
by exact inverse products. They are therefore units
in the characteristic-zero algebra. This keeps
every root of \(f_{60}\); it does not select a
numerically convenient ordinary clock ordering.

The grade-six matched read at \(V\), genuine quintic
primitive, and true first-middle commutator after
\(d_x=0\) give gates of degrees at most \(2,3,4\) in
\(E=q K_*\), exactly as in the linked small-contact proof.
With the full degree-60 basis and carrier cap 5,
the matrix has rank **360/360** modulo 101. Thus the
exact rational multiplication map contains the constant 1
in its image and no common zero is possible in a
characteristic-zero field. No reduction of \(E\) or
of unknown tableau entries is used.

Run **python3 clock.py** and **python3 rank.py** with
SymPy and python-flint 0.9. This is a reproducible
written and arithmetic source proof; it does not claim
a native Lean tableau nonexistence theorem.
