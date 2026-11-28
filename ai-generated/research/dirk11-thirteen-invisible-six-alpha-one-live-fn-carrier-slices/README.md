# Two live clock and carrier restrictions from the adjacent quadratic

**Result (characteristic zero).** In the normalized no-late invisible-six
DIRK11/13 direct \(F_n\) branch with \(\alpha=\beta=1\), live reciprocal
multiplier, and both fourth and fifth ordinary diagonals nonzero, the fourth
carrier \(K_*\) is nonzero and the first reverse ghost clock \(z\) cannot
coincide numerically with the fifth ordinary clock \(B\). The hypotheses are
those of the earlier
[adjacent-separable](../dirk11-thirteen-invisible-six-alpha-one-live-fn-adjacent-separable/README.md)
and [fifth-compensator](../dirk11-thirteen-invisible-six-alpha-one-live-fn-fifth-compensator/README.md)
packets. These are two separate exclusions, not a whole-branch or stage-bound
claim. All constructions below are exact over characteristic-zero fields, not
a positivity or order assumption.

## 1. Two paid rows in one monic algebra

Use reverse \(Y=1-c\) and the literal reverse prefix
\(T,v,u,w,z,V,x,B,y\) from the cited proofs. Ordinary locations \(V,B\) are
nonendpoints, the five ordinary clocks are distinct, the fourth/fifth
diagonals are nonzero, and \(x\) and \(z\) are different physical ghost
clocks. As before, \(R=(Y-v)(Y-u)(Y-w)\), \(P_0=YR\), and
\(P=Ym\) with \(m\) the old nonzero quadratic profile. The old adjugate
scale \(n\) and the homogeneous clock denominator \(q\) are live.
Set \(p=qz\), \(Z=qY-p\), \(E=qK_*\), \(Q=ZP+EP_0\).
The matched adjacent primitive identity with
\(L=\lambda(Y-z)(Y-x)\) enforces
\[
 A(E)=q\eta_N Vc_0+x_n[Y]Q=0,
 \qquad x=x_n/x_d,qquad c_0=R(0).
\]
Here \(x_n,x_d,\eta_N\) have the exact definitions in the
fifth-compensator source. This paid quadratic's leading coefficient
\(a_2\) is nonzero by the adjacent-separable result. The true quintic from
the four ordinary fits vanishes at both \(z\) and \(x\); its denominator-cleared
synthetic quotient at \(x\) gives the cubic \(Q_{\rm pin}(E)=0\) in that
same source. All polynomial coefficients here are in a common scaled
reverse coordinate, including the integral primitive. No ghost/clean collision
is assumed absent in this proof beyond earlier independent live guards.

Write \(A(E)=a_0+a_1E+a_2E^2\). Over the monic rank-12 clock algebra \(S\)
with ordered fifth ordinary and direct \(F_n\) parameter, use the single
monic carrier algebra
\[
 \mathcal H=S[e]/(e^2+a_1e+a_2a_0),\qquad e=a_2E .
\]
This finite free algebra has rank 24 over the base field, whether or not any
special fiber is reduced. Actual \(a_2\ne0\) allows evaluation at the true
\(e\). Homogeneous Horner reduction gives an element \(Q_H\) of
\(\mathcal H\) evaluating to a nonzero-scale multiple of the paid
\(Q_{\rm pin}(E)\). The two forbidden slices correspond to an extra row:
\(h=e=0\) when \(K_*=0\), and \(h=Bq-p=0\) when \(B=z\).
In either case both rows vanish in the **same** carrier and clock evaluation.
No independent projection of these two rows is used to decide a fiber.
The extra late ghost \(y\), its denominator, and the late commutator are not
needed.

## 2. Exact seed projections

The program uses the ordinary clock \(V_{\rm unscaled}\) as a free
base variable. The other four ordinary clocks come from the quotient by
\(Y-V_{\rm unscaled}\) in
\(J_4(V_{\rm unscaled})J_5(Y)-J_5(V_{\rm unscaled})J_4(Y)\).
The horizontal scale \(L=132J_4(V_{\rm unscaled})\) makes the four-clock
polynomial monic. For the remaining direct \(F_n\) cubic the variable
is \(s(12c_2)\), again monic by the live \(c_2\).
Their ranks over the base are four and three. Both scaling steps are
verified by the quotient identities in the program.

The extra slice gives a single seed on this rank-12 algebra before
adjoining the carrier:
\(a_0=0\) if \(e=0\), or \(Bq-p=0\) if \(B=z\).
At an evaluation where a seed vanishes, its norm vanishes. The program
removes only base content supported on the proved ordinary guards
\(V(V-1)J_4E_+E_-E_{\rm rep}\); these are the origin, terminal,
pencil-degree, endpoint-contact, and repeated-clock exclusions of the
reviewed clock chart. Constants used to normalize are nonzero rationals.
The remaining exact seed norms have raw/squarefree degrees
**1224/240** and **252/84**, respectively.

| Slice | Irreducible clock factor (degree, constant) | Live mask | Exact cap | Residue degree at 103 | Joint rank |
|---|---|---|---:|---:|---:|
| \(K_*=0\) | 12, 16227 | old ratio denominator | 22 | 12 | 22 |
| \(K_*=0\) | 12, 54123 | \(c_2\) | 18 | 4 | 18 |
| \(K_*=0\) | 48, 1865429207937 | \(q\) | 22 | 1 | 22 |
| \(K_*=0\) | 60, −1461941766456 | \(n\) | 22 | 1 | 22 |
| \(K_*=0\) | 108, 7261365757665534336793103761342611 | 1 | 24 | 1 | 24 |
| \(B=z\) | 12, 16227 | old ratio denominator | 22 | 12 | 22 |
| \(B=z\) | 12, 54123 | \(c_2\) | 18 | 4 | 18 |
| \(B=z\) | 60, 99738554904 | 1 | 24 | 3 | 24 |

## 3. Why the residue ranks give a characteristic-zero exclusion

Fix an exact irreducible factor \(f\) from the table and take the base
field \(F=\mathbb Q[V]/f\). Let \(G\) be the indicated live mask to
the 24th power (powering is safe and does not increase rank).
The exact multiplication rank of \(G\) is at most 24; for the ratio,
\(q\), and \(n\) factors its rank is at most 22, because the program
checks exact divisibility of the rank-12 multiplication norm of the
underlying mask by \(f\). Extension by the monic quadratic doubles the
rank bound. For \(c_2\), its exact norm already vanishes in the lower
rank-four clock algebra. Extending freely by degrees three and two gives
cap \(3\cdot3\cdot2=18\).

Take the simultaneous image
\[
 \operatorname{im}(Gh:\mathcal H\to\mathcal H)
  +\operatorname{im}(GQ_H:\mathcal H\to\mathcal H)
  \subseteq\operatorname{im}(G:\mathcal H\to\mathcal H).
\]
Each finite field rank in the table is for the entire simultaneous image
of these two rows in dimension 24 over the indicated residue field,
not just separately two determinants. Explicit polynomial-vector
elimination uses inverses checked by extended gcd. The leading coefficient
of \(f\) and the coefficient denominators used in this reconstruction are
103-units. Hence any nonzero residue minor is nonzero over \(F\); no true
clock or actual tableau coefficient is reduced. Its lower rank matches
the independent exact upper cap, so the simultaneous image equals the
multiplication image of \(G\). In particular it contains \(G\).
Evaluation at a true candidate then sends \(G\) to zero, since both rows
vanish, contrary to the live mask. This closes all factors on both slices.

Replay with `bash verify.sh` and python-flint 0.9. The arithmetic proof is
an exact executable source certificate; it is not yet a full native Lean
proof of the characteristic-zero branch exclusions.
