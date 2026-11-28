# The affine live-star transport at a fourth or fifth early root

In the [eight-distinct live-star chart](../sdirk-eight-eight-zero-affine-early-star/README.md), suppose instead that the nonconstant affine numerator root \(q\) occurs at the fourth or fifth actual zero read, physical row 6 or 7. It is live by the separate silent-root exclusion. The first three actual zero labels \(a,b,c\) are singleton labels other than \(q\).

**Result.** This chart also is impossible over characteristic-zero fields. Hence an actual zero label cannot be the reverse affine numerator root in **any** live-star phase here. The externally located affine root and the finite-gap phases with later roots remain separate.

## Transport to the already verified last seven-label equations

Normalize as in the earlier affine live-star proof. Let \(\sigma=(T-a)(T-b)(T-c)\), \(m=D-2\), \(Y=T-m\), \(s=m+1\), \(q=m+w\), \(x=m+\xi\) with \(x\) the other later early label. The early quintic is \(P_5=\sigma(Y-w)(Y-\xi)\). The two relative-cardinal masks from the gap-free proof become, after removing the common early factor \(\sigma(Y-\xi)\) from their expressions,
\[
 R=(Y-w)(Y+w)(Y-1),\qquad
 R'=(Y-w)[(1-w)Y-(2-w)].
\]
Their ordinary integrals after multiplying by that common factor are zero. An exact polynomial identity gives \(R+R'=(Y-w)(Y^2-2)\). Thus the two ordinary mask equations are **identical** to the two in the [last seven-label star proof](../sdirk-eight-eight-zero-star-unequal-late/README.md#1-two-ordinary-rows-with-a-cubic-peak-gap-projection), with its gap variable \(\delta\) replaced by \(w\). We do not assume that \(q\) is a physical rear site in this transport.

The actual \(F_4|_U\) singleton modes are \(L_4,K(T,q)\) with no jump on \(a,b,c\). Thus the same cubic third-read transfer and \(C_3(c;D)=0\) apply. The gap-free *actual* ordinary root weight satisfies
\[
 b_q=\frac{I_D(\sigma(Y-\xi)(Y-1))}
           {\sigma(q)(q-x)(q-s)} .
\]
Hence its correction \(-D^6/b_q\) agrees exactly with the split-free correction in the seven-label algebra. The fourth read is consequently identical in each of its two chronologies: isolated \(x\) if \(q\) is row 7, or the corrected physical \(q\) if it is row 6. This gives both of the same cleared fourth-read minors with the same signs and masks.

The downstream proof of the seven-label equations uses only these transferred row identities, the initial \(a,b,c\) gates, the actual first-two mode rank, and \(D\ne0\). In particular the guarded norm does **not** remove any factor merely because \(w=0,\ w=\pm1,\ 2-w^2=0\), or \(w\) originally parameterized a pair of rear clocks. Its exact degree-30 Hankel rank factor, degree-18 fourth-read factor, and leading-drop branch thus apply unchanged. All the required distinctness used to justify the actual reads and low-degree quotients holds here. No extra order-nine quadrature equation has been assumed.

## Replay

Run `python ../sdirk-eight-eight-zero-star-unequal-late/check_unequal_late.py` with SymPy 1.14 and Python-flint 0.8. This is the existing exact full-algebraic-fibre verifier, with no substitution or change to its inputs. The mask transport itself is checked in [Lean](../../lean/RKCert/Research/SDIRKEightEightZeroAffineFiniteMasks.lean); the remaining kernel and fourth-read scalar gates are the previously staged ones.
