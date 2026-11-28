# The neighboring singular cross block has no rotated right affine loss

**Scope.** In the ordered, all-live, fixed-full-pair neighboring coincidence with \(q=10,n=12\), take sole dormant physical 9 at active singleton \(s=c_8\notin\{0,1,a,d\}\) and the original right-loss width curve \(K_0(a,b)=0\), \(b=1-d\). Use original \(R_9\) for the left fit and actual \(L_9\) for the right fit. The [initial](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-RIGHT-SLOPE.md), fixed-moment and [left affine](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-LEFT-AFFINE-EXIT.md) exits are already known on this curve. This note excludes the **rotated right raw affine loss on \(K_0=0\)**, and under reflection the corresponding other neighboring coincidence. It leaves the fully pivotable width case and does not change the unrestricted stage count.

## Right raw equations with two distinct measured arguments

Use the [actual right rotated fixed-moment setup](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-RIGHT-MOMENT-EXIT.md): \(\widehat L=\beta' L^\circ-30\alpha'\ell_a\) is a live polynomial multiple of the direction of actual \(L_9\). Pair it against both right derivatives and remove only the common gcd of these two coefficients; it is live because the actual first slope is live. The resulting slopes determine \(B_0,B_1,\phi\) in the reflected coordinate \(Y=1-X\), with \(w=b\). For the independent fourth-row representer one can also divide the row \(\widehat L\) by its component gcd: this just scales the fourth row by a live unit. Its common component factor divides the live raw first right slope. This row normalization need not agree with the hull normalization; the outer equation is linear in the representer, and rescaling both hull slopes just reparametrizes the product.

For the raw right \(g_0,g_1\), use the same four-row determinants as on the left: moment columns \((\phi,YB_0,YB_1,B_i)\) for \(i=0,1\), plus the actual outer row
\[
 w y(y-w) E(0),\quad yS_0(y),\quad yS_1(y),\quad S_0(y),\quad S_1(y)
\]
restricted to the same four columns, with \(E,S_0,S_1\) made from the right representer in \(Y\). The actual \([L_9,R_{10}]=0\) gives this row at \(y=1-z\) with \(z=c_{10}\). Crucially, the moment correction uses a **different** location \(\sigma=1-s\) at the dormant row, and \(s-z\) is live.

The outer entries have \(y\)-degree at most three. Substitute \(y=(z_D-z_N)/z_D\) and first clear its whole row by \(z_D^3\), independently of the three moment rows. At the moment rows use the same \(\rho=-H^6U\beta'/(\alpha'B_NS)\) and correct at \(\sigma=(H-C_2)/H\). After the outer-row clearing the base determinant is width-only and the sum of single moment replacements has \(\sigma\)-degree at most six. Thus the correct width numerator is
\[
 F_i=\alpha'B_NS\,\mathrm{base}_i+U\beta'\,
 H^6\,\mathrm{adj}_i((H-C_2)/H).
\]
Here \(\mathrm{adj}_i\) is the sum before including \(-\rho\), and multiple correction rows again give zero. All these clearings and the deflated factors are live. The true coordinate kernel gives \(g_0+t g_1=0\), so true \(g_1=0\) implies both \(F_0=F_1=0\).

The two raw bidegrees \((81,90),(93,102)\) become \((52,52),(64,65)\). The two \(b\)-resultants with \(K_0\) have degrees 312 and 387, and their common \(a\)-gcd degree 276 with exact irreducible degrees and multiplicities \(3,3,12,12^2,12^4,30,54,102\). In the cubic fields \(165a^3-180a^2+54a-4=0\) forces \(b=0\) and \(30a^3-36a^2+12a-1=0\) has no finite common \(b\). The three degree-twelve fields have exact whole joint linear \(b\)-gcd: multiplicity one forces \(S=0\), the other two force \(U=0\). These are all forbidden.

## Exact slope exits, not inferences from vanishing residues

Let \(G_R\) be the compact bidegree \((9,9)\) factor of the raw rotated right first slope, and \(G_L\) the bidegree \((12,14)\) factor of the raw original left first slope. Their exact divisibilities into the actual raw slopes are checked. The degree-30 \(a\)-factor divides \(\operatorname{Res}_b(K_0,G_R)\), and the degree-54 \(a\)-factor divides \(\operatorname{Res}_b(K_0,G_L)\). These norms have degrees 54 and 78. This says that a guard-zero \(K_0\) root exists for each such \(a\), not yet that the actual width is that root.

At \((p,a,b)=(61,25,58)\) for degree 30 and \((19,6,1)\) for degree 54, the monic exact \(a\)-factor has full degree and simple residue, and \(K_0\) retains \(b\)-degree three. The **whole** residue \(b\)-gcd of \(K_0,F_0,F_1\) is the same linear polynomial as the whole residue gcd of \(K_0,G_R\) or \(K_0,G_L\), respectively. The derivative of \(K_0\) at that root is 18 or 15, a unit. Fix the \(a\) embedding at this place. Because the leading coefficient of \(K_0\) is a unit, both an actual candidate \(b\) and a guard-zero root of \(K_0\) are integral. Existence of the guard-zero root follows from its exact zero resultant and nonzero leading coefficient of \(K_0\) (the product-of-evaluations identity for the resultant). Both \(b\) values reduce to the same simple root, so Hensel uniqueness makes them **equal in characteristic zero**. Thus the literal live rotated right or original left first slope would vanish. This is not an inference that an exact guard vanishes merely because its residue vanishes.

## Degree-102 exit

For degree 102 use the simple place \((19,17,16)\) with \(K_0\) of full \(b\)-degree and the whole joint residue gcd of \(K_0,F_0,F_1\) linear. The original left fit has the needed units. Transfer its true calibrated profile to the right half-clock and use the independent **actual rotated outer contact** \([L_9,R_{10}]=0\); do not divide by the lost right affine slope. As in the [right moment proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-RIGHT-MOMENT-EXIT.md), this gives \((k_0,k_1)=(18,6)\) and \(t=16\bmod 19\). The true three calibrated right singleton hits would require zero monic hull remainder of \(Q-PY^2(b-Y)/b\), but it reduces to \(13Y^2+11Y+11\). The existing [right moment scalar source](erk11-neighbor-right-slope-draft/ERK11NeighborKRightMomentArithmetic.lean) contains this arithmetic; no new Lean diagnostic is made here.

The standalone deterministic python-flint 0.9.0 replay has no external data and completed in 7.821 seconds wall time under contention. Both affine masks are now excluded on \(K_0=0\); the fully pivotable width conditions still need a separate proof.
