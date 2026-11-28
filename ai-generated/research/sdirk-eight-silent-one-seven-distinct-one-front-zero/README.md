# One active literal front and a vanishing reverse factor

Use the [seven-distinct active profile classification](../sdirk-eight-silent-one-seven-distinct-anchors/README.md) at the ten-stage strict SDIRK8 floor over a characteristic-zero field. The sole stage with nonzero quadratic residual is the individually weight-zero first stage; there are seven active physical stages at seven different clocks, and the active cubic defect is detected. This is the case with exactly one active literal front, \(k=0\). The [both-front chart](../sdirk-eight-silent-one-seven-distinct-coprime/README.md) is separate. This packet does not address nonzero \(k\) with only one active front, or neither front active. The unrestricted **10–11** interval is unchanged.

Normalize clocks by \(\gamma\) and cubic defects by \(\gamma^3\); write \(A_0,B_0,H_a,H_b\) for the literal front data. Let \(a\) be the normalized clock of the active literal front, and \(b\) that of the silent one. Both literal defects are nonzero. With \(x=c_{10}=1-\gamma,\ c=c_9=x-\gamma u\), the actual reverse row is supported at \(x\). The terminal position there is singleton active, and at least one of the two other silent zero stages balances its nonzero \(w_{10}\). No Gauss \(h\)-hole is at an active trailing clock for zero \(k\), by the earlier [actual tail-ratio proof](../sdirk-eight-silent-one-seven-distinct-anchors/README.md).

## Tail pin and literal silent front at the terminal

The actual zero-factor ratios are \(u h_8=v h_9\) when eighth is active (\(v=B'-1-m'\) in its reflected phase) and \(h_9=2u^2h_{10}\) when eighth is silent. They use the actual weighted taps and remain true with two silent occupants at \(x\). Since the involved active tail defects are nonzero, \(L_4\) and the affine multiplier \(Q\) do not vanish there. Substitute the rational active profile and clear those two denominators. In normalized units the result is the homogeneous affine relation
\[
 s_0 Q(Y_0)+s_1 Q(Y_1)=0
\]
for two distinct actual tail clocks. Both scalar coefficients are nonzero. The actual anchored \(Q(a)=L_4(\gamma a)/h_a^{\rm act}\) is nonzero. Thus the tail relation and that anchor fix the complete affine \(Q\): the coefficient \(s_0(Y_0-a)+s_1(Y_1-a)\) cannot vanish. If it did, the two equations force \(s_0+s_1=0\), then \(s_0(Y_0-Y_1)=0\), a contradiction. The [native receipt](../../lean/RKCert/ReviewedNative/SDIRK8OneFrontZeroTailPin.lean) verifies this pivot and its homogeneous expression.

If the literal silent \(b\) is \(x/\gamma\), the diagonal is \(\gamma=1/(1+b)\) in the exact quadratic front field.

* When it is the only silent stage at \(x\), its ordinary balancing gives its actual cubic and pure-four values on the active profile. The other silent cannot be physical eight, since \(w_8\ne0\) there would force its clock \(x\). Both literal values therefore pin \(Q\). The reflected active-eighth ratio is a unit residual at every such forced diagonal.
* When both silents share \(x\), neither actual amplitude is assigned the weighted virtual read. Now fix \(Q\) by the single active literal anchor and the tail ratio just proved. In these exact field orientations it is linear coprime. In particular an affine root in this quadratic field cannot be a root of the irreducible \(L_4\) there. Physical four is active: the second silent could not be row four at the earlier literal clock \(b\), by its literal three-tap uniqueness. With active eight the four ordinary pegs give the missing cubic via the rational functional known through degree nine. It has no common root with the exact row-four equation \(Q(Y)H_4(Y)-L_4(\gamma Y)=0\). With silent eight, the literal row-four equation first supplies its own finite cubic after removing the unavoidable padded active-front factor (and only other known occupied clocks if factors occur). Add that actual row-four clock as the fourth peg and reconstruct the other three ordinary nodes. The actual row-five pure-four reads, anchored by the active literal and row four, fail at each missing singleton. No virtual read of either individual silent was used. [Replay](literal_terminal.py).

## Literal silent front is not \(x\): actual transport at the sole other silent

Only the other silent zero can balance \(x\), so its actual cubic and pure-four reads are exactly the terminal's profile. Both literal physical rows four and five are now on the profile, either as active stages or as this sole transported silent stage. Row four cannot be at either literal front. It cannot have zero \(H_4\): its literal \(Ah\) polynomial is coprime to \(H_4\), yet on the profile \(Ah\) would vanish at any zero of \(h\). This also excludes row four being an active Gauss hole.

For symbolic diagonal work use a homogeneous physical affine denominator \(q^*(X)=p_1-p_0 X\) determined by the actual tail comparison in physical variables: \(p_0=s_0+s_1\) and \(p_1=s_0c_0+s_1c_1\), where \(c_i=\gamma Y_i\). Its value at the active literal anchor is nonzero by the tail-pinning argument. Choose the polynomial numerator-denominator ratio
\[
 H(Y)=\frac{h_a^{\rm act}q^*(\gamma a)L_4(\gamma Y)}
            {L_4(\gamma a)\,q^*(\gamma Y)}
\]
at all ordinary-profile coordinates. The actual profile at a Gauss hole is zero, never this undefined ratio. The exact fourth-row equation clears these polynomials against \(H_4(s)\). Its padded root \(s=a\) is removed, yielding the cubic \(\Phi(\gamma,s)\), since physical four cannot repeat the literal active anchor.

At row five the affine pure-four slopes are fixed by the actual active literal and the actual row-four read (both prescribed nonzero defects). For \(v=Ah,\tau_4\) let \(q_v\) be the actual literal \(v/h\) ratio at \(a\), with
\[
 X_v(s)=\frac{v_4(s)-q_v H_4(s)}{s-a}
\]
the exact padded polynomial. At fifth \(y\), the actual literal read is \(v_5^0(s,y)+d_v(s)H_5\) by the three strict scalar moments after the mandatory stage-one feed. Thus it satisfies
\[
 H_4(s)v_5^0(s,y)+H_5\{H_4(s)(d_v(s)-q_v)-X_v(s)(y-a)\}=0.
\]
On an ordinary or transported fifth use \(H(y)\) above and clear its nonzero denominator; the resulting two polynomials have the exact padded \(y-a\) factor. If physical five is the active Gauss hole, its actual zero defect instead requires both literal \(v_5^0\) reads zero. The literal off-\(x\) silent front's amplitude is never substituted for a profile value. [Exact equations](off_literal_projection.py).

### Active eighth

There are four known distinct active pegs: the active literal front, terminal, penultimate and eighth. If physical four is the sole silent at \(x\), substitute \(s=x/\gamma\) into \(\Phi\), giving the guarded exact degree-ten diagonal projection. Otherwise four is a distinct ordinary active fifth peg; impose the [five-peg nodal determinant](../sdirk-eight-silent-one-seven-distinct-coprime/README.md) and eliminate \(s\) against \(\Phi\). This gives the guarded degree-55 diagonal projection. Polynomial contents removed before the determinant projection are kept as separate possible zero factors. Other removed factors correspond only to zero diagonal, vanished known active defects or their denominators, occupied active-clock coincidences, or the forbidden literal silent clock at \(x\).

Separate the exact constant-denominator and Gauss-hole factors. A coprime linear profile uses the paid rational functional through degree nine; constant \(Q\) uses the paid degree-eight and degree-nine ordinary moments. A Gauss hole is subtracted as its **known Gaussian atom**, before ordinary masked moments; it is not counted as missing ordinary mass. The four ordinary pegs then reconstruct two missing singleton nodes in the hole case, three otherwise. If row four is active retain each possible missing ordinary root for \(s\); remove that known chosen node from the polynomial for a distinct ordinary fifth. If row four is the actual silent \(x\), it contributes no ordinary peg and row five is active. With active four, row five could instead be the sole actual transported silent at \(x\); its affine equations at that clock are also checked. All sibling cases, including the actual zero-defect fifth when a hole exists, are excluded. [Replay](off_literal_active8.py).

### Silent eighth

The sole balance at \(x\) is now physically eight, so rows four and five are both active. For a non-hole fifth the two preceding literal pure-four equations, after their padded \(y-a\) factor, may be divided by \(y-s\) modulo \(\Phi=0\). Their superseded remainders are exactly \(\Phi(\gamma,s)v_5^0(s,s)\); distinct active stages forbid \(y=s\). The two resulting cubics give a resultant in \(y\). Pseudo-divide that resultant by the exact cubic \(\Phi\) in \(s\) over the quadratic field in the diagonal indeterminate. The known leading-coefficient roots are retained separately, so clearing or removing their common factors introduces no lost branch. Taking the subsequent resultant in \(s\) produces a finite guarded diagonal projection. The Gauss-hole diagonal is projected separately from the exact homogeneous equation \(L_4(p_1/p_0)=0\) with its denominator cleared; the branch also tests an actual Gauss hole at row five. A genuine lowered degree of \(\Phi\) is handled in its own exact leading locus.

There is an exact spurious stage-four locus \(H_4(s)=0,\ L_4(\gamma s)=0\), due to first clearing the pure-four reads. Its degree-twelve diagonal projection is an exact resultant. On precisely that diagonal locus use the finite exact gcd of the available \(\Phi\) and \(H_4\) polynomials to remove the prohibited \(s\)-roots. This uses the earlier actual \(Ah\) argument and never removes a root merely for vanishing in a residue field. Each remaining \(\Phi\) root supplies the actual ordinary fourth peg, added to the active literal and the two active tail clocks. Reconstruct the unknown ordinary nodes in the same rational, constant or known-Gaussian-atom functional. Test the literal fifth at each recovered ordinary clock, or with its actual zero Gauss-hole defect where relevant. [Replay](off_literal_silent8.py) and [separate exact root-removal](silent_guard.py).

## Verification

Run `python3 check_one_front_zero.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the repository's sibling proof tree. The 40 literal-terminal, 32 off-literal active-eighth, and eight off-literal silent-eighth checks retain all exact diagonal, leading and known impossible-polynomial-factor branches. Each actual required pivot and residual unit is checked in the monic quotient bases or all their residue factors. The verified residue prime is \(1103,t=161\) except where the replay explicitly selects another good reduction. No unknown tableau reduction or equality of physical silent defects is assumed. The [native scalar lemmas](../../lean/RKCert/ReviewedNative/SDIRK8OneFrontZeroTailPin.lean) check the tail pin and its homogeneous formula, compiled in Lean/Mathlib 4.36.0. The full chart and finite computations are source-level.
