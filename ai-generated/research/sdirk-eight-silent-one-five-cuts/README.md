# Two scoped cuts in five distinct ordinary sites with one invisible stage

At the strict SDIRK8 ten-stage floor over a characteristic-zero field, suppose stage one is the only nonzero quadratic residual, is individually weight zero, and \(B\boldsymbol h=0\). Assume five active stages with five distinct ordinary sites, the last undetected branch left by the [Gaussian low-active work](../sdirk-eight-silent-one-four-gauss/README.md). The two literal nonzero-\(h\) front stages \(2,3\) at clocks \(a,b\) are silent, and there are two additional silent zero stages. The present packet excludes the following cases:

1. Both extra silent zero stages have \(h=0\), regardless of their clocks or of the activity of physical stage eight.
2. The actual reverse quadratic factor \(k=1+2u-u^2\) vanishes, and physical stage eight is active, regardless of the two extra silent defects.

The remaining five-distinct cases have at least one nonzero extra silent \(h\), and either \(k\ne0\) or a silent eighth stage. No change to the unrestricted **10–11** interval.

Let \(x=c_{10}=1-\gamma\), \(u=(x-c_9)/\gamma\), and \(\boldsymbol w=\boldsymbol b^{\mathsf T}M\). Use the actual terminal identities \(\boldsymbol w(C-xI)=-k\boldsymbol w(A-\gamma I)\), \(w_{10}=-\gamma^2b_{10}\ne0\), \(w_9=-\gamma^2b_9k\). The invisible contribution \(w_1=0\). The \(F_4\) active restriction is the \(L_4\) line, nonzero because the five active clocks are distinct and \(L_4\) has degree four. Its kernel on the nine zero coordinates has basis \(\boldsymbol h,C\boldsymbol h\). Thus any actual pure-four column \(v\) satisfies
\[
 v_i=\rho_v L_4(c_i)+Q_v(c_i)h_i
\]
on all those coordinates for affine \(Q_v\), including silent rows. If both literal rows four and five are active, the fixed front Hankel already excludes five ordinary sites. Hence at least one extra silent zero is physically four or five.

## Both extra silent defects zero

All actual post-front rows \(4,\ldots,10\) now have \(h=0\) and the same degree-four pure line. The first two physical clock values come from the exact \((3,3,4)\) finite front regardless of their weights; they differ from each other, from \(a,b\), and from \(x\). The literal third physical clock, when distinct from the first two, lies in the same guarded quadratic as the earlier undetected chart. If that third clock repeated the first two, the four scalar reads (including \(\tau_4\) fixed by the common line) would give identical actual strict taps to the padded earlier stage, so a literal duplicate. In this comparison only a physical tap into stage one must be removed, and is zero at a zero-\(h\) row.

The paid \(\boldsymbol w\boldsymbol h\) moments show \(w_a=w_b=0\), so \(\boldsymbol w\) is supported on these seven physical post-front stages. If their clocks are distinct, the scalar reverse numerator is nonzero constant (six zero moments). Ordinary precision with both silent sites retained at zero weights still gives the ordinary nodal weight identity at these seven clocks. Therefore the earlier [reciprocal tail unit](../sdirk-eight-silent-one-row/README.md) applies for an active eighth, and the [silent eighth weight-zero unit](../sdirk-eight-silent-one-six/README.md) applies for a silent eighth. The masked nodal polynomial \(P_6(m_0 X-m_1)\) does not divide by \(m_0\). If physical seven is also silent, \(m_0=m_1=0\) and both required polynomials still vanish, contradicting the same unit. The argument does not classify any silent output as active.

If the seven physical clocks have a repeat, their at most six aggregate \(\boldsymbol w\) weights are all zero by the scalar moment probes. The active terminal is singleton among active sites, so at least one extra silent stage is at \(x\). The two actual early clocks cannot be \(x\), so exactly one extra silent stage is early and another later at \(x\). Denote the early silent clock by \(c_{\rm sil}\) and the early active clock by \(c_{\rm act}\).

* If \(k\ne0\), penultimate \(w_9\ne0\) needs the other silent occupant at \(c_9\), so \(c_{\rm sil}=c_9\). If physical eight is active, \(u=(x-c_{\rm sil})/\gamma\) fixes it in the literal star or arithmetic shape, and the four ordinary pegs \(x,c_9,c_8,c_{\rm act}\) leave just one ordinary site. The rank-one Hankel minor of its first three masked moments is a unit. If physical eight is silent, it is at \(x\) and the two actual weighted taps give \(u=2\). The requisite \(c_{\rm sil}=x-2\gamma\) is excluded in all front fields.
* If \(k=0\) and physical eight is active, the two fixed reflected tail clocks give the same four pegs and the same rank-one unit. If physical eight is silent, its clock is \(x\); physical row six is active and its finite third-clock value is available. The four pegs \(x,c_9,c_6,c_{\rm act}\) again give a rank-one unit.

These are fixed \((3,3,4)\) or \((3,3,4,2)\) monic fiber checks, with all phases and actual early placements tested at \(1103,t=161\). [Replay](zero_extra.py).

## Zero reverse factor with active eighth

Here \(\boldsymbol w\) is physically supported at \(x\), with \(w_{10}\ne0\). All three literal tail rows are active, with fixed \(c_9,c_8\) from the \(k=0\) reverse phases. The three pegs \(x,c_9,c_8\) in the five-site ordinary quadrature give exactly the [five-site diagonal projection](../sdirk-eight-silent-one-six/README.md): monic degrees \(9\) or \(1,8\) in the fixed star/arithmetic phases, after removing only \(\gamma=0\), zero signed two-by-two pivot and repeated factors. Its signed two-by-two pivot reconstructs the two other ordinary sites; the projection did not require a repeated active clock.

If physical row four is active, its \(H_4(c_4/\gamma)=0\) gate is impossible at these ordinary clocks (the nonterminal tail clocks are already occupied). If row four is silent and row five active, the same two literal first-active pure-four cubics from the earlier projection exclude it. Therefore both extra silent zero rows are physically four and five.

There must be an extra silent stage at \(x\): otherwise the terminal \(w_{10}\ne0\) would have to cancel with just one front stage at \(x\), and its nonzero \(h\) would contradict \(\boldsymbol w\boldsymbol h=0\). There are three placements:

* Only row four of the extra silent rows is at \(x\). It cannot coincide with a front clock (literal duplicate), so \(w_4=-w_{10}\) and \(h_4=0\). The \(H_4(x/\gamma)\) gate is a unit.
* Only row five of the extra silent rows is at \(x\). A front clock may also equal \(x\). The signed silent aggregate there is nonzero and its \(w h\) aggregate is zero. The actual row-five \(Ah,\tau_4\) at this fixed clock are affine in its \(h\): prescribe the strict stage-one feed by \(h\), then solve the three scalar strict reads at \(a,b,c_4\). Any coincident front stage is the padded earlier value of this exact same affine formula. Thus the normalized signed mixture is the actual formula at \(h=0\), with the pure-four \(L_4\) line by the global affine profile above. The earlier two literal first-active cubics apply to this virtual read at \(x\), since their only requirements are that same formula and the pure-four line; it need not carry positive or nonzero ordinary weight. They have unit gcd with \(y=x/\gamma\).
* Both physical four and five are at \(x\). Row four is not at an earlier front clock; remove only the exact diagonal factors violating this condition. Row five's pure-four profile there is again affine in its actual \(h\). The literal padded row-four read is the value at \(h=h_4\). Its derivative rank minor with the first three zero rows is nonzero in every reduced field, so rank three forces \(h_5=h_4\), producing a literal duplicate by the unique three scalar tap solve. [Replay](zero_reverse_active8.py).

## Replay

Run `python3 check_five_cuts.py` with `sympy==1.14.0` and `python-flint==0.9.0` using the earlier sibling folders. The exact masked, signed and copied-clock checks in fixed monic characteristic-zero fibers lift their units at \(1103\) or \(1129\); the hypothetical tableau itself is not assumed to reduce. The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8SilentFiveVirtualRead.lean) verifies the division-free signed silent affine read over commutative rings and compiled on Lean/Mathlib 4.36.0 with standard axioms. The physical census and exact finite arithmetic are source-level proofs.
