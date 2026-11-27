# The all-live two-pair ERK cut: exhaustion of the point-collision case

None of the reverse chronologies in the **all-live six-opening cubic-decoder, two-pair** architecture can have order ten. This note exhausts the point-collision branch left by the [generic two-pair proof](../erk149-six-opening-two-pair-order10/README.md). The earlier [anchored contrast note](../erk149-two-pair-point-collision/README.md) proves the rooted-to-projected equations; its own exclusion covered only a specific literal chronology. No arbitrary fourteen-stage tableau, no zero-weight high row or zero-aggregate pair, and no different decoder or cross block is excluded here. The unrestricted ERK10 real-algebraic stage interval is still **14–15**.

The field has characteristic zero. The old strict prefix is the canonical six rows with clocks \(0,e,2p/3,p,q,r\) and only the old origin scored. Its physical donor labels \(0,p,q,r\) are distinct. The interpolator is the same cubic \(\Pi\) at those labels. The high block consists of eight additional **physical** rows with six distinct nonzero clocks: 1, two repeated pairs, and three singletons. Every high weight and every high aggregate weight is nonzero, with arbitrary signs. All five interior clocks are distinct from both 0 and 1, with no requirement of order or positivity. The high cross block is literally \((EJ-BE)\Pi\). The hypothesis of this note is \(\ell=E_r\) and \(r\) equal to one high interior; the off-mesh case was handled already.

## Necessary equations, with physical pooling

Keep the chronological order of the actual reversed high rows. The first reversed row is the actual endpoint at \(x=1\) by the terminal equality result, and is strict with empty input. Write \(y=1-x\). Distinct scalar sites and nonzero \(y\)'s below follow from the distinct endpoints assumption. At an individual pair row with weight \(w\), the true weighted high transpose \(L\) divides by \(w\), so the live-share assumption is essential here. True order ten gives \(L\mathbf1=\mathbf y\). Write
\[
 \mathbf u=L\mathbf y-\mathbf y^{\odot2}/2,\quad
 \mathbf g=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\quad
 \mathbf h=L\mathbf u,\quad
 \mathbf k=L\mathbf y^{\odot3}-\mathbf y^{\odot4}/4 .
\]
The anchored contrast and actual rooted tests force zero weighted aggregate of
\[
 \mathbf u,\ \mathbf g,\ \mathbf h,\ \mathbf k,\
 L(\mathbf y\odot\mathbf u),\ L\mathbf g,\ L\mathbf h
\]
at **each nonanchor interior**, with no condition imposed at the anchor. When a nonanchor pair completes, its normalized incoming row is the weight-average of its two physical rows, divided by their nonzero aggregate. This row acts on the actual previously available donor coordinates (in particular, its first occurrence may itself be a donor at the completion). A singleton is already its own normalized row. At its target \(y=t\ne0\), any such row \(P\) must satisfy
\[
  P\mathbf y=t^2/2,\quad P\mathbf y^{\odot2}=t^3/3,\quad
  P\mathbf y^{\odot3}=t^4/4,\qquad
  P\mathbf u=P(\mathbf y\odot\mathbf u)=P\mathbf g=P\mathbf h=0. \tag{1}
\]
The endpoint donor affects none of these seven reads. A group is called completed at its second row if paired, and at its only row if singleton.

A row supported on only one nonzero scalar site cannot pay the three scalar moments: \((P\mathbf y^{\odot2})^2=(P\mathbf y)(P\mathbf y^{\odot3})\) would give \(t^6/9=t^6/8\). If only two nonzero earlier scalar sites are available, their total taps are therefore both nonzero. The two reads \(P\mathbf u,P(\mathbf y\odot\mathbf u)\) separate their individual-site contributions because the sites are distinct. If at such a site there is only one physical earlier donor, its nonzero tap forces that donor's \(u=0\). In particular, the first nonendpoint physical row has \(u=-y^2/2\ne0\).

## Singleton anchor

Before the first completed **nonanchor** group, the only possible rows are the two first occurrences of the nonanchor pairs and the singleton anchor. All of these have distinct nonzero \(y\)'s. If fewer than all three have occurred yet, (1) fails by the one-/two-site argument and the nonzero defect of the first physical donor. Thus all three occur. Write their \(y\)'s in chronological order \(c,a,b\), whatever the location and identity of the anchor among them. The row at \(a\) taps the row at \(c\) by \(k\). The row at \(b\) taps the two by \(\ell_0,m\), respectively. Let the first completed nonanchor target be \(t\), and denote its three normalized taps by \((\mu_c,\mu_a,\mu_b)\). Set \(X_0=\mu_a k+\mu_b\ell_0\), \(Y_0=\mu_b m\).

Evaluate (1) on the actual chronological defects and use its scalar moments. The two reads on \(\mathbf u,\mathbf g\) give
\[
 cX_0+aY_0=t^3/6,\qquad c^2X_0+a^2Y_0=t^4/12 ,
\]
so \((a-c)aY_0=t^3(t-2c)/12\). Now \(P\mathbf h=0\) gives \(Y_0kc=t^4/24\), and \(P(\mathbf y\odot\mathbf u)=0\) yields
\[
       (a-b)\mu_a kc=t^3(3t-4b)/24 .
\]
The cardinal formula determined by the exact scalar moments at \(0,c,a,b\) is
\[
 \mu_a(t)=\frac{t^4/4-(b+c)t^3/3+bc\,t^2/2}{a(a-b)(a-c)} .
\]
The denominators are nonzero by the scope guards. The \(Y_0\) relation and \(Y_0kc=t^4/24\) imply \((t-2c)kc=(a-c)at/2\); in particular \(t=2c\), \(Y_0=0\), \(k=0\) and \(\mu_b=0\) are each impossible. Substitution in the remaining relation gives \(2c(t-b)=0\), hence \(t=b\). In particular the third chronological row cannot be the already completed singleton anchor. It must be a first pair occurrence, and the first completion is its mate.

There must next be a second completed nonanchor group. Its target \(z\) is nonzero and **distinct from \(b\)**. There are no as-yet-unused first occurrences: the only nonzero sites of scalar support are still \(c,a,b\) (with an extra physical occurrence at \(b\)). Define the individual defect column
\[
        D_x=(u_x,xu_x,g_x,h_x)^{\mathsf T}
\]
on the first three physical rows. The first completion gave a nontrivial null column combination \(\mu_c(b)D_c+\mu_a(b)D_a+\mu_b(b)D_b=0\), where \(\mu_b(b)\ne0\). Its rank is exactly two. If \(u_a\ne0\), the first two components of \(D_c,D_a\) already separate them. If \(u_a=0\), then \(h_a=-kc^2/2\ne0\) but \(h_c=0\) and \(u_c\ne0\), so they are still independent. This explicitly covers the failed first-minor pivot.

Because the actual weighted aggregate at the completed \(b\) pair vanishes, the fourth physical defect column is a scalar multiple of \(D_b\), namely \(-w_b/w_{b'}\). Its separate tap can change the effective defect coefficient at \(b\), but not the scalar totals \(\mu_c(z),\mu_a(z)\) fixed by the new target's moments. Thus the new null column combination has first two components proportional to \(\mu_c(b),\mu_a(b)\). The relevant cardinal-tap determinant is, exactly,
\[
 \mu_c(z)\mu_a(b)-\mu_a(z)\mu_c(b)
     = -\frac{b^3z^2(z-b)^2}{24ac(a-b)(a-c)(b-c)}\ne0 .
\]
Even \(\mu_c(b)=0\) causes no problem; the determinant identity and the rank-two pivot replace division by that tap. This contradiction handles all placements of a singleton anchor, including first, second, and third.

## Paired anchor

Name the two chronological anchor rows \(A,A'\) at \(y=a\); the other pair is \(B,B'\) at \(y=b\). Before the first nonanchor group completes, only \(A,A'\) and \(B\) could occur. If \(B\) has not occurred or only one distinct donor exists, one-site impossibility applies. If only one of \(A,A'\) has occurred, the original two-site argument applies with two individual donors. Therefore all three have occurred. If their actual order is \(B,A,A'\), \(u(B)=-b^2/2\ne0\); the nonzero total \(b\)-tap and the separated \(\mathbf u,\mathbf y\odot\mathbf u\) equations then contradict (1). For the two other orders those equations force \(u(B)=0\) and zero pooled \(\mathbf u\) contribution from the two \(a\) rows. Denote the normalized scalar totals at \(a,b\) by
\[
  \nu=\frac{t^2(3b-2t)}{6a(b-a)},\qquad
  \lambda=\frac{t^2(2t-3a)}{6b(b-a)} .
\]
Neither can be zero in a solution, by the one-site argument. Exact cubic payment on those same scalar sites imposes
\[
          K(t)=6ab-4(a+b)t+3t^2=0. \tag{2}
\]

* **Order \(A,A',B\).** Each anchor row reads earlier \(y\)'s only at \(0,a\), hence \(g_A=a u_A+a^3/6\) individually on both anchor rows. The \(B\) row reads those same sites and has \(u(B)=0\), so \(g(B)=b^2(3a-2b)/6\). Zero grouped \(L\mathbf g\) at \(t\) therefore requires \(\nu a^3+\lambda b^2(3a-2b)=0\), i.e. \(3ab+at-2bt=0\). Combining with (2) gives \(b=2a,\ t=b\). This eliminates the possibility of a singleton first completion, but not yet the actual \(B'\) resonance. If \(B'\) completes at that resonance, the next nonanchor group must be a singleton \(s\notin\{0,a,b\}\), still with earlier donors only at \(0,a,b\). Its required cubic defect equals
\[
         (a+b)s^3/3-ab s^2/2-s^4/4=-s^2(s-b)^2/4\ne0 .
\]
* **Order \(A,B,A'\).** The \(B\) row can read only the endpoint and \(A\). Since \(u(B)=0\), its tap at \(A\) is \(b^2/(2a)\), giving \(g(B)=b^2(3a-2b)/6\), \(h(B)=-ab^2/4\). Allow both taps of \(A'\): write \(\alpha,\beta\) for its taps on \(A,B\). If \(d\) is the normalized pooled tap on \(A'\), let \(X_0=d\alpha,Y_0=d\beta\) (no division by \(d\)). The \(\mathbf h,\mathbf u\) reads imply \(X_0=-\lambda b^2/(2a)\) and \(Y_0=t^3/(6b)\). Its residual \(P\mathbf g\) is consequently
\[
       -\nu a^3/3+a^2 X_0+b^2 Y_0
                      +\lambda b^2(3a-2b)/6
          =-t^2(-3ab+2at-bt)/18 .
\]
Thus \(-3ab+2at-bt=0\). Together with (2) this gives \(a=2b,\ t=a\), impossible because the physical anchor pair already completed and the target is nonanchor. This implication did not presume a nonzero tap to the second anchor or a nonzero defect on a pair.

For each algebraic elimination substitute \((2b-a)t=3ab\) or \((2a-b)t=3ab\) into the rescaled (2). The corresponding numerators are \(9a^2b(2a-b)\) and \(-9ab^2(a-2b)\), with all needed factors paid by distinct nonzero clocks. Equivalently multiply (2) by the square of the coefficient to avoid any division. At the resonance (2) becomes \(3(t-b)^2=0\) or \(3(t-a)^2=0\). All possible first and second completed sites have now been considered in this branch.

## Reproduction and limits

The exact SymPy replay covers the seven normalized scalar equations, elimination/resonance factors, and the nonzero second-site determinant. Native characteristic-zero identities cover the impossible one-site moment system, three-donor \(t=b\) deduction, second-site determinant, and both paired-anchor implications, checked with Lean/Mathlib 4.36.0 and standard axioms only. The physical chronology and the actual rooted-to-contrast reduction are the mathematical arguments above and in the linked proofs, not a claimed end-to-end native impossibility proof.

From ai-generated:

    python3 -B research/erk149-point-collision-exhaustive/replay.py
    sha256sum -c research/erk149-point-collision-exhaustive/sources.sha256

From ai-generated/lean:

    lake build +RKCert.ReviewedNative.ERK149AnchoredChronologyCensus
    lake env lean AuditERK149AnchoredChronologyCensus.lean
