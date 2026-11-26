# Fourth-length contacts on the arithmetic tail need exactly one new hidden row

The arithmetic tail admits a word space of dimension nine through length four. The two new primitive tests require just one new independent residual row. The result does not attain the target order.

## 1. The first two actual new primitive reads

Keep the notation \(r=2n+1,\ m=r+1,\ p=m+r,\ d=(n+1)^2\), the true scalar row \(b\), the two earlier negative anchors \(\alpha,a\), and \(D(X)=(X-\alpha)(X-a)\). The literal reverse clock, strict matrix, and hidden row in units of the common diagonal are
\[
 M_0\coloneqq M/\gamma,\qquad T_0\coloneqq T/\gamma,\qquad
 h_0\coloneqq h/\gamma^2 .
\]
The formal normalized primitive is \(L_1=I_0^\beta-I\), where \(\beta=(1-X)/\gamma\). Write \(f_i=L_1(\beta^i)\). On the proved six-row arithmetic chart the actual inputs through length three span
\[
             b\mathbb P_{\le3}(M_0)+h_0\mathbb P_{\le1}(M_0).
\]
All primitive images are already known except
\[
             q_3\coloneqq (bM_0^3)T_0,\qquad
             z_4\coloneqq (h_0M_0)T_0 .                      \tag{1}
\]
They have formal models \(f_3\) and zero, respectively. This is an exact finite reduction: marks of earlier paid words are paid at the next narrower degree, and the four old tap equations cover the other four basis inputs.

In particular \(z_4 E F=0\) is a genuine new fourth-length rooted test on \(F\in D\mathbb P_{\le p-7}\). Indeed \(h_0=b\Omega_0\), where
\(\Omega_0=(T_0+I)M_0-M_0(T_0+I)-(T_0+I)^2\) has zero formal primitive model. For an actual earlier-null source head with late data \(EF\), its shifted primitive and then its reflected mark give the actual column \(M_0 T_0 EF\), in normalized units. Applying the linear combination of at most two further root operations represented by \(\Omega_0\) gives the genuine rooted order contraction \(b\Omega_0 M_0 T_0 EF\). All source profiles in the stated band come from the actual double-factor heads, not virtual samples. Similarly the strict primitive followed by three marks gives the condition \(q_3 EF=\int_0^1 f_3((1-X)/\gamma)F(X)\,dX\). These moment requirements do not follow just from the smaller four tap equations.

## 2. The new hidden read is independent; the other read can share it

The first four normalized reverse sites of the arithmetic tail are \(1,u,2u-1,\beta_3\), with \(u,\beta_3\to0\) and \(\beta_3\ne u\) at finite \(g=-\gamma\). Their measured values are \(H_i=(h_0)_i/b_i\). Put
\[
  k_i\coloneqq (q_3)_i/b_i-f_3(\beta_i),\qquad
  Z_i\coloneqq (z_4)_i/b_i .
\]
These data are fixed by the strictly earlier taps on the first four sites. In the \(u=0\) limit the first three sites are \(1,0,-1\), their \(H\)'s are \(-1,2,17\), and the first two nonempty tap rows are \((-1)\) and \((-7,5)\). Therefore
\[
 (k_i,H_i,Z_i)_{i=0,1,2}
  = (3/4,-1,0),\quad(-1,2,1),\quad(-33/4,17,7).
\]
For the variable fourth site the literal taps on those first three evaluate \(\beta^3\) just as \(\beta\), and evaluate \(H\beta\) just as \(-9\beta^2+8\beta\). With \(H=H_3(\beta)=N(\beta)/A(\beta)\) from the old fourth pivot, this gives
\[
 k(\beta)=f_1(\beta)-f_3(\beta)-H_3(\beta)/2,\qquad
 Z(\beta)=8f_1(\beta)-9f_2(\beta)+
                   (3\beta/2+1/2)H_3(\beta).
\]
Here \(H_3(0)=2,H_3'(0)=-10\). The derivatives of \(k/H_3,Z/H_3\) at zero are \(-1/2,-5/2\). The quadratic interpolants of their first-three ratios have derivatives \(-9/68,-7/34\) there. Thus their interpolation residual derivatives are
\[
                  -25/68,\qquad -39/17 .
\]
At finite \(u,\beta_3\) divide their fourth residuals by \(\beta_3-u\). The data depend analytically on the clocks near their stated limits, and the varying fourth-site solved response takes precisely the second-site value at \(\beta=u\); hence the divided residuals tend to the displayed derivatives. In particular \(H,H\beta,H\beta^2,Z\) are independent on the first four genuine sites, and \(z_4\) cannot be absorbed into the already available hidden row times a quadratic.

Consequently there is a unique literal four-slot fit
\[
             k_i=H_i P_2(\beta_i)+\lambda Z_i\quad(i=0,\ldots,3),
             \qquad \deg P_2\le2 .
\]
Its precise limits are
\[
       \lambda\longrightarrow25/156,\qquad
       P_2(\beta)\longrightarrow(-22\beta^2-31\beta-181)/312 . \tag{2}
\]
The ratio of residual derivatives gives \(\lambda\), and the remaining polynomial interpolates the three first residual ratios \(k_i/H_i-\lambda Z_i/H_i\). Impose this relation globally by prescribing the actual primitive response of one composite input:
\[
       \varphi\coloneqq bM_0^3-\lambda h_0M_0,\qquad
       \varphi T_0=b f_3(M_0)+h_0P_2(M_0).                   \tag{3}
\]
Together with a separately paid \(z_4\), this retains exactly one new numerical hidden direction and pays (1).

## 3. A new physical fifth pivot, then the sixth

Normalize \(\varphi\) by the nonzero weight at each site, so its function is
\(\phi(\beta,H)=\beta^3-\lambda\beta H\).
On the first four sites interpolate this actual input as \(A_2(\beta)+c H\) with \(\deg A_2\le2\). Its normalized limiting coefficients are
\[
             A_2=-1/13+(5/78)\beta+(63/52)\beta^2,\qquad c=1/26 .
\]
For detail the first-three polynomial for \(\phi\) is
\(9\lambda\beta^2+(1-8\lambda)\beta\), using the interpolant of \(H\beta\) above. Its derivative discrepancy from \(\phi(\beta,H_3(\beta))\) is \(6\lambda-1\); divide by the \(H_3\) derivative discrepancy \(-1\), giving \(c=1-6\lambda\). Subtract \(c(6\beta^2-9\beta+2)\) to obtain \(A_2\).

For a proposed new clock, its four old taps produce the composite response from this interpolant. The desired equality (3) is the single equation
\[
 D_4(\beta)H=N_4(\beta),\qquad
 \begin{cases}
 D_4=-(A_2)_1/2-(A_2)_2 K+c(\beta-1)/\kappa-P_2,\\
 N_4=f_3-L_1 A_2 .
 \end{cases}                                                 \tag{4}
\]
This follows by substituting the four literal moments (2) of FORCED-ARITHMETIC.md. The limiting polynomials, from (2), are
\[
 D_4=(11\beta^2-19\beta-6)/156,\qquad
 N_4=(39\beta^4-219\beta^3+184\beta^2+22\beta-12)/156 .
\]
Thus \(D_4\ne0\) on all sufficiently small interior \(\beta\) at large finite \(g\). With \(H_4=N_4/D_4\), the difference of the new actual input from its old interpolation is
\[
 \phi(\beta,H_4)-A_2-cH_4
   =\bigl((\beta^3-A_2)D_4-(\lambda\beta+c)N_4\bigr)/D_4 .
\]
Its numerator has degree at most five, limiting leading coefficient \(19/624\ne0\), and four old zeros because the old physical responses meet (3). Consequently at most one additional clock is forbidden by its numerator. Choose a distinct interior fifth site avoiding it, from the exact scalar grid, and take \(H=H_4\) there. Its four literal taps meet (3) and its actual input increases the pivot rank from four to five.

At the sixth site add \(h_0M_0\) as an independent input. The six candidate evaluation functions are \(1,\beta,\beta^2,H,\phi,\beta H\), which are polynomially independent as functions of \((\beta,H)\). After the first five independent sites a single nonzero annihilator is \(F(\beta)+H G(\beta)\) with \(\deg F\le3,\deg G\le1\). The polynomial \(G\) cannot be zero, since then \(F\) would have five distinct roots. Hence at most one new distinct \(\beta\) makes this expression vanish for every \(H\). Choose any allowed unused interior site and \(H\) avoiding the one possible value there. Its five earlier taps solve the four lower equations and (3), and its actual \(z_4\) value is then fixed. The six real inputs are now a literal six-pivot set. There are enough interior clock choices for \(n\ge3\).

## 4. Weighted fill and the exact rank claim

Keep \(p'=p\) if \(n\ge4\), and take \(p'=p-1\) if \(n=3\). On the other \(d-6\) sites assign \(h_0\) to kill \(D\mathbb P_{\le p'-5}\), and \(z_4\) to kill \(D\mathbb P_{\le p'-7}\), after subtracting the fixed first six values. These are ordinary Vandermonde moment solves on distinct non-anchor clocks; the larger number \(p'-4\) of moments is at most \(d-6\). Solve all six simultaneous equations at each remaining physical column on the six true later pivot sites: the old four responses, (3), and the prescribed \(z_4\). Formula (3) then makes \(q_3\) pay its true formal model because \(h_0P_2\) and \(z_4\) both vanish on the grade-four band. The four earlier responses and marks already cover every other actual length-four word.

The resulting actual rank is exactly nine. Its upper bound follows from \(V_4=b\mathbb P_{\le4}(M_0)+h_0\mathbb P_{\le2}(M_0)+\operatorname{span}\{z_4\}\). The four displayed hidden directions are independent already on the first four physical sites. They are independent of the five formal monomial rows by the genuine positive pairing with \(D\) times a polynomial of degree at most four, which is within the paid band since \(p'\ge11\). Equivalently a full minimum continuation has room for only one such new hidden direction, and the first four literal arithmetic rows force it to be present. This count is of numerical rows of a single actual matrix, not the number of symbolic words.

Attach the true earlier feed \(EJD'-TED'\). All late clocks and local order through \(m\) are preserved, and the double-factor spine calculation gives full rooted order at least \(m+4\). For \(n=3\) this reaches order \(12\) in the order-15 geometry; for \(n=4\) it reaches order \(14\) in the order-19 geometry. No remaining fifth-length or higher contact is asserted. The main packet does not impose the high prefix word compensation; its joint construction follows in HIGH-COMPENSATION.md.
