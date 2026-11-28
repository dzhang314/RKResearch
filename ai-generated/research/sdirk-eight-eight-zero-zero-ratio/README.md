# Zero reflected ratio is impossible with eight physical quadratic zeros

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\). Let \(\mathbf c=A\mathbf1,\ \mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), and suppose exactly eight physical entries of \(\mathbf g\) are zero.

**Result.** The literal reflected second defect ratio cannot be zero. By the [low-label count restriction](../sdirk-eight-eight-zero-low-labels/README.md), the two off rows are silent physical rows 1 and 2 at distinct clocks. In this branch the eight zero rows would have exactly seven distinct labels, with one doubled terminal site. The complete check below treats every placement of that duplicate. The nonzero reflected ratio chart remains open.

## 1. Two chronological rear gates on distinct-label aggregates

Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma,\ I_D(T^j)=D^j/(j+1)\). Write \(s=x_{10}=D-1,\ t=x_9=s-v,\ r=x_8=s-w\), where \(v^2-2v-1=0\) and \(w=2v\) or \(2-v\). The last three rows are live zeros at distinct clocks. The zero-ratio pure row \(\mathbf z^\mathsf T=-\mathbf b^\mathsf T(CA-AC-A^2)/2\) is supported precisely on the two copies of \(s\), with opposite entries. Its companion \(\boldsymbol\eta^\mathsf T=\mathbf z^\mathsf T(A'-I)\) annihilates powers through degree four. On seven distinct labels its cardinal numerators are affine in the clock, and \(Z_3=\langle\mathbf z^\mathsf T,\boldsymbol\eta^\mathsf T\rangle\). Use \(C=\operatorname{diag}(\mathbf c)\).

Let \(a,b,c,e,f\) be the five early zero labels in forward order (physical rows 3 through 7). They are pairwise distinct and one of them is \(s\). The remaining rear labels \(r,t\) are singletons. Use \(P_7\) monic on the seven distinct labels and \(B(T)=I_{D,X}((P_7(X)-P_7(T))/(X-T))\), so \(B\) is always formed with ordinary **aggregates**, not with one arbitrary representative weight.

For the fourth reverse gate take \(R=(T-r)(T-t)\). From the weighted grade-two row with profile \(R\), subtract a multiple of \(\mathbf z^\mathsf T\) to kill the physical terminal input. On the earlier \(s\) occurrence this moves the entire terminal-weight part of the \(R(s)\) input into that row. Thus at the fourth reverse zero \(f\), the actual right read is diagonal: at a singleton it is \(b_fR(f)\), and if \(f=s\) it is the full \(s\)-aggregate times \(R(s)\). The terminal read is zero; in the repeated case aggregate the pure discrepancy over both copies. Since the other pure direction has affine cardinal numerators, the errors at \(t,r,f\), after multiplication by their nodal derivatives, lie on a common affine line. With \(J_D^*R=JR(D)-JR(T)\) and
\[
 2vp_R=2wv+1+2w-w^2,\qquad p_R J_D^*R(t)=vJ_D^*R(r),
\]
as in the [earlier rank-two rear primitive check](../sdirk-eight-seven-zero-two-clock-active/README.md), the cleared fourth condition is
\[
 v(r-t)[R(f)-J_D^*R(f)]B(f)+J_D^*R(t)
 \bigl[v(r-t)B(t)+(f-t)(p_RB(r)-vB(t))\bigr]=0.               \tag{1}
\]
This uses no nonzero hypothesis on \(b_f\) or the total at the terminal clock.

For the fifth reverse gate take \(\sigma=(T-f)(T-r)(T-t)\), also subtracting a pure multiple to kill the actual terminal input. Now the right read is zero at \(t,r,f\) and diagonal at \(e\), interpreted in aggregate if \(e\) or \(f\) is the earlier \(s\). Pair the \(Z_4\) pure error with the actual supported \(E_3\) cubic \(\rho=(T-a)(T-b)(T-c)\), available by the two-profile basis proved in the low-label packet. It kills the first three labels, including both copies of \(s\) if that is among the first three. At the other four labels \(P_7'(x)=\rho(x)\sigma_4'(x)\) for \(\sigma_4=(T-e)\sigma\). Ordinary Lagrange interpolation gives
\[
 B(e)-[T^3]\bigl(B(T)J_D^*\sigma(T)\bmod \sigma_4(T)\bigr)=0. \tag{2}
\]
The corrected terminal read and the early duplicate are combined only when their shared label contributes to this pairing.

## 2. First three possible duplicate placements

The [exact front gates](../sdirk-eight-eight-zero-low-labels/README.md#1-literal-placements-and-exact-profile-gates) fix \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0\), \(C_3(c;D)=0\). Their exact base \(K=\mathbb Q(u,b,v)\) has degree twelve with recovered primitive \(\theta=u+b+2v\).

If \(s=a\) or \(s=b\), then \(D=1+a\) or \(1+b\) and the third-clock equation is a quadratic at that \(D\). If \(s=c\), the condition \(C_3(D-1;D)=0\) is irreducible of degree six in \(D\) over \(K\). For these placements the five pegs \(a,b,c,r,t\) are distinct, while \(e,f\) are initially unknown. Let \(P_5=(T-a)(T-b)(T-c)(T-r)(T-t)\) and \(m_i=I_D(T^iP_5)\). The ordinary nodal relation is
\[
 (f m_0-m_1)e=f m_1-m_2.
\]
Clearing \(k(f)=f m_0-m_1\) in \(P_7\) multiplies \(B(f)\) to the constant \(m_0m_2-m_1^2\). The selected exact fibers show this constant nonzero, so \(k(f)=0\) cannot be an ordinary solution. The cleared (1) is a polynomial in \(f\) of degree at most three. It vanishes at the two forbidden collisions \(r,t\) by the primitive identity and the same constant-numerator calculation. After the two factors are removed it is linear with a unit leading coefficient in every checked fiber. The recovered \(f,e\) then fail (2).

For \(s=a,b\), both roots of the quadratic for \(c\) are checked through simple reductions; for \(s=c\) the irreducible diagonal sextic has one simple residue root in the chosen base embedding, giving an embedding of its whole exact field.

| Rear | Earlier \(s\) | \(p\) | \(\theta\bmod p\) | \(D\bmod p\) | Residues of (2) |
|---|---|---:|---:|---:|---|
| Star | \(a\) | 79 | 10 | 31 | 58,16 |
| Star | \(b\) | 79 | 10 | 52 | 33,29 |
| Arithmetic | \(a\) | 31 | 8 | 12 | 18,10 |
| Arithmetic | \(b\) | 31 | 9 | 18 | 2,6 |
| Star | \(c\) | 17 | 3 | 2 | 13 |
| Arithmetic | \(c\) | 17 | 8 | 15 | 5 |

No other algebraic candidate is inferred absent merely from its not being prime-field rational.

## 3. Latest two placements: exact lower-degree projections

Now \(s\notin\{a,b,c\}\) and \(\{e,f\}=\{s,y\}\) for one unknown label \(y\). Keep \(P_5,m_i\) as above and set \(k=s m_0-m_1,\ \ell=s m_1-m_2\). Ordinary precision gives \(ky=\ell\). The norm in the third-zero quadratic \(C_3(T;D)=A_2 T^2+A_1 T+A_0\) is computed by using the monic \(\widehat c=A_2 c\), followed by scaling its evaluation by the necessary power of \(A_2\). For a genuine clock and \(A_2\ne0\), zero before scaling implies zero norm. Only exact factors supported on \(A_2\) are stripped; its zeros will be checked separately.

The exact guarded projection of \(k=0\) has degree 16 in \(D\). Its reduction is coprime to the cleared norm of \(\ell=0\) at the selected primes. Therefore a singular actual ordinary equation would be impossible. For \(k\ne0\), write \(P_7^\#=P_5(T-s)(kT-\ell)\), with cardinal \(B^\#=kB\). At the unknown node \(y=\ell/k\),
\[
 B^\#(y)=kI_D(P_5(T-s))=-k^2.
\]
This permits the following small fourth projections without multiplying every node by the ordinary pivot.

* At \(f=s\), use (1) with \(B^\#\) directly, giving an exact guarded \(D\)-projection of degree 32.
* At \(f=y\), clear \(k\) in (1), using \(B^\#(y)=-k^2\) and the degree-at-most-three polynomial \(R-J_D^*R\). Its guarded projection has degree 54.

For the modular fifth projections, initially scale **only** by \(A_2\) to represent \(\widehat c\). Build \(k,\ell,P_7^\#,B^\#\) in that scaled clock coordinate. The quartic in (2) is represented by \((T-r)(T-t)(T-s)(kT-\ell)\), with leading \(k\), where the known clocks now mean their scaled values. Seven fixed pseudo-remainder steps represent its degree-three coefficient multiplied by \(k^7\). If \(f=y\), use \(\sigma^\#=(T-r)(T-t)(kT-\ell)\) and multiply the entire fifth equation by \(k\); if \(f=s\), use the ordinary cubic. The scaled primitive also requires the diagonal factor \(A_2\) on the left. The replay implements exactly these polynomial equations and takes their norm in the monic \(\widehat c\) algebra.

For the star cell \(p=79,\theta=10\); for arithmetic \(p=31,\theta=8\). Degrees 16, 32 and 54 of the exact guarded polynomials are preserved, and the three gcds with the calculated modular second ordinary/fifth reverse norms are constant. In particular, the fifth norms have degrees 550 and 610 in these reductions. A possible characteristic-zero \(D\) is integral at the chosen embedding since it is a root of one of the exact guarded leading-unit polynomials. Reduction of the other necessary norm then contradicts the checked gcd. No assumption that the ordinary pivot is a unit at all reductions is used to strip its roots.

Finally \(A_2(D)\) is an irreducible quartic over \(K\), coprime to \(A_1(D)\). Its simple good reduction at \(p=31,\theta=20,D=20\) gives \(c=7\) from the surviving linear equation, in both phases. The ordinary last-label pivot is a unit there. The actual two node placements give nonzero rear pairs \((27,6),(2,6)\) for star and \((24,7),(18,28)\) for arithmetic, in the order \((\text{fourth},\text{fifth})\). This checks the exceptional quadratic leading drop separately, rather than treating it as a forbidden actual value.

## 4. Replay

Run `python check_zero_ratio.py zero-star` and `python check_zero_ratio.py zero-arith` with SymPy 1.14 and python-flint 0.8. The script computes the small exact projections and all fixed residue receipts from scratch. The native `RKCert.Research.SDIRKEightEightZeroZeroRatio` gives the cleared affine identity and the ordinary extra-cardinal sign calculation. Fraction-free projections and the rooted-tableau ingress are source-level. The full branch exclusion is characteristic zero, not an asserted exclusion in every paid positive characteristic.
