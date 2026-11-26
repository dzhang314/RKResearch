# A true unmarked head fills the double-factor band

The one-stage early extension supplies the full space of actual double-factor inputs. This is a statement about genuine earlier-zero rooted combinations and true late stage data, not about full order or an improved upper bound.

## 1. Whole actual double-factor band

The earlier bank is the actual canonical minimum Laguerre cache through tree size \(m-1\), with zero output weights, prescribed common real-algebraic \(\gamma<0\), last actual clock \(\alpha<0\), and exact linear decoder \(D_F\) through \(m-1\). The symbol \(K_m\) denotes the actual first-excess model image of early-numerically zero trees through size \(m\). Put
\[
 J\coloneqq I_0-\gamma I,\qquad
 D(X)\coloneqq (X-\alpha)(X-a),\qquad
 K_m^0\coloneqq\ker(E_\alpha J|_{K_m}).
\]
Here \(I_0\) is the primitive from zero and \(E_x\) is evaluation at the clock \(x\). The genuine added sampler, at a negative real-algebraic \(a\ne\alpha\), uses \(E_a J D_F\) as its strict row. Use a polynomial \(q_a\) satisfying the literal conditions
\[
 q_a\in K_m^0,\qquad q_a(a)=1,\qquad (Jq_a)(a)=0.
\]
The repaired decoder is \(D'(\mathbf e,z_a)=D_F\mathbf e+q_a(z_a-E_aD_F\mathbf e)\). Thus its otherwise unchanged pure polynomials and residuals obey the two anchor identities of [the early sampler](EARLY.md). All late rows have the direct strict feed \(EJD'-TED'\) from the repaired early data, and strict lower matrix \(T\) within the late bank. Write \(E\) for evaluation at those literal clocks.

If \(m\ge5\) is odd, the true marked-head proof in [the early sampler](EARLY.md) gives the entire double-factor space at size \(m+1\). If \(m\ge6\) is even, there is a choice of the actual canonical early clocks and the above sampler such that the same is true:
\[
 \{\text{genuine earlier-null heads with formal profile }F
                    \text{ and actual late data } EF\}
 \quad\hbox{attain}\quad D\,\mathbb P_{\le n-3}
                    \qquad(n\ge m+1).                         \tag{1}
\]
The assertion means that every polynomial in the displayed space has a realizing linear combination of genuine trees of size at most \(n\); it makes no claim that arbitrary earlier-null tree combinations have pure late data. One can choose \(a\) outside a finite set of negative algebraic exceptions after the canonical clock choice.

To see what must be supplied in the even case, the existing first-excess basis gives
\[
 K_m\oplus X K_m=(X-\alpha)\mathbb P_{\le m-1}.
\]
Thus every \(F\in K_m^0\) has unique polynomials \(P_F,Q_F\in K_m\) with \(JF=P_F+XQ_F\). At \(a\), the condition \(JF(a)=0\) implies \(P_F(a)=-aQ_F(a)\). The one-mark heads span
\[
 K'_m+XK'_m,\qquad K'_m\coloneqq K_m\cap\ker E_a,
\]
a codimension-one subspace of \(D\mathbb P_{\le m-2}\). So the exact extra test on the repaired decoder is \(Q_{q_a}(a)\ne0\). It then puts \(Jq_a\) outside this marked subspace.

Crucially \(Jq_a\) itself is a genuine pure late head, not just a permissible polynomial. Choose an old-early-null shifted tree combination through size \(m\) with formal model \(q_a\). Its repaired early numerical data are zero except for the value \(1\) at the appended sampler. Its late numerical data are \(Eq_a\) by actual local correctness through \(m\). The shifted unary extension is zero on all repaired early stages, since their shifted matrix is strictly lower triangular and the only possible nonzero child coordinate was last. Its literal late data are
\[
 (EJD'-TED')(\mathbf e,z_a)+T E q_a=EJq_a,
\]
because \(D'(\mathbf e,z_a)=q_a\). Its true model is \(Jq_a\). This supplies the missing dimension at size \(m+1\), and actual root marks supply every larger space in (1).

## 2. Choosing the clocks for the missing unary direction

Here are exact clock choices ensuring the required nondegeneracy for every even \(m\ge6\). No fixed-degree parameter has to be evaluated. Let \(h\coloneqq m-1\), which is odd and at least five. Use normalised clock \(Z=X/\gamma\), \(J_1=I_0-I\), and monic ordinary Laguerre polynomials \(W_l(Z)=l!J_1^l1\). A real normalised root \(\lambda\) of \(W_h\) gives \(\alpha=\gamma\lambda\). Set
\[
 r_l\coloneqq W_l(\lambda)/W_{h-1}(\lambda),\qquad
 U_l\coloneqq W_l-r_l W_{h-1},\qquad
 \xi\coloneqq (h\lambda-1)/(h-1).
\]
The denominators are nonzero by interlacing. The actual two last copy impulses in the canonical bank are \(U_{h-2}\) and
\[
 U_{h-4}+A U_{h-3}+B U_{h-2},
 \qquad A(h-3)^2=4h-8-(u+v),                                \tag{2}
\]
where \(u,v\) are the two distinct actual level-\((h-1)\) roots selected from \(W_{h-1}\). Indeed the penultimate impulse starts at index \(h-4\), leaves that coefficient one, and fits its two actual zeros with coefficients at \(h-3,h-2\). On roots of \(W_{h-1}\), divide by \(W_{h-2}\) and apply the three-term recurrence. The result has leading coefficient \(1/[(h-3)^2(h-2)^2]\) and is proportional to \((Z-u)(Z-v)\), giving (2). The last copy keeps these coefficients and chooses the coefficient at \(h-1\) to vanish at \(\lambda\).

For testing a primitive at the two points, define
\[
 \Delta_l(Z)\coloneqq J_1U_l(Z)-
   \frac{(J_1U_l)(\lambda)}{W_{h+1}(\lambda)}W_{h+1}(Z).
\]
The subtraction is the primitive of subtracting a multiple of the true tall mode \(W_h\); hence the adjusted source is in the kernel of primitive evaluation at \(\lambda\). The Laguerre recurrence gives
\[
 \begin{aligned}
 \Delta_{h-2}(Z)&=\frac{(Z-\xi) W_h(Z)}{h^2(h-1)},\\
 \Delta_{h-3}(\xi)&=
    \frac{\xi-\lambda}{(h-2)(h-1)^2}W_{h-1}(\xi)
  + \frac{h(h-1)-(\lambda-h)^2}{h(h-2)^2(h-1)^3}W_h(\xi).
 \end{aligned}                                               \tag{3}
\]
For example \(r_{h-2}=(\lambda-2h+1)/(h-1)^2\), and
\(r_{h-3}=((\lambda-2h+3)r_{h-2}-1)/(h-2)^2\). Substitute these in
\(J_1U_l=W_{l+1}/(l+1)-r_l W_h/h\), use
\(W_{h+1}(\lambda)=-h^2W_{h-1}(\lambda)\), and express the remaining \(W_{h-2},W_{h+1}\) in terms of \(W_{h-1},W_h\). The equality \(\xi-2h-1=h(\lambda-2h+1)/(h-1)\) gives (3).

One can always choose \(\lambda\) so that the second expression in (3) is nonzero. Take an odd prime \(q\mid h\), choose an embedding of the algebraic splitting field into an algebraic closure of \(\mathbb Q_q\), and let \(v_q(q)=1\). The nonleading coefficients of \(W_h\) are \((-1)^i i!\binom hi^2\), all divisible by \(q\): if \(i\ge q\) use the factorial, and if \(0<i<q\) use the factor \(h\) in \(\binom hi\). Thus all roots have positive valuation. The average root valuation is \(v_q(h!)/h<1/(q-1)\le1/2\), by the factorial valuation formula. Choose a root with \(0<v_q(\lambda)<1/2\), taking it in the real embedding for the clock. All ordinary Laguerre roots are positive real, so this is an allowed canonical clock. Now \(\xi\equiv1\) in the residue field and \(W_h(\xi)\) is a unit. The first term of (3) is integral, while the second has valuation \(2v_q(\lambda)-v_q(h)<0\), since \(h-1,h-2\) are units and the numerator has valuation \(2v_q(\lambda)\). Thus they cannot cancel. This argument only chooses a root from the full set; it does not require irreducibility or any statement about a specified extremal root.

Use (2) to choose \(u,v\) so that
\[
       \Delta_{h-4}(\xi)+A\Delta_{h-3}(\xi)\ne0 .
\]
There are at least two possible sums \(u+v\), and only one possible forbidden value because \(\Delta_{h-3}(\xi)\ne0\). The \(B\) coefficient does not affect this test by (3). The adjusted last and penultimate compressed sources therefore give two elements \(F_1,F_2\in K_m^0\) (after rescaling) with \(JF_1\) a nonzero multiple of \((Z-\xi)W_h\) in the normalised coordinate and \(JF_2(\xi)\ne0\) in that coordinate. The first has \(Q_{F_1}\) a nonzero multiple of \(W_h\) by uniqueness in \(K_m\oplus X K_m\). Consequently
\[
 (JF_1)Q_{F_2}-(JF_2)Q_{F_1}\not\equiv0:
\]
after factoring the nonzero polynomial \(W_h\), the remaining bracket does not vanish at \(\xi\).

It follows that \(E_aJ\) and \(F\mapsto Q_F(a)\) are independent on \(K_m^0\) for generic real-algebraic \(a<0\). Likewise \(E_aJ\) and \(E_a\) are independent: for any independent \(F,G\in K_m^0\), the polynomial \(F JG-G JF=F I_0G-G I_0F\) cannot vanish identically, since it is the numerator of the derivative of the nonconstant rational function \(I_0F/I_0G\), up to sign. The space \(K_m^0\) has dimension \(m/2-1\ge2\). In the kernel of \(E_aJ\) avoid the two proper linear subspaces \(E_aF=0\) and \(Q_F(a)=0\), then normalise \(E_aF\) to one. This gives the required \(q_a\) and completes (1).
