# A first-consumption inequality from the actual weighted terminal support

Use the notation from `ANTICHAIN-AND-EXACT-GRAM.md`. Suppose the original tableau is stage-minimal through order \(p\) in its fixed diagonal class. For an unread unweighted stage \(i\) in the measured prefix \(I\), let
\[
 \sigma_i\coloneqq\min\{k\ge0:\mathbf e_i^I\in E_k|_I\},\qquad
 \beta_i\coloneqq\min\{k\ge0:\mathcal C_k|_i\ne0\},
\]
with infinity if a set is empty. Stage minimality gives \(E_H=K^s\), hence finite \(\sigma_i\). Indeed, any linear dependence of all degree-through-\(H\) derivatives could be used to delete its last pivot, preserving every retained derivative and weighted output to order \(p\). At the unread cut, \(\sigma_i-1\) is exactly the last degree on which a restoration of \(i\) by the other prefix rows is possible. This uses all the measured prefix rows, not just those preceding \(i\).

Take \(D=\{i\}\), \(h=\sigma_i-1\), \(c=\sigma_i+1\), and \(d=d_i\). If \(\sigma_i+\beta_i>H\), then all the required linear contexts miss \(i\); thus stage minimality forces
\[
                     H\ge2\sigma_i+d_i+1. \tag{3}
\]
Otherwise its first nonlinear effect is not paid, and the deletion would preserve the method's order. This is stronger than comparing the forward birth degree merely to the shortest graph distance, since it uses actual vanishing of weighted contexts. It remains valid if \(\beta_i=\infty\).

## Weighted first receivers at equality

Suppose a prescribed restoration kills \(E_h\) and reaches the first quadratic boundary \(H=2c+d-1\) under the invisibility in the companion note. Let \(\mathbf w\) and \(Y\) have the meanings there. For each \(\mathbf x\in Y\), the actual ordinary visibility gives
\[
 \mathbf w\cdot(\mathbf x\odot\mathbf f)=0\qquad(\mathbf f\in E_c). \tag{4}
\]
To see this, \(\mathbf w\odot\mathbf f\) is an ordinary context of cost at most \(d-1+c\). Its pairing with the strict response \(U\) is an additional \(A^\mathsf T\) operation minus the omitted-coordinate diagonal term; both vanish on the named omitted coordinates. Equation (4) uses neither sign assumptions nor a pure representation of \(U\).

If the original is stage-minimal and \(D\ne\varnothing\), the exact Gram cannot vanish. Choose \(\mathbf x,\mathbf y\in Y\) with \(\mathbf w\cdot(\mathbf x\odot\mathbf y)\ne0\), and put
\[
                     J\coloneqq\operatorname{supp}(\mathbf w\odot\mathbf x).
\]
This is an actual weighted first receiver set, not merely a set of graph neighbours. By (4) the nonzero row \((\mathbf w\odot\mathbf x)|_J\) annihilates \(E_c|_J\), whereas \(\mathbf y|_J\notin E_c|_J\). Thus the measured terminal history rank is strictly deficient there. In particular, if its named clocks are all distinct, then \(|J|\ge c+2\) by the Vandermonde test on the bushy powers through degree \(c\).

Let \(s_b\) be the last nonzero output index. Every actual \(j\in J\) is strictly after \(m\), and at most \(s_b-d+1\). In fact a nonzero \(w_j\) has an actual path of \(d-1\) matrix entries to a weighted row; nonzero \(x_j\) means some omitted stage has a direct strict edge to \(j\). This path must be entirely strict, even in DIRK: one diagonal step would give a shorter path from that omitted stage, contrary to the definition of \(d\). Cancellation may still remove potential rows from \(J\), which is why the actual \(\mathbf w\) appears. For distinct receiver clocks the resulting inequality is
\[
                        s_b-m\ge d+c+1. \tag{5}
\]
In particular, for one still-dependent unread row under the failure of the weighted lag bound at equality in (3), it reads \(s_b-m\ge d_i+\sigma_i+2\). This is a conditional stage interval bound at every order with this measured boundary; it does not assert a new unrestricted order table entry.

If there are \(k\le c+1\) distinct labels on \(J\), the weaker pooled consequences of (4) are already exact: every separate clock sum of \(\mathbf w\odot\mathbf x\) is zero. More generally multiplication by actual clock interpolation indicators, of degree \(k-1\), shows that the local row at each clock annihilates its actual restricted \(E_{c-k+1}\). Therefore if those local history restrictions are all full, the quadratic obstruction is impossible. Conversely an output count based on nonzero aggregate clock weights alone is insufficient to certify the Gram. For example, in the one-column case, if \(J\) consists of just two weighted responders at a common clock, their histories must coincide on \(E_c\), and their weights satisfy \(w_1u_1+w_2u_2=0\), where \(\mathbf u\) is the one strict feed. Since both coefficients are nonzero,
\[
             w_1u_1^2+w_2u_2^2=w_1u_1^2\frac{w_1+w_2}{w_2}.
\]
A same-clock two-row obstruction therefore needs a nonzero aggregate *transported* weight at those two actual responders. A larger same-clock group need not obey that two-row inference.

## After the first quadratic degree, but before three changes can arrive

The argument also gives an observable support certificate when \(2c+d-1\le H<3c+d-1\). Retain the same linear invisibility assumption \(\mathcal C_{H-c+1}|_D=0\). If preserving the old order fails, at least one two-replacement term must have a nonzero output. At the first common root of the two replacements write its two vectors as \(\mathbf v,\mathbf v'\), each obtained from a direct response \(U\rho_t\) by an ordinary sequence of \(A\) and actual tree diagonal multipliers. Write \(\ell,\ell'\) for their extra degree charges beyond \(c\), including any excess in the replaced child, and let \(a\) be the cost of the ordinary outer covector \(\mathbf z\). Then \(a+\ell+\ell'\le H-2c\). The nonzero term has the form \(\mathbf z\cdot(\mathbf v\odot\mathbf v')\).

Put \(J'=\operatorname{supp}(\mathbf z\odot\mathbf v)\). The row \((\mathbf z\odot\mathbf v)|_{J'}\) annihilates \(E_{c+\ell'}|_{J'}\): replace the second vector by a true test of that degree, move the operators of the first onto \(\mathbf z\), and test the strict response, at total context cost at most \(a+(c+\ell')+\ell+1\le H-c+1\). Meanwhile \(\mathbf v'|_{J'}\) is not in that numerical span, because it pairs nontrivially. Thus if all such named terminal support restrictions are full, deletion is safe, without a global selector degree assumption. Distinct clocks on a witnessing \(J'\) require \(|J'|\ge c+\ell'+2\). These are necessary witnesses for any failed restoration in this window, not individually sufficient beyond the exact first quadratic boundary; different terms can cancel.
