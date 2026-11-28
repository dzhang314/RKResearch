# A scalar-to-literal sufficient chart for the fixed q split host

This packet completes a **conditional construction**
within the rational fifteen-stage fixed-contact \(q\)-host
architecture. It is not a rational order-ten tableau:
the rational scalar spectrum is still required.
It uses the previously earned
[late rational chart](../erk10-fifteen-split-host-late-chart/README.md)
and
[strict raw realization](../erk10-fifteen-split-host-raw-realization/README.md).
The actual order through ten, rather than just
short words, follows if the explicit gates below hold.
The distinct free-contact \(p\)-host is not asserted
covered by this sufficiency result.

## Exact nonlinear filter independent of the physical c split

Work now in actual reverse ordinates \(y=1-x\),
with physical rows \(0,a,b,c,c,d,e,f,g,h,R\)
and external origin at \(y=1\). Use the raw scalar
score/cofactor spectrum and the quartic interpolation
\[
             n(y)=\frac{(1-y)V_c(y)}{(1-R)V_c(R)}
\]
from the terminal packet. Let \(Q\) denote the
possible quadratic in
\(\boldsymbol w\odot\boldsymbol\eta
=Q(\boldsymbol y)\odot\boldsymbol u\).
It is nonzero and divisible by \(y-R\).
Its remaining affine factor is uniquely determined
by matching \(w_z n(z)=Q(z)u_z\) at two of the
three ordinary singletons \(f,g,h\) with \(u_z\ne0\),
followed by checking the third. There are at least
two such sites because the aggregate numerator \(A\)
is nonzero and affine. The additional guard is
\(A(1)Q(1)=0\), not \(Q(1)=0\) when \(A(1)=0\).

At each other singleton with nonzero weight,
\(\eta_z=Q(z)u_z/w_z\); set \(\eta_R=1\) and
\(\eta_0=0\). At a zero-score ordinary singleton
other than \(R\), the exact guard is \(Q(z)u_z=0\).
The rational cofactor argument already excludes a
zero-score ordinary singleton with \(u_z=0\).
Thus \(z\) must be the extra root of \(Q\), of
which there is at most one. If it is among
\(f,g,h\), use the actual prescribed \(n(z)\);
otherwise treat \(\eta_z\) as one linear unknown.

The entire \(\boldsymbol u\)-part of the true
grade-five silence is then equivalent to three
split-independent equations followed by one pair
sum:
\[
 \begin{split}
    &\sum_{z\ne c} (z-c)z^j\eta_z u_z=0
                                           \quad(0\le j\le2),\\
    &\Lambda_c:=\sum_{i:y_i=c}\eta_i u_i
                               =-\sum_{z\ne c}\eta_z u_z .
 \end{split}
\]
The zero-score singleton unknown, if present,
can be solved from the first equation using
\((z-c)u_z\ne0\), with the two remaining
equations still checked. These formulae are
just the four true \(\boldsymbol\eta\)-pairings
with \(\boldsymbol u{\cal P}_3\), after eliminating
the \(c\)-pair.

Write \(W_c,U_c\) for the pooled weight and
grade-two defect, \(L_c\) for the paid ratio at
the first physical \(c\), and \(t\ne0\) for its
chosen \(u\). The paired data are
\[
 (w_{c,1},u_{c,1})=(L_ct,t),\qquad
 (w_{c,2},u_{c,2})=(W_c-L_ct,U_c-t).
\]
Guard \(W_c\ne L_cU_c\) (physical pair independence).
If \(Q(c)\ne0\), both physical weights must be
nonzero and \(L_c\ne0\). The exact pair equation is
\[
 \frac{\Lambda_c}{Q(c)}
    =\frac{t}{L_c}+\frac{(U_c-t)^2}{W_c-L_ct}
    =\frac{U_c^2+t(W_c/L_c-2U_c)}{W_c-L_ct}.
\]
The linear-fractional determinant
\((W_c-L_cU_c)^2/L_c\) is nonzero. Solve for \(t\)
rationally and check its two excluded poles.
If the coefficient of \(t\) in the cleared linear
equation is zero, its constant cannot also vanish
by that determinant, so no finite \(t\) exists.

When \(Q(c)=0\), on every scored pair coordinate
the dirt must be zero. If \(L_c=0\), the first
coordinate has zero score and nonzero \(t\),
and independence implies \(W_c\ne0\); choose
\(\eta_{c,1}=\Lambda_c/t\), \(\eta_{c,2}=0\).
If \(L_c\ne0\) and \(\Lambda_c=0\), choose a
nonzero \(t\) avoiding the second-score zero
and put both dirt values zero. If \(L_c\ne0\),
\(\Lambda_c\ne0\), the second score must be zero,
forcing \(t=W_c/L_c\ne0\); independence gives
\(U_c-t\ne0\), so put
\(\eta_{c,2}=\Lambda_c/(U_c-t)\) and
\(\eta_{c,1}=0\). This exhausts the physical pair
possibilities, including all signed and zero masses.

Finally the nominal five-letter marks of the
constructed \(\boldsymbol\eta\) vanish if
\(A(1)Q(1)=0\): use the exact ordinary cofactor
on \(A(y)Q(y)/(1-y)\), of degree at most two,
times each power \(0,\ldots,5\).
There are no endpoint or high-zero contributions
in this chart. Thus the filter explicitly earns
\[
 \boldsymbol\eta\perp
  \bigl(\boldsymbol w{\cal P}_5+
        \boldsymbol u{\cal P}_3\bigr),\qquad
 \boldsymbol w\odot\boldsymbol\eta
                 =Q(\boldsymbol y)\odot\boldsymbol u\in D_4 .
\]
The first annihilator is the actual grade-five
word space of the reconstructed raw block,
by its previously established dimension and action.

## Recover the fixed old opening and all physical high taps

Switch to forward clocks \(x\). Set \(r=1-R\),
\(v=1-h\), \(z=1-g\), the first three physical
raw clocks; they are distinct and nonzero.
The required cubic is
\(P=X(X-r)(X-t_0)\), where \(t_0\) is fixed by
\[
                         J_vP=\eta_h J_rP .
\]
Writing \(a(v)=v^3(3v-4r)/12\) and
\(b(v)=v^2(3r-2v)/6\), this is
\[
   (b(v)-\eta_h r^3/6)t_0=-a(v)-\eta_h r^4/12 .
\]
A zero coefficient cannot give a solution:
then the negative of its right side is
\(v^2(v-r)^2/4\ne0\). So the guard is simply that
the coefficient is nonzero. The resulting \(J_rP\)
is nonzero: otherwise \(t_0=r/2\), whose
\(J_vP=v^2(v-r)^2/4\) is nonzero.

Set
\[
                    s=(2r-t_0)/3,\quad
                    p=rs/t_0,\quad q=r .
\]
Check the regular opening guards
(\(t_0\ne0,\ s,p,r\ne0\) pairwise distinct,
\(P(s)\ne0\)); they are exact rational checks.
Then \(q=3ps/(2p-s)\) and \(t_0=2q-3s\).
Take any nonzero old \(e_o\), independent of
the reverse tail index \(e\). The literal fixed
opening and decoder \(\Pi\) are precisely the
[regular five-row formulas](../erk10-five-opening-nonsplit-kernel/README.md);
the \(q\)-tap to \(e_o\) is zero.

Put \(F_2=X(X-2r/3)\), with \(F_2(r)\ne0,\ J_rF_2=0\).
We require the following physical forward laws:
\[
 T(F_2)=0,\qquad T(P)=-J_rP\,\boldsymbol\eta,
                              \quad T(f)=BEf-EJf .
\]
Only three actual taps still need to be chosen.
At \(v\) set \(B_{v,r}=J_vF_2/F_2(r)\).
At \(z\) choose \(B_{z,v}\) to satisfy
\[
           B_{z,v}P(v)=J_zP-J_rP\,\eta_g .
\]
If \(P(v)=0\), require its right side zero
and leave that particular tap free; this branch
must not be divided away. Then set
\(B_{z,r}=[J_zF_2-B_{z,v}F_2(v)]/F_2(r)\).
These three individual prescribed entries are
exactly the free \(h,R\) reverse taps in the raw
linear construction: choose the coefficients at
\(g\) in the \(h\) row and at \(g,h\) in the
\(R\) row, then solve on the independent preceding
eight rows. Thus no extra nonlinear matrix solve
is hidden here.

The two residual laws hold everywhere, not just
in the first three physical forward rows. Each
side lies in the annihilator of the actual
fourth observer space by the raw word tests and
true five-letter silence. The restriction of
this annihilator to \(R,h,g\) is injective:
the complementary first eight *reverse* rows
already give an invertible restriction of the
eight fourth observers. The first three raw
row checks therefore prove both laws globally.

## Actual decoder after reclassification

Let \(\chi=\Pi\boldsymbol e_q\), a quadratic
with \(\chi(r)=1\). The fixed-\(q\) opening
conditions make it \(F_2/F_2(r)\).
Indeed its three readouts are \(E_0\chi=0\),
\((E_p-\alpha E_s)\chi=0\), and \(E_r\chi=1\);
the exact fixed-\(q\) quadratic has those values.
Let \(\Pi_{\rm ret}\) mean the old decoder
applied to the retained \(0,e_o,s,p\) vector
with its \(q\)-entry set to zero.
Every polynomial in its range has value zero
at \(r\).

For each original high row build the literal
old-contact block \((E_hJ-B_hE_h)\Pi\).
Its coefficient of the old \(q\) column equals
the already prescribed raw \(B_{i,r}\), because
\(T(\chi)=0\) and \(\chi(r)=1\).
On the other four old columns this is exactly
\((EJ-BE)\Pi_{\rm ret}\) after reclassification,
since \(\Pi_{\rm ret}\) evaluates to zero at \(r\).
The same identity holds at the physical \(q\)
row itself. Both its old row and \(J_r\Pi_{\rm ret}\)
kill the old \(e_o\) axis and the pure vector
\(\boldsymbol V\) at \(s,p\) (the fixed contact
condition \((A_o\boldsymbol V)_q=0\)).
They agree on the retained model columns \(1,X\):
the physical row has the clock sum \(r\)
and first moment \(r^2/2\), and replacing
the old \(q\) entry of either column by zero
subtracts only a multiple of \(\chi\) whose
\(J_r\)-value is zero. These two models are
independent in the quotient, since
\[
           p-\alpha s=p(p-s)(2p-s)/s^2\ne0 .
\]
This accounts for all retained vectors, not
only those of low rooted order. Consequently
the entire reclassified high block has literal
old contact
\[
                              L=(EJ-BE)\Pi_{\rm ret}.
\]

## Full rooted order through ten

Use unnormalized elementary weights: a tree
with children \(t_i\) has profile
\(\boldsymbol\Phi_t=\prod_i A\boldsymbol\Phi_{t_i}\)
componentwise, and scalar nominal polynomial
\(f_t=\prod_i J f_{t_i}\), with both leaf values
one. Then \(f_t\) is a scalar multiple of
\(X^{|t|-1}\). Its output order condition is
\(b^T\boldsymbol\Phi_t=I(f_t)\).
The old origin contributes correctly for the
leaf and zero for all other trees.

Write \(\boldsymbol D_t=\boldsymbol\Phi_t^{\rm raw}
-Ef_t\) and \(q_t=\Pi_{\rm ret}\boldsymbol\Phi_t^{\rm ret}-f_t\).
The actual unary edge error is exactly
\[
       \boldsymbol e_t=A\boldsymbol\Phi_t|_{\rm raw}
                         -EJ f_t
                       =B\boldsymbol D_t-T(q_t).
\]
For \(|t|\le3\), the old decoder identity makes
\(q_t\) a multiple of \(\chi\); causal induction
gives zero errors. For \(|t|=4\), the old
\(q\) row remains pure (the host is a root of
\(P\) and of the old lower error directions).
The old decoder gives its model modulo \(P\),
so \(q_t\) is a combination of \(P,\chi\).
Its unary error is therefore a scalar multiple
of \(\boldsymbol\eta\), and all actual stage
errors through size five are in that line.
For \(|t|=5\), \(q_t\) has degree at most four
and zero constant (the explicit origin is
zero on all nonleaf profiles). Its unary error
is therefore in the fourth annihilator:
\(B\boldsymbol\eta\) and \(T(q_t)\) both belong
there. For every \(m=|t|\ge5\), the same
origin argument gives \(q_t(0)=0\) and
\(\deg q_t\le m-1\).

Expand a tree error by multiplying each real
edge as its nominal polynomial plus
\(\boldsymbol e_t\).
A linear error propagates up its path by
unary \(B\) and marks by monomials from other
nominal children, their degrees equal to
their vertex counts. A size-five source
\(\boldsymbol\eta\) uses at most five outer
letters through order ten, so is killed.
A source \(T(q_t)\) from a child of size
\(m\ge5\) uses at most \(9-m\) outer letters.
Its two terms \(BE q_t\) and \(EJq_t\)
compare by the raw word budget: their
total degrees are at most nine, and
their word lengths at most five.
This kills all linearly propagated errors.

There are exactly two kinds of nonlinear error
product through order ten. Two defective child
edges can only have child sizes \(4+4\) or \(4+5\).
In \(4+4\) the error is a multiple of
\(\boldsymbol\eta^{\odot2}\); there can be at
most one additional mark or unary through
order ten. Its output, marked output, and unary
output vanish respectively from
\[
 \boldsymbol w\odot\boldsymbol\eta\in D_4,\quad
 \boldsymbol\eta,C\boldsymbol\eta\perp D_4,\quad
 B^T\boldsymbol w=(I-C)\boldsymbol w .
\]
In \(4+5\) the product is a multiple of
\(\boldsymbol\eta\) times a member of the
fourth annihilator, with no additional letter.
Its output vanishes by
\(\boldsymbol w\odot\boldsymbol\eta\in D_4\).
Three defective edges already exceed order ten.
Thus every actual rooted condition through ten
holds. A candidate would still need an independent
literal all-tree check, and a next-order defect
if asserting *exactly* ten. No such candidate
is asserted by these conditional arguments.

## Replays and status

    python3 -B audit.py | diff -u exact-audit.txt -
    python3 -B spectrum.py --grid | diff -u finite-grid.txt -

A specific rational input can be checked with
the options \(\texttt{--c --d --g --R}\);
the default tries the \(A(1)=0\) first-pair
reconstruction. Passing explicit
\(\texttt{--a --b}\) instead tests the affine
\(A(1)\ne0\) score spectrum. On a successful
input, \(\texttt{--literal}\) reconstructs the
literal fixed-\(q\) tableau, runs a separate
1,205-tree exact verifier, and checks on
through order eleven for a next-order defect.
The included seven-row fixture instead checks
all 17 low-order rooted profiles and the
actual size-five host line, not order ten.

The [separate origin-root note](ORIGIN-SUBCASES.md)
contains an exact one-parameter exclusion, a
uniform \(c=2\) 7-adic pressure constraint,
and the scope of the bounded rational sample.
No candidate survived that sample, and the
generic rational stage bound is unchanged.

The [common symmetric head solve](HEAD-SYMMETRY.md)
reduces both affine-cofactor cases to one two-row
linear system. The [nonlinear reciprocal filter](RECIPROCAL.md)
excludes eight listed tail triples for arbitrary
rational remaining clocks. Its
[modulo-29 refinement](RESIDUE-29.md) excludes a
whole outer-clock residue class without any
integrality restriction on the four inner clocks.
These are exact fixed-architecture obstructions,
not another height-bounded sample.
