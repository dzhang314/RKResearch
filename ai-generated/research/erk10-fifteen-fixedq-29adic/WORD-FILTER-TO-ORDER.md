# Eight actual raw words imply the literal order-ten tableau

This is a **mathematical implication**, not a claim that the
whole implication or the lifted order-ten endpoint has been
kernel-checked. The separate stock-Lean GradeCore checks the
scalar polynomial and finite degree facts. The already checked
ring-polymorphic word rows include \(0,\ldots,5,8,9,10\).
The actual \(e,f\) words (indices 6,7) have exact algebraic
replays but still need the slot-specific native adapter.
The implication below uses the eight equalities in **every**
physical row; a residue-only action would not suffice.

Work over any commutative ring \(R\) with a local ring map
\(\rho:R\to\mathbb F_{29}\) and the displayed decic/head-quadratic
roots with residues \(2,11,20\). In particular all integers
\(1,\ldots,10\) and all paid pivot denominators are units.
Use the actual raw vectors \(\boldsymbol Y,\boldsymbol w,
\boldsymbol u,\boldsymbol\eta\) (eleven physical coordinates,
with both copies of \(c\)). Let \(K\) be the literal
chronological matrix, not an arbitrary matrix with the same
residue. The physical forward \(B\) is the reverse transpose
of \(K\); write everything below in the same indexing as
\(K\), so \(B=K^T\) and \(\boldsymbol x=1-\boldsymbol Y\).
Conjugating by reversal merely puts the physical array in
forward chronology. Dot products below use no inverses of
individual scores.

## 1. The two terminal words pay a unit change of generators

Let \(\mathcal P_j\) be formal polynomials of degree at most \(j\),
with \(\mathcal P_j=0\) for negative \(j\), and define
\[
 D_j=\{\boldsymbol w\,p(\boldsymbol Y)+
               \boldsymbol u\,r(\boldsymbol Y):
                     p\in\mathcal P_j,\ r\in\mathcal P_{j-2}\}.
\]
All products of vectors in the proof are pointwise except
matrix actions and dot products. Set
\(s=b/a,\ t=c/a,\ k=c/(2c-4b)\), \(d=26\).
The native `head_normalN` gives
\(N_{\rm head}(Y)=n_0+n_1Y\), where \(n_0=-4bk\),
\(n_1=-2-4k(s-t)\).
Write
\[
 M=Y^2(Y-c)^2,\quad L=M'/4,\quad
 A_G=(Y-d)L,\quad B_G=(Y-d)(2-t)(Y-c),\quad
 B_Z=-(Y-c)(n_0+n_1Y).
\]
Then the **actual** last inputs are
\(\boldsymbol G=\boldsymbol w A_G+\boldsymbol u B_G\) and
\(\boldsymbol Z=\boldsymbol w M+\boldsymbol u B_Z\), evaluated
at \(\boldsymbol Y\). In particular they lie in \(D_4\).
Their \(w\)-leading coefficients both equal 1.
Their difference is
\[
 \boldsymbol G-\boldsymbol Z
 =\boldsymbol w H_A(\boldsymbol Y)
  +\boldsymbol u H_B(\boldsymbol Y)
  +\Delta\,\boldsymbol u\boldsymbol Y^2,\qquad
 \Delta=(2-t)+n_1=2kt ,
\]
where \(\deg H_A\le3,\deg H_B\le1\).
The last equality uses \(2k(t-2s)=t\).
The actual \(\rho(k)=\rho(t)=16\) gives \(\rho(\Delta)=19\);
therefore **\(\Delta\) is a unit in \(R\)**. Recover
\(\boldsymbol u\boldsymbol Y^2\) by this paid difference,
then recover \(\boldsymbol w\boldsymbol Y^4\) from
\(\boldsymbol Z\) using \(M=Y^4-2cY^3+c^2Y^2\).
This proves that the eight actual input vectors generate \(D_4\)
over the ring. No fraction-field rank or independence
assumption beyond the checked unit leading minor is used.

## 2. The filtered images have the exact nominal primitives

Let \(J\) be the formal primitive from zero in its displayed
variable. Put \(\Lambda(Y)=Y-14Y^2+56Y^3-84Y^4+42Y^5\) and
\(\gamma=-J(M)(c)/\Lambda(c)\), with \(\rho(\Lambda(c))=17\).
The two prescribed terminal outputs give
\[
 \begin{split}
 K\boldsymbol Z&=\boldsymbol w(JM+\gamma\Lambda)
                         +\boldsymbol u Q_Z,\\
 K\boldsymbol G&=\boldsymbol w(J A_G-\gamma\Lambda/4)
                         +\boldsymbol u R_G,\qquad
 R_G=((Y-d)B_Z-Q_Z)/4 .
 \end{split}
\]
For the second equality use
\(4J A_G=(Y-d)M-JM\), since \(M(0)=0\).
The degrees of \(Q_Z,R_G\) are at most 3.
Write \(\mathcal A,\mathcal B\) for the defect polynomial maps
on the six primitive words:
\[
 K(\boldsymbol w p)=\boldsymbol w Jp+\boldsymbol u\mathcal A(p)
      \quad(p\in\mathcal P_3),\quad
 K(\boldsymbol u r)=\boldsymbol u\mathcal B(r)
      \quad(r\in\mathcal P_1).
\]
In detail \(\mathcal A(1)=0\),
\(\mathcal A(Y)=1\),
\(\mathcal A(Y^2)=a\,\mathrm{modelP}(Y/a)\),
\(\mathcal A(Y^3)=a^2\,\mathrm{modelR}(Y/a)\).
Also \(\mathcal B(1)=k(Y-a)\) and
\(\mathcal B(Y)=a^2\,\mathrm{modelQ}(Y/a)\).
The degrees are evident from the literal formulas.

Apply \(K\) to the unit difference in section 1. Since
\(J A_G-J M-J H_A=0\), it gives
\[
 K(\boldsymbol u\boldsymbol Y^2)
   =\lambda_U\,\boldsymbol w\Lambda+\boldsymbol u V_U,\quad
 \lambda_U=-5\gamma/(4\Delta),\quad
 V_U=(R_G-Q_Z-\mathcal A(H_A)-\mathcal B(H_B))/\Delta .
\]
The degree of \(V_U\) is at most 3. Applying the
\(K\boldsymbol Z\) identity then gives
\[
 K(\boldsymbol w\boldsymbol Y^4)
   =\boldsymbol w Y^5/5+\lambda_W\,\boldsymbol w\Lambda
                              +\boldsymbol u V_W,\quad
 \lambda_W=\gamma+n_1\lambda_U .
\]
Here \(V_W=Q_Z-\mathcal A(M-Y^4)
             -\mathcal B(B_Z+n_1Y^2)+n_1V_U\) also has degree at most 3.
Consequently for \(j\le4\) and any representation
\(\boldsymbol v=\boldsymbol w p+\boldsymbol u r\in D_j\)
there is a (possibly representation-dependent) \(r'\) of
degree at most \(j-1\), zero for \(j=0\), such that
\[
 K\boldsymbol v =\boldsymbol w Jp +\boldsymbol u r'
                                  +\lambda\boldsymbol w\Lambda,
 \qquad \lambda=0\ \text{if }j<4 .
\]
This proves \(K D_j\subset D_{j+1}\) for \(j\le4\).
Multiplication by \(\boldsymbol x\) or \(\boldsymbol Y\)
similarly sends \(D_j\) into \(D_{j+1}\).

## 3. A direct residual pairing, stronger than enumerating raw words

Let \(I\) be the coefficient integral on \([0,1]\), with
\(I(Y^i)=(i+1)^{-1}\) for \(i\le9\).
The existing `avg_integer_moments` and `raw_cardinal` yield
\[
 \langle\boldsymbol w,p(\boldsymbol Y)\rangle+
    w_{\rm origin}p(1)=I(p)\quad(\deg p\le9).
\]
The first theorem expresses the already used finite evaluator
with denominator \(7257600=2\cdot10!\); casting its integer
moment identities gives the displayed \(I\) through degree nine.
The proved cofactor identities give
\(\langle\boldsymbol u,p(\boldsymbol Y)\rangle=0\) for
\(\deg p\le7\).
Finally \(I(\Lambda p)=0\) for \(\deg p\le4,p(1)=0\):
write \(p=(1-Y)q\), \(\deg q\le3\), and use its four
scaled coefficient moments (the clearing integer 2520 is a
unit). Factoring a monic linear factor and evaluating at 1
is valid over commutative rings, without a field assumption.

Put \(N_j=D_j^\perp\), and let \(E\) evaluate at
the assigned forward clocks \(\boldsymbol x\). For a formal
polynomial \(q\) in \(X\), define the true error
\[
   S(q)=BEq-EJq .
\]
For \(0\le j\le4\), **if \(q(0)=0\) and
\(\deg q\le8-j\), then \(S(q)\in N_j\)**.
Indeed pair separately with
\(\boldsymbol v=\boldsymbol w p+\boldsymbol u r\in D_j\).
Use the adjoint pairing
\(\langle\boldsymbol v,BEq\rangle=\langle K\boldsymbol v,Eq\rangle\),
and write \(\widetilde q(Y)=q(1-Y)\).
The \(u\)-terms in both pairings vanish since
\((j-1)+(8-j)\le7\) and \((j-2)+(9-j)\le7\) where present.
The Jacobi term is present only for \(j=4\), for which
\(\deg \widetilde q\le4,\ \widetilde q(1)=0\).
The two remaining terms are \(I((Jp)\widetilde q)\) and
\(I(p\,\widetilde{Jq})\): both degree at most 9 and both
are zero at the external-origin reverse ordinate 1.
They are equal by exact formal integration by parts:
\(\widetilde{Jq}(Y)=\int_Y^1\widetilde q(Z)\,dZ\).
On monomials \(p=Y^i,\widetilde q=Y^\ell\) this pairing
clears to \(i+\ell+2=(i+1)+(\ell+1)\); all denominators
required by the degree cap are units. This proves the pairing
over \(R\), not just over \(\mathbb Q_{29}\).

Also \(B N_{j+1}\subset N_j\) by transposition, and
multiplication by a polynomial in \(\boldsymbol x\) of degree
at most \(d\) sends \(N_{j+d}\) into \(N_j\) whenever
\(j+d\le5\). The latter is direct from the two degree bounds
and does not require an induction on raw words.
The exact contact and mark receipts `raw_contact`,
`raw_weighted_eta`, `raw_mixed_eta_u` give
\[
 \boldsymbol w\boldsymbol\eta\in D_4,\qquad
             \boldsymbol\eta\in N_5 .
\]

## 4. Forward laws and the actual retained opening

Use the actual forward host data \(r,v,z,t_0,s_o,q_o\),
where \(t_0\) is the decoder parameter `HostInput.t` and
\(q_o\) is its retained stage `HostInput.q`. These are unrelated
to the scalar head normalizations \(s,t\) above. Put
\[
 F_2=X(X-2r/3),\quad P=X(X-r)(X-t_0),\quad
                           \chi=F_2/F_2(r).
\]
Both \(S(F_2)\) and \(S(P)\) are in \(N_4\) by section 3.
The first three forward sites \(r,v,z\) are reverse 10,9,8.
The identities `actualK_ports`, `actual_host_contact`,
`actual_forward_host_eta` pay their **actual** strict taps.
They give \(S(F_2)=0\) at those three sites (including
\(JF_2(r)=0\)). They give
\(S(P)=-JP(r)\boldsymbol\eta\) there:
at \(r\) this is immediate, at \(v\) use \(P(r)=0\)
and \(JP(v)=\eta_v JP(r)\), and at \(z\) it is the
prescribed \(v\)-tap equation.

Restriction of \(N_4\) to reverse coordinates \((8,9,10)\)
is injective. If a vector in it is zero on these sites, it
is supported on the first eight, and its dot product with
all eight generators is zero. The actual leading \(8\times8\)
matrix has unit determinant, so multiply by its inverse.
Thus these three pointwise receipts prove the global laws
\[
               S(F_2)=0,\qquad S(P)=-JP(r)\boldsymbol\eta .
\]
In particular \(S(\chi)=0\).

The actual `retainedPoly` decoder is linear: its three
guarded readouts are \(E_0,\ E_{q_o}-\alpha E_{s_o},\ E_r\),
with the last input fixed to zero. Its expansion on the
four old coordinate axes proves that the old-to-raw block
of `tableau15` acts as \((EJ-BE)\Pi_{\rm ret}\) on every
retained vector. This follows directly from its formula,
not merely a low-grade identity.

Here is the full low-grade check for the actual retained
\(0,\epsilon,s_o,q_o\) part. The row sums are its clocks.
The linear primitive has the correct value at \(s_o,q_o\);
at \(\epsilon\) its defect is \(-\epsilon^2/2\), on the
ignored \(\epsilon\)-axis. The quadratic primitive defect at
\(s_o,q_o\) is respectively
\[
 \left(\epsilon^2-\frac{2\epsilon s_o}{3}\right)
 A_{s_o,\epsilon},\qquad
 \left(\epsilon^2-\frac{2\epsilon s_o}{3}\right)
 A_{q_o,\epsilon}.
\]
At \(q_o\) subtraction gives exactly
\([3s_o q_o^2-\alpha s_o^3-2q_o^3]/6=0\);
at \(s_o\) it is one substitution.
Because \(A_{q_o,\epsilon}=\alpha A_{s_o,\epsilon}\),
the projected difference \(E_{q_o}-\alpha E_{s_o}\)
kills the two primitive defects. The size-four unary
chain has just a further multiple of that same
\(\epsilon\)-column; the other two size-four shapes are
a bush and a clock times the size-three unary profile,
correct at both \(s_o,q_o\). This pays all size-four
readouts, including both child orders of the mixed shape.

The integer geometry identities in GradeCore show
\(P(q_o)=\alpha P(s_o)\) and
\(F_2(q_o)=\alpha F_2(s_o)\) from
\(3s_o=2r-t_0,\ t_0 q_o=r s_o,\
\alpha s_o^3=q_o^2(3s_o-2q_o)\).
They also give \(P(0)=P(r)=0\) by its factors.
The unit decoder determinant and \(F_2(r)\) therefore
give \(\chi\) as the quadratic with readouts \(0,0,1\).
For a true old low-tree profile and its scalar model \(f_t\),
the difference
\(q_t=\Pi_{\rm ret}\boldsymbol\Phi_t^{\rm ret}-f_t\)
is a multiple of \(\chi\) for \(|t|\le3\) and a
combination of \(\chi,P\) for \(|t|=4\):
reduce the cubic by its leading coefficient times the
monic \(P\), then subtract \(f_t(r)\chi\).
For every nonleaf \(q_t(0)=0\) because the old origin is
strictly explicit; the decoder's degree is at most two.
In particular \(\deg q_t\le |t|-1\) when \(|t|\ge5\).

## 5. Tree.attach filtration induction, including all products

Take the unnormalized model \(f_{\rm leaf}=1\),
\(f_{\mathrm{attach}(u,v)}=(J f_u)f_v\).
Let \(\boldsymbol D_t=\boldsymbol\Phi_t^{\rm raw}-E f_t\)
be the true raw stage defect. Its associated edge error is
\[
 \boldsymbol e_t=A\boldsymbol\Phi_t|_{\rm raw}-EJf_t
                 =B\boldsymbol D_t-S(q_t).
\]
This is the actual block-linear identity of section 4.
Use strictness and the low decoder laws:
\(\boldsymbol D_t=0\) through size four, and
\(\boldsymbol D_t\in R\boldsymbol\eta\) for size five.
Indeed edge errors vanish for size at most three;
for size four they are multiples of \(\boldsymbol\eta\),
and only a size-four child with a leaf rest has such
an error at size five. This does not assume purity
of the old nonorigin stages.

**Induct directly on the binary Tree.attach recursion** to prove
\(\boldsymbol D_t\in N_{10-|t|}\) for \(5\le |t|\le10\).
The size-five line starts it. For child of size \(m\) and
rest of size \(n\), put \(\ell=10-(m+n)\).
The exact pointwise expansion is
\[
 \boldsymbol D_{\mathrm{attach}(u,v)}
  =E(J f_u)\,\boldsymbol D_v+
      (E f_v)\,\boldsymbol e_u+
      \boldsymbol e_u\boldsymbol D_v .
\]
If \(5\le m\le9\), the inductive hypothesis and
\(B N_{10-m}\subset N_{9-m}\) pay the first part
of \(\boldsymbol e_u\), and section 3 pays its other
part \(S(q_u)\) in \(N_{9-m}\). If \(m=4\) the same
grade \(N_5\) follows from the host line; if \(m\le3\)
the edge error vanishes. Therefore the linear terms
are in \(N_\ell\), using \(\deg Jf_u\le m,\deg f_v\le n-1\).
Only \(n\ge5\) needs the first multiplication, so its
upper grade stays at most 5; similarly \(m\ge4\) for
the second.

The nonlinear term can be present only for
\((m,n)=(4,5),(4,6),(5,5)\).
For \((4,5)\) it is a multiple of \(\boldsymbol\eta^2\)
which lies in \(N_1\):
\(\boldsymbol w\boldsymbol\eta\in D_4\) and
\(\boldsymbol Y\boldsymbol w\boldsymbol\eta\in D_5\),
both annihilated by \(\boldsymbol\eta\).
For \((4,6)\) use \(\boldsymbol D_v\in N_4\) and
\(\boldsymbol e_u\in R\boldsymbol\eta\); the \(w\)-pairing
is zero by \(\boldsymbol w\boldsymbol\eta\in D_4\).
For \((5,5)\) the same reason uses
\(\boldsymbol e_u\in N_4,\boldsymbol D_v\in R\boldsymbol\eta\).
These last two are exactly the required \(N_0\). This induction
accounts for all attached trees, without assuming that linear
word exactness alone implies rooted order.

For every tree through ten the output error is now zero:
\(\boldsymbol w\) is in each needed \(D_j\), and the only
nonzero old score is the explicit origin. The nominal
output is \(I(f_t)\) by scalar quadrature and reflection.
Writing \(\sigma(t)\) for the product of the child densities,
a separate recursion gives
\(\sigma(t)f_t=X^{|t|-1}\): on every child integrate the
monomial and multiply by its vertex count, a paid integer.
Thus \(t.\mathrm{density}\,I(f_t)=1\).
This is `RKCert.HasTreeOrderAtLeast` for the actual tableau;
`ReviewedOrderBridge.hasOrder_iff` transfers it to
`RKResearch.HasOrder` without field assumptions.

## 6. Exactness at eleven only needs the scalar residues

The leaf edge formula already gives
\(A\boldsymbol 1=\boldsymbol x\) on the raw sites
(\(S(\chi)=0\)) and the retained row sums on the other four.
Thus the actual order-eleven bush has denominator-cleared
defect
\[
       11\sum_{i=0}^{10}w_i(1-Y_i)^{10}-1 .
\]
The old origin contributes zero even if its weight is nonzero.
The existing `actual_Y_mod` and `actual_W_mod` give its
residue \(10\) in \(\mathbb F_{29}\), independently checked
in GradeCore. The defect is a **unit** by locality. No map
of the full 15-row coefficient matrix to a separate residue
literal, and no workflow trusting small nonzero floating
defects, is required. This distinguishes exact order ten from
mere order at least ten.

## 7. Native implementation ledger

The stock-Lean checks certify the scalar coefficient
equalities, primitive scaling, Jacobi and bush receipts,
and the finite nonlinear-case and degree budgets only.
To finish the actual native endpoint, keep these obligations
separate:

1. Complete the native \(e,f\) action and the all-row
   collector. The tail algebra uses seven degree-six
   quotient samples, the one scale identity and the two
   terminal outputs; existing exact integer/rational
   replays validate these but are not a native adapter.
2. Package sections 1–2 as linear actions on polynomial
   coefficient generators; pay \(\Delta\) with the existing
   actual head residues and use `head_normalN`. This gives
   the filter without rank/degree search.
3. Cast `avg_integer_moments` and lift the `raw_*` monomial
   moments by summing coefficients; prove the degree-bounded
   residual pairing of section 3. A scalar binomial/reflection
   or monomial integral lemma suffices.
4. Native linear decoder and low-profile projection
   receipts, and the global \(N_4\) injection via the
   existing 8-row unit minor, complete section 4.
5. The remaining native endgame is the single structural
   `Tree.attach` induction and the density recursion, then
   `ReviewedOrderBridge.hasOrder_iff`. A large replay of
   all 1,205 trees over the infinite coefficient ring is not
   needed by this proof.
6. Transport the scalar bush residue along \(\rho\) and
   use the existing `exact_nonlinear_limit` as the source
   \((c,a,b)\) in the compatible 29-adic ring.
   `project` specializes its endpoint to every \(29^n\)
   level for \(n\ge1\), and the unit defect persists under
   all maps to nonzero rings. These final wrapper theorems
   are still unverified in Lean.

No claimed new upper bound beyond the already mathematically
verified 15-stage \(29\)-adic family is made in this packet.
