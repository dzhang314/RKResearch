# Dense derivative rank with a singular triangular commutator

**Scope.** Let \(p\ge1\) be the largest tree vertex count tested, so the corresponding exact formal stage polynomials have degree at most \(p-1\). We use no ordinary unit-time order assumption. Full dense derivative accuracy means that an actual polynomial row \(L(x)\) satisfies, as polynomial identities,
\[
              L(x)\boldsymbol\Phi_t(A)=q_t(x)
              =(|t|/t!)x^{|t|-1}\qquad(|t|\le p).
\]
The quotient \(|t|/t!\) denotes the reciprocal product of the child factorials; only \((p-1)!\) is needed. In the denominator-cleared formulation the tall tree of size \(p\) forces \((p-1)!\) to be a unit by equality of the highest coefficient. Thus the field results apply in characteristic zero or characteristic at least \(p\), including characteristic \(p\) when it is prime. For example in characteristic two, strict \(A_{21}=1\) with two stages and row \((1-x,x)\) gives dense derivative accuracy through size two; ordinary order two is impossible there. No integration of the highest dense row coefficient is used below.

## 1. Exact rank and kernel charge

Let \(A\) be lower triangular on \(s\) stages, \(C=\operatorname{diag}(A\mathbf1)\), and
\[
             D=CA-AC-A^2,\qquad \kappa=\dim\ker D .
\]
Write \(E_j\) for the actual span of stage tree columns through grade \(j\) (tree size at most \(j+1\)), \(e_j=\dim E_j\). Write \(Z_j\) for the actual image of zero-formal-polynomial combinations through that grade. These definitions do not assume that the formal model is well-defined on the numerical stage span. Under full dense accuracy it is well-defined there, with kernel \(Z_j\). The actual pure clock powers \(1,\mathbf c,\ldots,\mathbf c^{\odot j}\) map to the independent monomials, so
\[
           E_j=\operatorname{span}(1,\mathbf c,\ldots,\mathbf c^{\odot j})
                         \ \oplus\ Z_j,\qquad e_j=j+1+\dim Z_j .
\tag{1}
\]
In particular at least \(p\) distinct clock labels are needed for a full dense polynomial decoder.

Unary lift by \(A\) acts formally as \(J=\int_0^x\), and \(C\) acts as multiplication \(X\) (append a leaf at the root). The identity \(XJ-JX=J^2\), checked on a monomial, shows \(D E_{j-2}\subset Z_j\) for \(2\le j\le p-1\). The largest antiderivative denominator in this use is \(j\le p-1\). Consequently
\[
 e_j\ \ge\ j+1+e_{j-2}-\dim(E_{j-2}\cap\ker D).
\tag{2}
\]
Unrolling any \(a\le\lfloor(p-1)/2\rfloor\) steps gives the measured lower bound
\[
 s\ \ge\ (a+1)(p-a)
           -\sum_{h=1}^a\dim(E_{p-1-2h}\cap\ker D).
\tag{3}
\]
This allows a late-arriving kernel direction to be charged only at the grades where it is actually present. Using only \(\kappa\) and optimizing the truncation gives
\[
 \boxed{\displaystyle s\ge p+
         \left\lfloor\frac{\max(0,p-1-\kappa)^2}{4}\right\rfloor .}
\tag{4}
\]
Indeed \((a+1)(p-a)-a\kappa=p+a(p-1-\kappa-a)\); its nearest-integer maximum lies in the allowed range, or \(a=0\) if the linear coefficient is nonpositive. This interpolates between the invertible bound \(\lfloor(p+1)^2/4\rfloor\) and the basic \(p\)-dimensional dense readout. At corank one it is exactly \(1+\lfloor p^2/4\rfloor\).

One purely joint finite packet making the loss explicit is \(T_j\) spanned by the actual columns \(D^h C^k\mathbf1\), \(2h+k\le j\). Under (1) its recursion is the exact direct sum \(T_j=\operatorname{span}(C^k\mathbf1:0\le k\le j)\oplus D T_{j-2}\); hence its dimension is the nonsingular parity sum minus the successive *actual* kernel intersections with \(T_{j-2}\). This is an equality for that joint packet, not an equality for the whole tree span. Additional formal-zero columns, such as mixed words in \(A,C,D\), can increase the measured rank, but separate rank counts for different words cannot simply be added. If desired decompose the charge into pure-defect and model-visible parts:
\[
 \dim(E_j\cap\ker D)
 =\dim(Z_j\cap\ker D)
  +\operatorname{rank}\big(L|_{E_j\cap\ker D}\big).
\]
Here \(L\) denotes the joint coefficient readout.

## 2. Diagonal positions, actual corank, and some strict ERK comparisons

The diagonal of \(D\) is \(-a_{ii}^2\). Let \(N\) be the set of nonzero physical diagonal sites of \(A\), and \(Z\) its zero sites, \(z=|Z|\). Then \(D_{NN}\) is invertible and
\[
 \kappa=z-\operatorname{rank}\bigl(D_{ZZ}-D_{ZN}D_{NN}^{-1}D_{NZ}\bigr).
\tag{5}
\]
The matrix in parentheses is strictly lower triangular on the inherited order of \(Z\). Indeed an intermediate nonzero-pivot contribution uses indices \(i>k\ge l>j\), since the inverse of the nonzero principal block is lower triangular in its own order. In particular the corank is at most \(z\), but may be much smaller. A nonzero first subdiagonal in that Schur block gives a pivot for every such link: use the row after the link and the column before it; the resulting minor is lower triangular because the original diagonal is zero. Thus its corank is bounded by the number of components remaining after splitting the zero-index line at absent first-subdiagonal links. For physically consecutive zero-diagonal stages the Schur correction does not enter that pair, and the link is \(A_{i+1,i}(c_{i+1}-c_i)\).

Moreover \(\ker D\) injects into the zero-site coordinate space, again by invertibility of \(D_{NN}\). If the actual zero-site restriction of \(E_{p-1}\) has rank \(r_0\), then \(e_{p-1}\le s-z+r_0\), while each kernel charge in (3) is at most \(\min(\kappa,r_0)\). Thus the joint physical count includes
\[
 s\ \ge\ z-r_0+p+
        \left\lfloor
          \frac{\max(0,p-1-\min(\kappa,r_0))^2}{4}
        \right\rfloor .
\tag{6}
\]
For example a prefix of several pure origin sites carries only one zero-site profile direction if all zero-diagonal sites are in that prefix. The extra origins are therefore not independent kernel charges. In the one-origin, all-other-diagonal-nonzero chart \(\kappa=1\) exactly, so (4) gives \(1+\lfloor p^2/4\rfloor\); no assumption of equal nonzero diagonals is required for this lower bound.

In strictly explicit ERK, \(D\) is strict, but if every actual first-subdiagonal product \(A_{i+1,i}(c_{i+1}-c_i)\) is nonzero, \(\ker D=K e_s\) on the last physical coordinate. For \(p\ge3\), this direction is in neither \(E_0\) nor \(E_1\): the first two clock values are \(0,c_2\) with \(c_2\ne0\), so neither constant nor affine clock data can vanish on both while producing \(e_s\). Keeping the corresponding zero charge at the end of the parity sum in (3) gives
\[
                         s\ge \lfloor p^2/4\rfloor+2 .
\tag{7}
\]
This is conditional on the actual links. Without those links, a simple general ERK comparison is \(s\ge p+1\) for \(p\ge3\): at the first nonzero clock \(c_i\), strictness makes \((A\mathbf c)_i=0\), so \(A\mathbf c-\mathbf c^{\odot2}/2\) is a nonzero grade-two defect. Combine it with (1). No global first-subdiagonal hypothesis follows from dense accuracy alone.

The field bound with \(\kappa\le z\) also specializes over a nonzero commutative ring when the product of the specified nonzero diagonals is not nilpotent (in particular if they are units), keeping the specified zero diagonals. Choose a prime avoiding that product and pass to its quotient fraction field, preserving the dense identities. Do not count merely nonzero nilpotent entries as diagonals that survive this specialization.

## 3. Incomplete exact sampling versus a permitted error subspace

Here is a general actual rank bridge, valid without full dense accuracy. At grade \(j\) let \(L_j:K^s\to Y_j\) be any joint measurement map, and \(P_j=D E_{j-2}\subset E_j\) (zero for \(j<2\)). The induced map \(E_j/P_j\to Y_j/L_j(P_j)\) gives the literal inequality
\[
 e_j\ge \dim P_j+
           \operatorname{rank}L_j|_{E_j}
          -\operatorname{rank}L_j|_{P_j}.
\tag{8}
\]
This applies also when only a selected subset of tree witnesses has been verified: in that case the two measurement ranks are the actual ranks, not extrapolated accuracies. In particular do not place a formal-zero lift in a measurement kernel just because some of its terms were separately sampled.

**Exact incomplete samples.** Suppose \(L_j\) agrees on every mathematical witness of grade \(\le j\) with a specified model reading \(Q_j(q_t)\), where \(Q_j:K[x]_{\le j}\to Y_j\) may read only selected polynomial coefficients or values. Then \(L_j(P_j)=0\) and \(\operatorname{rank}L_j(E_j)=\operatorname{rank}Q_j\), because the formal bush features span the model polynomials. With \(r_j=\operatorname{rank}Q_j\), (8) becomes
\[
 e_j\ge r_j+e_{j-2}-\dim(E_{j-2}\cap\ker D),\qquad e_j\ge r_j .
\tag{9}
\]
For instance \(k\) distinct time samples of all paid trees give \(r_j=\min(k,j+1)\), not the full polynomial rank \(j+1\). Different grade readings are allowed, provided their through-grade agreements or literal ranks are established. Iterating at the target \(p-1\) gives
\[
 e_{p-1}\ge
 \max_{0\le a\le\lfloor(p-1)/2\rfloor}
  \left(\sum_{h=0}^{a}r_{p-1-2h}
              -\sum_{h=1}^{a}\dim(E_{p-1-2h}\cap\ker D)\right).
\tag{10}
\]
With only the uniform charge \(\kappa\) and the fixed \(k\)-sample rank sequence, this reads
\(\min(k,p)+\sum_{h=1}^{\lfloor(p-1)/2\rfloor}
(\min(k,p-2h)-\kappa)_+\).
This is a lower formula for incomplete observation, not a claim of full polynomial accuracy.

**Allowed errors at paid grades.** Instead suppose \(L_j\) agrees with \(Q_j(q_t)\) modulo a specified subspace \(H_j\subset Y_j\) for all through-grade witnesses. The exact readout after quotienting by \(H_j\) has rank
\[
       r_j=\dim\operatorname{im}Q_j
                      -\dim(\operatorname{im}Q_j\cap H_j),
\tag{11}
\]
and annihilates \(P_j\) there, so (9)–(10) hold with this rank. The loss is the measured intersection, not the full dimension of the allowed error space. More tightly, one can take \(H_j\) to be the actual joint image of the error witnesses if it is known. Concatenate all selected reads before taking these ranks; independently counting marginal ranks or independently charging overlapping error directions is invalid. This does not require \(H_j\) to be an ideal or invariant under polynomial operations.

A related measured reverse check for a full dense row, if useful, is the actual joint rank of covectors \(L W-\widehat W L\), where \(W\) is a physical context operator and \(\widehat W\) its formal action truncated at degree \(p-1\). For context cost \(a\), these rows annihilate \(E_j\) when \(j+a\le p-1\), by literal context expansion. Thus their actual joint rank plus \(e_j\) is a stage lower bound; no independence of these rows is automatic for singular \(A\) or for incomplete readout. The truncation does not permit charging an untested operation on the highest coefficient.

## 4. What is sharp

The uniform interpolation (4) is best possible from the *abstract filtered-rank axioms* alone. For \(0\le\kappa\le p\), use one model generator \(v_k\) of grade \(k\) mapping to \(x^k\), \(0\le k<p\). Kill the first \(\kappa\) of them by \(D\). For each remaining \(v_k\), add a chain with one new zero-model vector for each available grade \(k+2,k+4,\ldots\), and let \(D\) advance to the next vector. Close each of these chains invertibly on its last vector, at a grade where a further step is outside the paid horizon. For example use the companion closure for a polynomial \((X+1)^{\text{chain length}}\), so the whole abstract \(D\) can even be triangularized with nonzero diagonal \(-1\) on these chains. Its kernel is exactly the first \(\kappa\) model directions; the dimension is \(p+\sum_{k\ge\kappa}\lfloor(p-1-k)/2\rfloor\), namely (4). If \(\kappa>p\), the separate fact \(s\ge\kappa\) is unavoidable. This construction does **not** realize a physical \(A,C\) or their commutator, so it does not prove sharpness in any RK subclass.

In particular the corank-one formula is a general lower bound, to be combined with an independently proved actual upper construction only under its precise field, diagonal, and tree-order hypotheses. The strict ERK refinement and the sampler/error conditions above may have additional structural losses or gains. No general RK attainability is asserted here.
