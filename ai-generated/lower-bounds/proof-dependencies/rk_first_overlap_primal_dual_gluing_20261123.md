# A sharp primal–dual gluing theorem for triangular Runge–Kutta methods

Scope: fixed two-block projected construction, not all RK methods and not a claim of new global stage bounds. The same argument treats strictly explicit and lower triangular implicit methods. The first interface overlap needs one bilinear orthogonality condition, and the first nonlinear overlap adds a definite, exactly identifiable quadratic condition.

## Geometry of the splice

A tree has grade d=|t|−1. Its scalar derivative is f_t(x)=|t|x^d/t!; the one-node tree has scalar 1. Rooted sum multiplies derivatives, and unary extension t↦[t] takes f_t to Jf_t, where J is integration from 0 to x. The discrete operations are coordinatewise multiplication and the stage matrix.

Let a triangular prefix G start with a zero row, let u_t be its derivative vector, and take a linear map Π from prefix vectors to polynomials with Π1=1. Write ρ_t=f_t−Πu_t. Assume ρ_t=0 for d<m; for the scalar transport formulation below assume also deg ρ_t≤d and ρ_t(0)=0 at all tested grades. For example these degree bounds hold if Π has range in polynomials through m−1; evaluation at 0 agrees with the seed if (Πv)(0)=v₁.

Choose suffix nodes ξ, nonzero suffix weights w (signs unrestricted) and a lower triangular suffix-internal matrix T. Write E for evaluation at ξ, X=diag(ξ), W=diag(w). Define the full matrix and output by
    A=[G 0; K T],     K=(EJ−T E)Π,       b=(b₀,0,…,0;w).
If G,T are strictly lower, so is A. The suffix row sums are ξ. The scalar quadrature Q(f)=b₀ f(0)+wᵀ E f is assumed exact through n=p−1. Thus order p is equivalent to wᵀe_t=0 for d≤n, where e_t is actual suffix derivative minus E f_t: the initial zero row is an exact scalar sample for all orders. The theorem also holds with b₀=0. A zero-weight suffix should be treated separately; invertibility of W is used only when expressing the dual and its adjustable rows.

For a word B in T and X of length ℓ, define the reverse integration-by-parts functional
    λ_B(f)=wᵀ B (T E f−E Jf).
The index set includes the empty word. Let F_m=span{ρ_t : grade(t)=m}. All definitions make sense without a dense high-order tableau on either side.

## First overlap: an if-and-only-if test

Let r≥1 and n=m+r, with m≥1, r≤m+1. Assume the SHORTER-word tests:
    λ_B(ρ_t)=0 whenever ℓ≤r−2 and d+ℓ+1≤n.
For r=1 these tests are empty. Then the full method has order p=m+r+1 if and only if
    λ_B(F_m)=0 for EVERY word B of length r−1.                 (1)
This is an equivalence at the boundary once the stated lower tests are known; it makes no claim that arbitrary lower interface tests are necessary for arbitrary splices.

A useful sufficient way to obtain the shorter tests needs no tree-by-tree checks. Let L=W⁻¹ Tᵀ W, or conjugate it by reverse chronological permutation to work with a lower triangular reflected L. The adjoint of scalar J is J*P(x)=∫_x^1 P(z)dz, integration from zero in y=1−x. For each word B let h be its weighted-transpose word acting on 1 and P its scalar version with T* replaced by J*, X by multiplication by x. For every f of the relevant degree with f(0)=0, exact quadrature and Fubini give
    λ_B(f)=⟨Lh−E J*P, E f⟩_w − ⟨h−E P, E Jf⟩_w.             (2)
Indeed deg((J*P)f),deg(P Jf)≤ℓ+d+1 and both vanish at the omitted 0 sample. If every reverse word error up to length r−1 has weighted sum zero separately at each common-node cluster, the shorter tests follow. At length r−1, (1) becomes the single subspace pairing
    span{Lh−E J*P : |B|=r−1}  ⟂_w  E F_m.                    (3)
The full high reverse vectors need not vanish, need not cancel per cluster, and need not annihilate arbitrary polynomials. One can instead use (1) directly if cluster cancellation is unavailable.

Proof of sufficiency. For every t the primitive discrepancy on the suffix obeys the EXACT identity
    e_[t]=T e_t+(T E−E J)ρ_t.
Every derivative through grade m is exact, by induction. Hence every inexact primitive factor first has grade at least m+1. Inside a tree of grade ≤n≤2m+1, at most one primitive factor at the root can be erroneous. All siblings of that factor are exact scalar monomials on ξ. Multiplying their values is a constant times the corresponding power of X. Starting at each possible source primitive and propagating outwards therefore expresses wᵀe_t as a sum of multiples of λ_B(ρ_u), with d_u+ℓ+1 equal to the resulting grade. If d_u<m the source is zero. All others have ℓ≤r−1; equality can occur only at d_u=m. The shorter tests and (1) kill every term.

Proof of necessity, which is stronger than a sufficient word expansion. Given an arbitrary grade-m tree t and any fixed word B of length r−1, start at the unary extension [t]. Its suffix error is exactly (T E−E J)ρ_t because e_t=0. Read B from right to left. Realize each T by adding a new unary root; realize each X by multiplying by the tree [•], i.e. attaching one additional leaf at the current root. Each X multiplies the error exactly by X. Each T propagates it and adds a new source (T E−E J)ρ_v from the current larger tree v. Those new sources all meet words of remaining length at most r−2 and obey the shorter tests. Thus the final tree's output discrepancy is EXACTLY λ_B(ρ_t). Its grade is n. Full order forces zero for each t,B, proving (1).

## Sharp rowwise correction at the first overlap

Keep all quantities except selected allowed entries of the reflected matrix L fixed. Work in reverse chronological coordinate order. Equivalently T is the reversed normalized transpose after every change, and K is rebuilt from the same Π. Start from L⁰ satisfying the shorter tests. Let V be any prescribed matrix of low input columns containing all actual reverse word values h of length ≤r−2; preserving L V preserves those words through length r−1 and all shorter λ. Other row constraints can be included as more columns of V. Let H collect the fixed h columns for words of length r−1. Choose a basis f₁,…,f_a of F_m and put F_{ij}=f_j(ξ_i), (JF)_{ij}=(J f_j)(ξ_i), in the same coordinate order. The nominal high defect matrix is
    D⁰=Fᵀ W L⁰ H−(JF)ᵀ W H.
Let I_i be the accessible predecessor indices of row i: j<i for ERK, j≤i for DIRK; fixed diagonals use the strict version for variations. The high responses achievable at row i while preserving all low responses form
    K_i={δ H[I_i,:] : δ V[I_i,:]=0}.
These row spaces are nested because the predecessor sets are nested. The exact image of all possible changes to D⁰ is
    Σ_i span{w_i F[i,:]ᵀ} ⊗ K_i.                               (4)
In particular, (1) is repairable if and only if −D⁰ belongs to (4). This is a conditional construction theorem with explicit row recovery by independent linear solves, not a dimension heuristic.

For a rank formula, choose a basis for K_s adapted to K_1⊂⋯⊂K_s and let ν_j be the first row where a new basis vector appears. The image dimension is
    Σ_j rank(F[ν_j:s,:]).
The arbitrary forward coefficient vector multiplying basis direction j ranges precisely over the span of the forward samples at rows i≥ν_j; any component outside K_s is immutable. Proof: (4) is immediate by summing w_i F[i,:]ᵀ δ_i H[I_i,:], where the rows δ_i are independent. Expanding in the adapted basis splits (4) into independent components with the stated remaining sample spans. For independent new high probes all freely accessible on a final group of a rows with full-rank F, every previously unforced high pairing is repairable there. This explains why two freely adjustable rows cancel two forward residual shapes in the order-eleven DIRK construction, or why rows with F[i,:]=0 need no high correction.

## Sharp first nonlinear grade, separately

Keep the shorter-test hypothesis with r=m+2 and n=2m+2. Then (1) is still necessary by the same single-spine test. At exactly this grade it is sufficient IF AND ONLY IF one also has
    (T E−E J)F_m  totally isotropic for ⟨u,v⟩_w=uᵀWv;           (5)
that is, every pair of first primitive errors has zero weighted inner product. Indeed a nonlinear error at a root can now have exactly two inexact primitive factors, both of the minimal grade m+1, and no remaining factors or ancestors with positive grade. Its only extra term is their weighted product, proving sufficiency. For necessity use the formal grade-(m+1) defect [t]−(scalar coefficient of Jf_t) times the bushy tree of that grade. Its scalar image is zero and its actual suffix vector is (T E−E J)ρ_t. The rooted sum product of two such defects has grade 2m+2, zero exact output and zero initial-row contribution, so order forces every pairing in (5). With positive suffix weights (5) forces (T E−E J)F_m=0 coordinatewise. Formula (4) by itself establishes only the linear tests; it cannot silently replace (5) at the collision grade.

## Two minimal stage-count order-five examples from the same calculation

Take m=r=2, so p=5. Use a two-row prefix with nodes 0,a for any a≠0, and let Π be linear interpolation of the two derivative values. For the ERK prefix use the explicit row (a,0); for DIRK use (a/2,a/2). On grade two the bush has residual N=x(x−a); the unary chain has residual x²/2 in ERK, N/2 in DIRK. Consequently F₂=span{x,x²} in ERK and F₂=span{N} in DIRK. Everything through grade one is exactly projected. For any reflected block satisfying L1=y with y=1−x the sole independent high error is δ=Ly−y²/2: the two word-length-one input vectors are y and 1−y, and their high primitive errors are δ and −δ. Criterion (3) says exactly
    Σ_i w_i δ_i f(x_i)=0  (f∈F₂).
No componentwise condition δ=0 is necessary.

ERK, six stages. Pick four distinct reflected nodes y=(0,u,v,z) with distinct physical x(v),x(z) nonzero. The omitted physical zero supplies a fifth scalar node. Start from any degree-four quadrature on these five nodes whose suffix weights are nonzero. Every generic such grid works (interpolatory weights, with exceptions if a weight vanishes). The first reflected row is zero; strict causality forces δ(u)=−u²/2. Each of the next two rows has predecessors 0,u, so can assign its row sum and its value of Ly independently. The weighted 2×2 matrix of x,x² at x(v),x(z) is nonsingular. Its solution gives all order conditions in 2+4=6 stages. For a completely rational instance use a=1, y=(0,1/4,1/2,3/4), suffix weights (7,32,12,32)/90, omitted weight 7/90, and
    L rows: (0), (1/4,0), (−1,3/2,0), (0,3/4,0,0).
Here δ=(0,−1/32,1/4,−3/32). Neither high defect vector is zero. The full tableau is given by the preceding K,T formulas.

DIRK, four stages. Use the degree-four left Radau quadrature: physical x₁=(6−√6)/10, x₂=(6+√6)/10, b₀=1/9, (w₁,w₂)=((16+√6)/36,(16−√6)/36). Index the two suffix samples in this reflected construction order and set y_i=1−x_i. Choose a=1, so N(x_i)≠0. Set L₁₁=y₁; then δ₁=y₁²/2≠0. Prescribe δ₂=−w₁N(x₁)δ₁/[w₂N(x₂)]. The second row sum and Ly determine
    L₂₂=(δ₂+y₂²/2−y₁y₂)/(y₂−y₁),   L₂₁=y₂−L₂₂.
Thus 2+2=4 stages and a nonzero, genuinely cross-node cancellation. The same formulas work for any prefix a≠0,x₂. These are alternative parametrized constructions at known minimal stage counts, not new unrestricted upper bounds.

## Direct, characteristic-zero all-tree replays

Independent of the word proof, reconstructing the two displayed examples gives the following forward-chronology tableaux. For ERK the nonzero-length rows (include diagonal zeros where needed) are
    (0)
    (1,0)
    (7/32,1/32,0)
    (3/8,1/8,0,0)
    (−3/8,−3/16,3/4,9/16,0)
    (15/14,1/2,0,−12/7,8/7,0),
with b=(7/90,0,16/45,2/15,16/45,7/90).
For DIRK write d=√6. The four rows are
    (0)
    (1/2,1/2)
    ((23+3d)/100,(−33−13d)/100,(7+2d)/10)
    ((19−9d)/500,(123+47d)/500,(−21−69d)/250,(4+d)/10),
with b=(1/9,0,(16−d)/36,(16+d)/36). In both cases canonical unordered rooted-child multiset enumeration and exact arithmetic in Q(d) passed ALL 17 tree conditions through p=5, with per-order counts 1,1,2,4,9. At order six, ERK fails 14 of 20 and DIRK fails all 20; the examples have order exactly five. The rational ERK has order-six error 7/1440 on the first nonzero discrepancy in child-multiset order; the DIRK's degree-five quadrature error is −1/600. These are finite exact checks, not numerical diagnostics.

A concise independent replay from the stated complete rows is:
```python
import sympy as S
Q=S.Rational; d=S.sqrt(6)
Er=[[0],[1,0],[Q(7,32),Q(1,32),0],[Q(3,8),Q(1,8),0,0],
    [-Q(3,8),-Q(3,16),Q(3,4),Q(9,16),0],[Q(15,14),Q(1,2),0,-Q(12,7),Q(8,7),0]]
Eb=[Q(7,90),0,Q(16,45),Q(2,15),Q(16,45),Q(7,90)]
Dr=[[0],[Q(1,2),Q(1,2)],[(23+3*d)/100,(-33-13*d)/100,(7+2*d)/10],
    [(19-9*d)/500,(123+47*d)/500,(-21-69*d)/250,(4+d)/10]]
Db=[Q(1,9),0,(16-d)/36,(16+d)/36]
def check(R,b):
    s=len(b); A=S.Matrix([r+[0]*(s-len(r)) for r in R]); b=S.Matrix(b)
    trees=[]; counts=[]
    for n in range(1,7):
        layer=[]
        def visit(rem,k,children):
            if not rem:
                weight=S.ones(s,1); factorial=n
                for j in children:
                    weight=weight.multiply_elementwise(trees[j][2]); factorial*=trees[j][1]
                passed=S.expand(b.dot(weight)-Q(1,factorial))==0
                layer.append((n,factorial,(A*weight).applyfunc(S.expand),passed));return
            for j in range(k,len(trees)):
                if trees[j][0]>rem:break
                visit(rem-trees[j][0],j,children+[j])
        visit(n-1,0,[]); trees.extend(layer); counts.append((sum(t[3] for t in layer),len(layer)))
    return counts
assert check(Er,Eb)==[(1,1),(1,1),(2,2),(4,4),(9,9),(6,20)]
assert check(Dr,Db)==[(1,1),(1,1),(2,2),(4,4),(9,9),(0,20)]
```

**Positive-weight nonlinear corollary.** At r=m+2, positive suffix weights collapse (5) to the LINEAR pointwise interpolation requirement T E F_m=E J F_m. It automatically implies (1), since then every λ_B annihilates F_m for words of any length. In particular the first ordinary suffix row at a nonzero ξ must integrate all f∈F_m entirely on earlier suffix samples; at that first row the precise tests are (Jf)(ξ)=0 in ERK or (Jf)(ξ)=γ f(ξ) for one shared diagonal γ in DIRK. These are genuine restrictions in this construction, not global nonexistence claims.

The entire positive-weight first-collision repair, including preserving low reverse word actions, is again one causal linear problem rather than a quadratic search. With reflected H replaced by the full identity and ΔL V=0 as before, its target is (JF)ᵀW−FᵀW L⁰. Apply (4) with K_i the row vectors supported on I_i and annihilating V. They are nested, so exactly the same adapted-basis rank formula and independent recovery solve the complete condition. This links the kernel/causality criterion for clean forward donors to sharp reverse-word cancellation at the very first grade in which two imperfect primitives can collide.
