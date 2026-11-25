# Fin 10, p=8, one off clock: an exact physical-row contradiction

**Source-only mathematical proof and port plan at public main
244c5a160a47f4f5ee3a067a337a18d700ce54b3.** No new Lean check. This does not
touch the census, the four-off case, or any held candidate. All row numbers
below are zero-based **physical** indices of the given tableau. In
particular no coincident-clock rows are identified. The proof uses only
characteristic zero (hence applies to the requested ordered fields).

## Endpoint and notation

Input: the literal A : Matrix (Fin 10) (Fin 10) K, b : Fin 10 → K,
strictness ha, RKResearch.HasOrder 8 A b, the public activated midpoint
H : Reverse.ERKEvenHorizon A b 4, and (OneOff.offKnots A).card=1. Output:
False. The census worker can produce H and consume this branch; nothing
here assumes the branch disjunction or asserts the all-width conclusion.

Use c=nodes A, g=mDef A 1, h=A g, F_j=zeroSpace A j,
E_j=treeSpace A j, c-multiplication pointwise, and τ=Fin.last 9.
For P a polynomial write P(c) for the actual stage evaluation vector.
All moments below mean the reviewed probe Σ b_i c_i^k v_i.
Let G=−a²/2, D=2d, and H_i=h_i/a when a,d have been found.
In this note H_i is the scaled defect, never the midpoint certificate H.

## 1. Earned p8 facts and the actual terminal

H gives dim E4=8 and F4=3, and at τ it gives cτ=1, bτ≠0 and
eτ∈E4. The last index is τ because H.terminal gives a maximal physical
index in Fin 10. For any u∈F3, u*eτ is in F7 by zeroSpace_mul_treeSpace,
and its grade-zero probe is paid (0+7+1=8). It is the one-coordinate
vector uτ eτ, so bτ uτ=0. In particular gτ=hτ=0. No claim about an
arbitrary grade-five defect at τ is used anywhere.

Reverse.backward_count at (j,n)=(5,1) gives dim E5≤9 (5+1+2=8).
Forward_minimal_ranks and explicit_coeff_separated at q=4 apply with
the grade-four cap of eight and the exact order-eight budget. Use
constant_amplitude_of_single_off_of_capacity, then
global_normal_from_amplitude. This yields a≠0,d≠0, the earliest origin and
first clean h receiver, g supported only at c=a and equal there to G, and

    F3 = span(g,h),    F4 = span(g,h,c h),
    A h = (d−c) h,
    mDef A 2 = (2a/3) g + (4d/(3a)−2) h,
    mDef A 3 = (a²/2)g + ((2d²−2a²)/a)h − (d/a)c h.

The displayed λ in grade three is twoLam a d, as one sees by its definition.
The first clean receiver has c=d and h=−ad²/4. Ordinal origin has
c=a,g=G,h=0. first_doubled_clean_clock gives a clean clock D=2d
with h=ad². new_clean_clock_h supplies a clean stage with h≠0 at a
third clock distinct from d and D. The stages in this last sentence need
not be numbered yet. All these are actual-width generic one-off APIs.

## 2. Eliminate the polynomial part in the low-top kernel

Consider the native grade-five family

    P(c) + β g + h Q(c) + η g h,      deg P≤5, deg Q≤2.              (1)

It is a linear map on 6+1+3+1=11 coefficients; omitting η makes the usual
10-coefficient normal map. Each last three term is in F5: g∈F2,
h∈F3, multiplication by the degree-2 clock polynomial uses
zeroSpace_mul_treeSpace (2+1≤8), and gh∈F5 by zeroSpace_mul. P(c)∈E5
by evalNodes_mem_treeSpace. This proves the p8 versions of
wide_defect_mem and wide_profile_mem directly, without an order-nine
hypothesis. Write Ptop for P.coeff 5, read as a linear coordinate.

We require two exact scalar facts:
* If deg P≤4, P(0)=P(1)=0, and the actual probes of P(c) vanish for
  k=0,1,2, then P=0. Factor P=X(X−1)R with deg R≤2, and use
  beta_probe_coeff with n=2, k≤2. Pad the last two zero coefficients
  in beta_pair_decoder. It gives R=0 since R.coeff 3=R.coeff 4=0.
* If deg P≤3, P(0)=0 and the probes vanish for k=0,1,2, then P=0.
  Factor P=X R with deg R≤2. Use anchor_probe_coeff (n=2, k≤2);
  the three unknown coefficients of R satisfy exactly moments_detect
  with size 3 and shift d=2. The denominators' maximum index is 6≤8.
  Consequently the degree-≤4 polynomials having P(0)=0 and those
  three zero probes form a space of dimension at most one: the top
  coefficient injects. This last statement also follows directly by
  subtracting suitably scaled copies to cancel coefficient 4.

For a kernel relation (1) with Ptop=0, P(c) is in F5 and hence paid at
k=0,1,2 (k+5+1≤8). Its origin is zero by origin_zeroSpace and c0=0,
so P(0)=0. At τ the non-polynomial parts vanish (gτ=hτ=0); the kernel
relation gives P(1)=0. Thus the first scalar test gives P=0. At the
off origin, h=0 and g≠0 give β=0. At the three actual clean nonzero-h
clocks in §1, the remaining relation gives three distinct roots of Q,
hence Q=0 by the finite-root theorem. This uses no assumption about the
individual b_i or the cancellation of same-clock weights.

Apply rank-nullity to (wideProfile,Ptop) with target E5×K, dimension
≤10<11: a nonzero kernel vector has P=β=Q=0 by the preceding argument,
therefore η≠0 and **g h=0**. In the normal map, a relation with Ptop=0
has all coefficients zero. Hence Ptop is injective on its kernel, and
the 10-coefficient map has image dimension ≥9. The dim E5≤9 bound
then gives equality of that image with E5 and exact dim E5=9. The
normal kernel is a line on which Ptop is nonzero. By subtracting a
suitable multiple of a nonzero kernel vector, **every E5 vector has a
representation P(c)+βg+h Q(c) with deg P≤4 and deg Q≤2.** For any such
representation of v∈F5, P(c)∈F5 and P(0)=0 with the same three paid
probes; P(1)=0 is required only for the earlier kernel proof and is
not assumed for v.

## 3. Earn the five numbered rows, then the sixth

A literal duplicate physical row at i<j contracts to strict order 8
on Fin 9 by exists_merge_equal_rows. The public even floor (q=4) excludes
that. Apply the actual prefix selector theorem prefix_equal_physical_rows
(the four selectors of chartNode and chartDefect). Its first-four proof
is the public order-nine body with only the no-duplicate proof replaced
by this order-eight floor argument; the body uses the generic rank and
normal-form facts in §1. More explicitly:

* Row 0 is zero in c,g,h by strictness. If the first nonzero c is later
  than 1, row 1 agrees in all three features with 0; the one preceding
  actual row is certified by the prefix selectors, forcing a raw duplicate.
  Thus row 1 is (a,G,0).
* If the first nonzero h is later than 2, FirstH.prefix_features forces
  row 2 to be either the zero or off state with h=0. The same scoped
  prefix selector comparison gives a raw duplicate, so row 2 is the
  first clean receiver (d,0,−ad²/4).
* If the first changed h-clock of first_doubled_clean_clock is later
  than 3, that theorem's preceding ThreeFeatures forces row 3 to equal
  one of the three existing profiles and again a raw duplicate. Thus
  row 3 is (D,0,ad²). The new-clock row cannot be one of 0,1,2 because
  its h≠0 and its clock is D≠d.
* At row 4 all predecessors are now the four known normal features.
  The generic four_feature_residuals and normal_clean_clocks with
  e=2d leave clean clocks 0,d,D. If row 4 is off then g=G, c=a and
  h=0 by §2, hence duplicates row 1. In the clean 0,d cases the
  public scalar normal_clean_at_zero / normal_clean_at_d force the
  earlier h (as before), again a raw duplicate. Hence row 4 is clean at
  D, and comparison with row 3 gives h4≠h3. This is the actual fifth
  row, not an assertion that there are two freely supplied D states.

Evaluation at rows <4 is independent on E4 by the four grade-two
prefix selectors. Let T be selector 3. The E4 vector (c−d)h−d h3 T
is zero on rows 0–3 and at 4 equals d(h4−h3)≠0, so evaluation at
rows 0–4 is independent on E4 (extend_independent_before). Even
when a=d or a=D, the g coordinate distinguishes the off row.

**Chronological same-clock interpolation is forbidden.** At grade five,
dim E5=9 and (j,n)=(5,1) is a saturated reverse payment. Suppose a
physical row r in E5 evaluation were an affine combination of previous
rows all of the same clock c_r, and E4 evaluation of rows <r were
independent. Then the contrast q=e_r−Σ λ_i e_i is a nonzero vector
of annih(E5), supported at indices ≤r and on that clock. Since
A E4⊆E5, Aᵀq∈annih(E4); strictness gives support before r, so
Aᵀq=0 by the independent prefix. Multiplication by 1−c preserves
span(q). The public no_joint_invariant_of_paid_capacity kills this
line (10=dim E5+1, 5+1+2=8). This is exactly the mathematical
order-nine causal interpolation argument at the **different, paid**
order-eight indices. It holds for signed affine coefficients.
The profile representation from §2 implies that any repeated
(c,g,h) and any interpolated h between two earlier clean same-clock
rows give that forbidden evaluation relation.

At row 5, an off row repeats row 1 (gh=0); a clean row at D is an affine
combination of the two earlier clean D rows, whose h differ. Both
are impossible by the preceding paragraph and independence before 5.
The vector cleanClockTest is zero at all predecessors (on an off row
use cleanClockTest_zero_off). It belongs to E3 as degree 3 polynomial
plus g. Strictness and cleanClockTest_action give

    c5=z,  g5=0,  z≠D,  H_5=h5/a = h0(z) := z²(z−D)/(4d).

At z=0 or d this repeats the feature of row 0 or 2 respectively, so
z≠0,d,D. In particular H_5≠0. The same test, zero earlier and nonzero
at row 5, extends independent E4 evaluation to rows <6. At row 6
the same repeated-off or affine-at-D logic gives g6=0 and c6≠D.
These consequences do not claim cleanliness or a branch for later rows.

## 4. The actual E4 terminal profile is a cubic, not the p9 quartic

Use treeSpace_coeff_sup at q=4 and the actual F4 from §1 to represent

    eτ = P_T(c)+β_T g + (h/a) Q_T(c),    deg P_T≤4, deg Q_T≤1.       (2)

Absorbing the nonzero a into Q_T is harmless. At physical row 0,
P_T(0)=0. At τ, gτ=hτ=0 and cτ=1 give P_T(1)=1. The two clean D
rows 3 and 4 are before τ, have different h/a, and both have eτ=0.
Subtracting their two equations gives Q_T(D)=0, then P_T(D)=0, so
D≠1. Thus Q_T(X)=ρ(X−D) for some ρ (possibly zero for now).

For k=0,1,2,3, the defect part of (2) is in F4, paid by
k+4+1≤8. The actual probe of eτ is bτ (cτ=1), and so the four
probes of P_T(c) are equal. Write P_T=X B with deg B≤3. Then for
k=0,1,2 the probe of (X²−X)B(c) vanishes by subtraction of consecutive
equal probes. beta_probe_coeff with n=3 uses only k+3+3≤8. Pad its one
zero high coefficient for beta_pair_decoder. It yields B as a scalar
multiple of the public monic cubic

    L(X) = X³ − (3/2)X² + (9/14)X − 1/14
         = (X−1/2)(X²−X+1/7).

Since L(1)=1/14 and P_T(1)=1, the coefficient is 14. In particular
P_T=14 X L and L(D)=0 as D≠0. This is not the order-nine p=9
Jacobi endpoint formula: the degree-four representation in **E4**
has spent only p8's actual paid moments.

## 5. One rank-nine defect combination breaks the seventh-row choice

Set
    J = A(c h/a),
    V = mDef A 4 + 2a² h,
    W = V − (4d/5)J.

All three are in F5 by the paid grade operations, hence have the
degree-≤4 polynomial-part representation of §2, with H_i=h_i/a
multiplying a residual quadratic. No terminal vanishing of J,V,W
is used. Actual predecessor identities, not order-nine homogeneous
payment, give the following two scalar actions for any clean row r≤6.
Put x=c_r, U=h_r/a; with the publicly defined functions
m1=x²/2+2U, m2=x³/3+(4d/3)U, m3=x⁴/4+(2d²−dx)U, they are

    jValue = D(d−x)U + ((z−d)m3−d(3z−2d)m2+2d²z m1)/(4d);
    vValue = (3d+z)m3 − (2d²+3dz)m2 + 2d²z m1 − x⁵/5;

and J_r=jValue, V_r=vValue. To derive on the actual original rows,
define the cubic predecessor functions

    Js(y)=((z−d)y³−d(3z−2d)y²+2d²zy)/(4d),
    Vs(y)=(3d+z)y³−(2d²+3dz)y²+2d²zy.

For each earlier row l<r:
    c_l H_l = D H_l + Js(c_l) − Js(a)/G · g_l,
    c_l^4   = Vs(c_l) + (a^4−Vs(a))/G · g_l.
The five source types are (0,0,0), (a,G,0), clean d with H=h0(d),
clean D with arbitrary H, and clean z with H=h0(z). The identities
follow by substitution (the Vs difference is y(y−d)(y−D)(y−z)).
They are also the checked, order-free Seven.source_interpolation
scalar identities. Apply A causally on the stated r. In the clean
receiver row x, §1 gives A H=(d−x)U and
    A c^k − a^k h/G = m_k       (k=1,2,3).
Hence the displayed jValue/vValue equations, with no reliance on
the Fin 12 source theorem at a different width.

The following exact scalar identity is the cancellation in the
public Seven.master_residual (its Radau and interpolation terms
cancel algebraically, so none are needed as hypotheses):

    vValue − (4d/5)jValue + (4d/5)(x²−2d²)U
      = (x−D)(x−z)(4d U−x²(x−D))/5.                               (3)

At the doubled rows 3 and 4, the affine function jValue at x=D is
d⁴/3−(4d²/3)U by j_value_doubled. In the actual representations,
both rows are clean and their U differ. Comparing two affine values
at this one clock gives **P_J(D)=d⁴/3≠0**. By (3), at those same
rows W has only the slope −(4d/5)(D²−2d²), so **P_W(D)=0**.
The polynomial parts P_J, P_W both have degree≤4, vanish at 0,
and have the three k=0,1,2 paid zero probes. The second scalar
test in §2 says the space has dimension at most one; since it
contains nonzero P_J, P_W is proportional to P_J. The two values
at D force P_W=0 (zero polynomial, not just zero evaluations).

On each clean stage W thus equals H times a quadratic Q_W.
At the three distinct clocks d,D,z use rows 2,3,5, each with nonzero
H. Equation (3) has zero RHS (at d by H=h0(d), at D/z by their
factors); therefore Q_W agrees there with −(4d/5)(X²−2d²).
A degree-≤2 polynomial cannot have three distinct roots unless
zero. It follows that on every clean row
    W=−(4d/5)(c²−2d²)H.
At the actual seventh row r=6, we already proved it clean with x≠D.
Compare this exact W with (3). Either x=z or H_6=h0(x).

We now exclude x≠z without needing any later row or a Radau scalar.
Factor L=(X−D)L₂, deg L₂≤2, using L(D)=0; L₂(0)=1/(14D)≠0.
At any of the clean nonterminal rows with x≠0,D and H=h0(x),
(2), P_T=14XL and Q_T=ρ(X−D) imply

    14 L₂(x) + (ρ/(4d)) x(x−D) = 0.                               (4)

This is a **nonzero quadratic-or-lower** polynomial (its constant
term is 1/D). Rows 2 and 5 have d and z satisfying it, so (4) has
no third distinct root. Under x≠z, x≠D and H_6=h0(x), if x=0
then row 6 repeats row 0 (forbidden). Otherwise (4) forces x=d;
its H=h0(d) then repeats row 2 (also forbidden). Thus x=z.
The two actual clean z rows 5 and 6 must have H_5≠H_6, otherwise
the same-clock interpolation contradiction applies at 6.

## 6. Close on the same original tableau

The two physical z rows are both before τ. Their equations (2)
give Q_T(z)=0 and P_T(z)=0. Since z≠D and deg Q_T≤1, the two
roots z,D force Q_T=0. At the clean row of clock d, (2) then gives
P_T(d)=0, hence L(d)=0. But L(D)=L(2d)=0 is already forced.
These two roots are impossible:
* if d=1/2, L(2d)=L(1)=1/14≠0;
* if 2d=1/2, d=1/4 and L(1/4)=5/448≠0;
* otherwise both d²−d+1/7=0 and (2d)²−2d+1/7=0. Subtracting
  four times the former from the latter gives d=3/14, at which
  the former is −5/196≠0.

Contradiction on the requested one-off branch, on original Fin 10 rows.
No order-nine predicate, positive individual weight, numerical
abscissa ordering, disjoint on/off clock sets, guessed rank or
missing row closing lemma entered. The only chronological
counting input is strictness and the existing width-nine floor for a
**proved raw duplicate**, never mere equality of features.

## Source checking boundary

This is a new source-level derivation from the public inputs. The attached
Lean helpers are candidates for later serial checking, not a checked
end-to-end endpoint. Keep the endpoint/census/branch dependencies separate.
Require full native materialization and a named ordered audit at
RKResearch.HasOrder 8 before updating the native floor; the four-off
branch is separate work.
