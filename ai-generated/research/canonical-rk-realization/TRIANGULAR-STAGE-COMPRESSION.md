# Finite-order triangular stage compression

In a lower-triangular Runge–Kutta tableau, a chronological stage relation can remove a physical stage without changing the prescribed diagonal. Over a field, one can test the earlier stage rows without their highest-order unary trees: the missing output can be repaired in the last active row. The result preserves every rooted output through order $p$. It need not preserve an unpaid witness or exact order $p$.

## Graded redirection

Work over a commutative semiring $R$, with a lower-triangular tableau $(A,b)$ on stages $1,\ldots,s$. Write $\gamma_i\coloneqq a_{ii}$ for the physical diagonal and $c\coloneqq A\mathbf 1$ for the actual clocks. For a rooted tree \(t\), define the scalar entry
\[
\Phi_i(t)\coloneqq\bigl(\boldsymbol{\Phi}_t(A)\bigr)_i.
\]
In the notation of the reviewed rooted-tree definitions, the recurrences are
\[
\Phi_i(\bullet)=1,\qquad
\Phi_i([t])=\sum_j a_{ij}\Phi_j(t),\qquad
\Phi_i(t\mathbin{\#}u)=\Phi_i(t)\Phi_i(u).
\]
For $q\ge 0$ define the stage, unary and output rows by
$$
v_i^q\coloneqq(\Phi_i(t))_{1\le |t|\le q},\qquad
U_i^q\coloneqq\sum_j a_{ij}v_j^q,\qquad
Y^q\coloneqq\sum_i b_i v_i^q.
$$
Here $v_i^0$ is empty. The coordinate of $U_i^q$ indexed by $t$ is $\Phi_i([t])$, where $[t]$ is the unary lift. We preserve the actual scalar outputs $Y^p$, independently of how the rooted order conditions are normalized.

**Graded certificate.** Fix $p\ge 1$. Retain a set $S$ in its original order and choose a cutoff $0\le h_i\le p$ for each retained stage, meaning that its responses through tree size $h_i$ must agree. Put $q_i\coloneqq\max(h_i-1,0)$, and allow strict donors only in $P_i\subseteq\{j\in S:j<i,\ h_j\ge q_i\}$. With the inherited diagonal and weights $\beta_i=0$ for $h_i<p$, the reduced tableau exists with these stage rows and the original $Y^p$ exactly when its taps and weights can solve
$$
\gamma_i v_i^{q_i}+\sum_{j\in P_i} a'_{ij}v_j^{q_i}=U_i^{q_i}
\quad (i\in S),\qquad
\sum_{\substack{i\in S\\h_i=p}}\beta_i v_i^p=Y^p.
\qquad (1)
$$
The row tests are vacuous for $h_i\le 1$. Necessity follows from the unary lifts and the output. For sufficiency, induct on tree size simultaneously at all retained stages. A leaf already agrees. At a root of size at most $h_i$, every child has size at most $q_i$; the induction hypothesis gives the agreed child response at every allowed donor, including the diagonal term. The row equation gives its unary factor, and the product agrees. The last equation then pays the output.

Over a ring, these are module membership tests after subtracting the terms to be kept. For example, to delete stage $k$ while keeping every surviving stage row through $p$ with every earlier survivor allowed as a donor, a strict consumer $i>k$ must express $a_{ik}v_k^{p-1}$ in the span of the surviving strict prefix of row $i$. The replacement cannot use the receiver itself or any later stage. At the output one can instead use *all* surviving $v_j^p$ to express $b_kv_k^p$; if $b_k=0$, the old surviving weights already work. Over a field and with unrestricted prefixes, the first nonzero strict consumer suffices, because its tap can be divided out and the prefixes are nested. When all grade-eligible earlier donors are allowed, only new positive records of $q_i$ among the consumers need to be tested: a successful earlier test at a larger or equal cutoff restricts to the later one and still uses eligible donors. This simplification need not hold for nonunit taps or arbitrary row supports.

**Simultaneous substitution.** Suppose cutoffs on all original stages satisfy $b_i\ne 0\Rightarrow h_i=p$ and $a_{ij}\ne0,\ j<i\Rightarrow h_j\ge h_i-1$. Let $P$ select the retained rows, and let $T$ have columns indexed by $S$ and identity rows at the survivors. At an omitted positive-cutoff stage require
$$
v_i^{h_i}=\sum_{\substack{j\in S,\ j<i\\h_j\ge h_i}}T_{ij}v_j^{h_i};
\qquad (2)
$$
at an omitted zero-cutoff stage use the zero row. Then
$$
A^0\coloneqq PAT,\qquad (\beta^0)^\top\coloneqq b^\top T
\qquad (3)
$$
satisfy (1) for the unrestricted grade-eligible strict prefixes. Indeed, substituting (2) pays each required child coordinate and each active output row. A strict donor is sent only to its own retained index or to earlier ones, so only $a_{ii}$ contributes to the new diagonal at retained stage $i$. If a further restriction $P_i$ is imposed, the induced strict support of $PAT$ must lie in $P_i$. With a common diagonal, $A=\gamma I+B$ gives $A^0=\gamma I+PBT$. The induced weights are supported only at cutoff-$p$ stages. A stage of cutoff at least two keeps its actual clock $\Phi_i([\bullet])$; preserving clocks at smaller cutoffs requires the leaf-donor equations as well.

A useful choice is $h_i\coloneqq\max(p-\delta_i,0)$, where $\delta_i$ is the shortest number of strict edges from an active stage backwards to $i$. Use $\delta_i=\infty$ and $h_i=0$ if there is no such path. The cutoff drops by at most one along a backwards edge, and exactly the originally active stages have cutoff $p$. Thus no previously inactive stage acquires a nonzero weight under (3), though old weights may cancel. All cutoff-zero stages can be erased: they do not enter any nonempty required child row. After a grade-preserving redirection the truncated shortest distance $\min(p,\delta_i)$ to a retained stage cannot decrease. In fact a new path of length $d$ from an active stage forces $h_i\ge p-d$. A shortest original path to a positive-cutoff inactive stage also supplies a strict consumer whose required child cutoff is exactly $h_i$. The construction does not preserve individual path lengths.

## The top unary repair

Now take $p\ge 2$ and work over a commutative ring. Keep all readout coordinates through order $p$ except those with a unary root and $p$ vertices:
$$
D_i\coloneqq(\Phi_i(t))_{\substack{1\le |t|\le p\\t\notin\{[u]:|u|=p-1\}}},
\qquad U_i\coloneqq U_i^{p-1}.
\qquad (4)
$$
The row $D_i$ contains the entire $v_i^{p-1}$. Agreement through $p-1$ at a stage already fixes its order-$p$ nonunary entries: at a root with at least two children, each child has size at most $p-2$, so each unary factor is an agreed entry through $p-1$. A relation on the lower rows alone does not generally lift to the $D_i$: the nonunary coordinates are products of lower stage entries, not linear functions of them.

Suppose $A^0$ on $S$ uses only the permitted strict donor sets $P_i$ and keeps the inherited diagonal and the original $v_i^{p-1}$. Choose weights $\beta$ matching the $D$-output. Let $\pi$ restrict child rows from sizes at most $p-1$ to sizes at most $p-2$, allowing the empty restriction at $p=2$. Set
$$
U_i^0\coloneqq\sum_{j\in S}a^0_{ij}v_j^{p-1},\qquad
F_i\coloneqq\operatorname{span}_R\{v_j^{p-1}:j\in P_i\}\cap\ker\pi,\qquad
\mathcal R\coloneqq\sum_j b_jU_j-\sum_{i\in S}\beta_iU_i^0.
$$
The agreed lower unary outputs give $\pi\mathcal R=0$. With the weights, diagonal and lower stage rows fixed, the omitted unary outputs are repairable exactly when
$$
\mathcal R\in\sum_{i\in S}\beta_i F_i .
\qquad (5)
$$
Indeed, a row change $z_{ij}$ preserves its lower unary entries only if $\sum_{j\in P_i}z_{ij}v_j^{p-2}=0$. Conversely these equations preserve all retained $v_i^{p-1}$ by (1). Its change to $U_i^0$ is then exactly an element of $F_i$, and every element of $F_i$ is available by its module representation. The top nonunary entries stay fixed. This proves (5).

For unrestricted strict prefixes the $F_i$ are nested. Over a field with some nonzero $\beta_i$, the sum in (5) is $F_\ell$ at the last active stage $\ell$. Therefore one strict row suffices for any feasible repair. Over a ring the scalar factors in (5) cannot in general be removed.

## Compression at the last active stage

**Theorem.** Over a field, let $b\ne0$ and $m\coloneqq\max\{i:b_i\ne0\}$. There is a tableau on exactly
$$
1+\operatorname{rank}\{D_i:i<m\}
\qquad (6)
$$
retained stages in the inherited order, with the inherited diagonal and the original $Y^p$. It retains stage $m$ with weight $b_m$ and every surviving stage row through $p-1$. In particular it keeps all surviving actual clocks if $p\ge 3$.

First discard the suffix after $m$. It has zero weights and no earlier row uses it. Keep $m$ and choose the chronological greedy basis of the $D_i$ before it. Every omitted $D_i$ is a combination of retained earlier rows. Use these relations for $T$, with identity rows at the survivors. Since each $D_i$ contains $v_i^{p-1}$, substitution gives $U_i^0=U_i$ at every retained row for $A^0=PAT$. In fact at this point the retained stage responses all agree through $p$ by the row part of (1). The induced weights $\beta^\top=b^\top T$ match the $D$-output; $\beta_m=b_m$, since no omitted earlier stage was redirected to $m$.

The remaining residual is
$$
\mathcal R=\sum_{i\notin S}b_i\rho_i,\qquad
\rho_i\coloneqq U_i-\sum_{\substack{j\in S\\j<i}}T_{ij}U_j .
$$
For an omitted $i<m$, each original donor of $U_i$ has index at most $i$. After substitution even the diagonal term uses only retained indices before $m$. The same holds for the other terms in $\rho_i$. Also $\pi\rho_i=0$: every lower unary coordinate belongs to the $D_i$ relation. Thus $\rho_i\in F_m$ for the unrestricted strict prefix. Represent $\mathcal R/b_m$ by that prefix and adjust only row $m$. Equation (5) restores the unary outputs without changing the inherited diagonal or any retained row through $p-1$. Earlier retained rows keep their entire responses through $p$; at $m$ only the top unary coordinates can change.

Over a ring the same construction works when the earlier $D$-row representations are supplied and $b_m$ is a unit. More generally (5) is the exact test for the chosen weights and lower stage rows. As a sufficient alternative, for each omitted $i$ require $b_i$ to lie in the ideal generated by weights $\beta_\ell$ of retained stages $\ell>i$, with unrestricted prefixes. Then $\rho_i\in F_\ell$ for each such $\ell$, so the ideal expression puts $b_i\rho_i$ in the sum in (5).

The unit or ideal condition cannot simply be dropped for this fixed-weight repair. Over $\mathbb Z[1/2]$ take a three-stage explicit tableau with $a_{21}=1$ as its only tap and $b=(-5/2,1/2,3)^\top$. Its order-two outputs are $(1,1/2)$. All $D_i=(1)$ at $p=2$, so substitution retains stages 1 and 3 and induces weights $(-2,3)^\top$. Repairing the omitted output with these weights would require $3a'_{31}=1/2$, which has no solution in the ring. This does not rule out choosing different weights.

## Consequences at a physical stage minimum

Here a minimum means a minimum for order **at least $p$** in a class admitting the indicated compressions, such as ordinary explicit tableaux or triangular tableaux with a prescribed common diagonal over a field. Agreement through $p$ need not preserve exact order $p$. Further support constraints, signs, bounds on coefficients or a prescribed position-dependent diagonal can prevent the changes; neither positivity nor stability is asserted.

The cutoffs from shortest active distance give an additional prefix test over a field. Keep a positive-cutoff stage exactly when its row at its own cutoff is outside the span of earlier rows with at least that cutoff. Any earlier discarded row can be replaced by its own earlier representation, restricted to the needed size. Thus (2) applies. At a true minimum no stage has cutoff zero, and every stage of cutoff $h$ increases
$$
r_h(k)\coloneqq\dim\operatorname{span}\{v_j^h:j\le k,\ h_j\ge h\}.
$$
In a chronological interval $(a,b]$ there are at most $r_h(b)-r_h(a)$ stages of cutoff exactly $h$. A cutoff-one stage must be the first and is unique, since every positive-cutoff stage has the same nonzero leaf response. There are at most two cutoff-two stages, since their test rows are $(1,c_j)$.

Taking uniform cutoff $p$ in (2) shows that the full physical rows $v_i^p$ are independent at a minimum. By (6) the last physical stage is active and all $D_i$ before it are independent. Thus the space of $D$-relations has dimension at most one and every nonzero relation has nonzero last coefficient. Equivalently, the span of full physical rows has at most one independent direction supported only on the top unary coordinates.

If the class also admits topological reindexing, any nonzero $D$-relation has a nonzero coefficient at **every sink** of the actual strict donor-to-receiver graph. An inactive sink could be deleted outright. Any sink can be moved last while keeping the other stages in their old relative order. This preserves the inherited diagonal and all elementary outputs; applying the preceding independence in that order proves the assertion for that sink. Equal clock labels play no role.

The extra last slot in (6) is necessary in general. At $p=2$ all $D_i=(1)$. A two-stage explicit tableau with $a_{21}=1$ and weights $(1/2,1/2)$ attains order two, whereas a one-stage explicit tableau has $c_1=0$ and cannot pay $b^\top c=1/2$. With prescribed lower stage values and weights, (5) tests further repair using the strict prefixes of the *new* retained stages, not the old later rows or the new last active row itself. These are sufficient algebraic compressions and necessary structural conditions at a minimum, not a characterization of the unrestricted nonlinear stage minimum.
