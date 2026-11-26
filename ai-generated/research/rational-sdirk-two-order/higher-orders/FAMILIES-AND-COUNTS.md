# Smaller rational strict SDIRK families through order twenty

These are exact ordinary rooted-order constructions over the rationals. Literal common diagonals are \(1/7\) on the odd branch and \(1/4\) on the even branches. The outputs can be signed. The stage counts are not asserted to be minima, and do not change the real-algebraic upper table.

The proof has three parts. HEAD-PREPARATION-AND-FRONTIER.md gives the freedom and induction for protected early rows and the genuine scalar frontier payment. RATIONAL-GATES.md supplies the rational quadratures, next-order defects and any mixed sample determinants. The recipes below specify the physical counts, stages and dependencies. In ordinary two-order steps below the only old decoder invoked for order is the stated one; if the old stage space happens to supply extra frontier moments they pose no obstruction.

## Odd branch: a free midpoint sample pays one frontier

Begin with the already proved eleven-stage rational order-seven seed, common diagonal \(1/7\), and its grade-four decoder supplied by ordinary order. The \(p=9\) receiver has four early output stages, at \(-1,-2,1/2,z\), and four pivotal ladder clocks, in order \(0,2/7,4/7,6/7\). Use the rational scalar gate for precisely these clocks in RATIONAL-GATES.md. The first two early rows are individually exact through size five. The old moment observations and these two real stage values give a grade-five decoder on the old tableau together with those two early rows. The next row at \(1/2\) is therefore individually exact through size six. No stage is added outside this eight-row output block, giving 19 stages at exact order nine.

For exact order eleven, use \(q=5\), the old order-nine decoder through five, and the actual old midpoint row exact through six. The midpoint alone pays the grade-six frontier, by reflection parity; a full old grade-six decoder is not used and no zero-output startup/sample row is appended. Hence only four final fixed clocks are needed. Use ten scalar sites with the midpoint first, four fresh negative early clocks, and the solved \(z\) followed by the four pins as the five correction pivots. The first row merges with the existing midpoint. The first fresh negative row is locally exact through six. Together with the old midpoint it completes a grade-six decoder inside the head. The last three early fresh rows become locally exact through seven. There are \(19+10-1=28\) stages.

For each later odd \(p=2n+1\), take \(q=n\) and \(d=n+1\). Any two of the preceding fresh negative samples give the stronger old decoder, using ordinary order \(2n-1\). Merge every preceding fresh high sample. Use \(q-t\) new fresh negative clocks, one solved arbitrary pivot, and the last \(a-1\) fixed clocks. All newly protected fresh rows are exact through \(d+1\), so the procedure continues. The fixed ladder at diagonal \(1/7\) has exactly three interior clocks whenever there are at least three pins; all later donor and fresh clocks on this branch are independent negative parameters. The scalar generic lemma therefore applies.

| Exact order | Reused old stages | New high-ready rows | Total |
|---:|---:|---:|---:|
|9|0|1 midpoint through size 6|19|
|11|1|3 through size 7|**28**|
|13|3|3 through size 8|**37**|
|15|3|4 through size 9|**48**|
|17|4|4 through size 10|**60**|
|19|4|5 through size 11|**74**|

## Even seed: the 13-stage order-eight branch

Begin with the already proved seven-stage rational order-six method at common diagonal \(1/4\), with its actual fifth row at \(1/2\) exact through size four. Use the previously verified exact order-eight scalar rule with early clocks \(1/2,-1,1090/1081\) and last fixed clocks \(-3/4,-1/4,1/4,3/4\). Its scalar gate is unchanged. The old decoder through three comes from order six; copy the first old high row and merge it. Choose the next early row at \(-1\) to be pure through size four. It supplies the one missing sample for the grade-four decoder on the old and already assigned rows. Prescribe the third early row at \(1090/1081\) from that decoder so it is exact through size five. This uses the same seven virtual new rows as the known 13-stage construction but an altered strict head, not a reused unverified local profile.

The old order-eight moments plus this one exterior sample now give a true decoder through size five. In particular \(1090/1081\) is beyond 1 and not a root of the relevant shifted Legendre polynomial.

## A branch optimized for order twelve

At \(p=10\), take \(q=4,d=5\) and use the old local-five row at \(1090/1081\) as the single donor. The \(p-1=9\) scalar sites consist of that donor, three fresh negative clocks, the solved point, and four fixed clocks. The three fresh rows become pure through size six, and the total is \(13+9-1=21\). At \(p=12\), merge all three, use \(q=5,d=6\), and choose two fresh negative clocks followed by the solved pivot and the five fixed clocks. The decoder uses one of the old high samples. This gives \(21+11-3=\mathbf{29}\) stages. Continuing with this pattern alone yields even stage counts \(40,51,65,79\) at 14, 16, 18, 20.

## A branch that carries two spare clocks without separate preparation

At \(p=10\) instead use \(q=d=5\) with no merge. Of the five early sites, use two negative and the solved clock as the first three low receivers, each pure through size six. They yield a grade-six decoder on the old and these three rows, using old order-eight observations. The other two early sites are independent negative variables, and their rows become pure through size seven. The mixed sample determinant is paid by the rational rule proof: a variable among those last two sites changes the solved clock, but not the two fixed negative sample coordinates. The order-ten tableau now has 22 stages, with two local-seven rows.

At \(p=12\), take \(q=d=6\) and merge those two local-seven rows. The next early site is the solved clock, made pure through seven. These three sample rows and the old order-ten moments give a grade-seven decoder on the available coordinates. The mixed determinant is again paid by varying one of the remaining independent negative clocks. Those last three early rows are then individually exact through eight. With \(11\) scalar sites and two merges the total is 31. The six early sites are therefore the two merged negative samples, one newly solved local-seven sample, and three newly added negative local-eight samples. Five of them are negative independent parameters for further use, and three are high enough to supply the next degree-eight decoder.

At \(p=14\), use the normal low cap \(q=6\) and the old decoder \(d=8\). The old order-12 moment observations and three negative size-eight samples give this decoder. The spare clock count is now two. Two arbitrary pivots, of which one is the solved clock, precede the \(a-2\) prescribed ladder clocks. Thus no further initial preparation is needed. In a continued branch keep exactly three newly protected fresh stages at each even target; this requires \(t=q-3\) merges. Each added fresh row is locally exact through \(q+3\), so it is eligible as a donor two successive lifts later as well as one lift later. An eligible old stage can be reused more than once; a merge never removes its original row. For an independent terminal target, merge additional eligible old stages if no further high receiver capacity is needed.

Throughout this branch the ladder at diagonal \(1/4\) has at most two interior fixed clocks. In each generic scalar construction use the previous negative clocks and the new negative clocks as separate entries of a joint parameter list. The special solved size-six/size-seven samples at orders ten and twelve are not reused as old donor times in subsequent quadratures. All other required mixed sample gates are covered in RATIONAL-GATES.md. This establishes the following costs without running any solver, compiler or tableau checker:

| Exact even order | Continuing path | Terminal variant of this path | Where its old donors come from |
|---:|---:|---:|:---|
|8|13|13|order-six known row at \(1/2\)|
|10|22|22|no merges|
|12|31|31|two local-seven rows from the 22-stage seed|
|14|41|**39**|three for continuation; five negative local-seven/eight rows for termination|
|16|52|**50**|four for continuation; three order-12 local-eight and three order-14 local-nine rows for termination|
|18|64|**63**|five for continuation; three order-14 local-nine and three order-16 local-ten rows for termination|
|20|**77**|**77**|three order-16 local-ten and three order-18 local-eleven rows|

Each total is the number of physical retained stages plus \(p-1-t\) for its own extension, not a count of contributing clocks. The two initial even targets that build the bank use only ordinary output rows. The order-fourteen-to-twenty path retains the two paid spare clocks in every lift.

## Combined result and scope

The best exact rational counts from the branches above, for orders \(11,\ldots,20\), are
\[
                     28,\ 29,\ 37,\ 39,\ 48,\ 50,\ 60,\ 63,\ 74,\ 77 .
\]
The preceding spare-clock results gave \(29,31,38,40,49,52,61,65,75,79\) in the same range. The improvements come from making output receivers prepare one another, and in the odd branch from paying a scalar frontier rather than buying a whole old decoder at the first step. These are proofs of existence with deterministic rational coefficient recipes and, for the revised order-nine rule, an explicit hand modular check. The generic rational parameter choices need not be expanded into literal coefficient tables to establish the upper bounds. No such later table, Lean theorem replay, held endpoint, or positivity statement is asserted here.
