# A skip-two tableau can realize the rank transcript with O(p log p) stages

This is a **rank-only diagnostic**, separate from the bounded-skip lower-bound theorem. It uses actual finite tableaux over the rationals, with their own actual c=A1 and terminal-only weights. It does not fit any of the prescribed beta-Hankel values and does not construct a high-order RK method.

## Claim

For any integers n>=1 and H>=0, there is a common-diagonal, hop-at-most-two layered tableau with terminal-only output and
```
s <= n+1+sum_(d=1)^(2H) ceil(2n/d)
```
physical stages. For every h=0,...,H and every r=1,...,n, its actual beta-probe square
```
[ b · ((1−c)^k ⊙ B^h c^a)/(k!a!) ]_(0<=k,a<r)
```
is nonsingular. Hence all weaker rectangular rank requirements are met. Taking n=floor((p+1)/2) and H=max(0,p-2) (or H=p-1 for the strict transcript) costs O(p log p). It satisfies this rank transcript for every fixed maximum skip L>=2, because only jumps of one or two are used. This matches the scale of the rank-window lower bound for fixed L, not its exact constant or a growing-L optimality claim.

## 1. Physical slots and synchronized paths

Index levels backwards from terminal depth zero. Give depth 0 exactly n slots, each depth d=1,...,2H exactly ceil(2n/d) slots, and depth 2H+1 one extra slot. The last slot ensures all possible probe endpoints have a subsequent depth from which to receive a nonzero input. Choose n tokens x=0,...,n-1. At hop time t=0,...,H put token x at depth
```
d(t,x)=t+floor(t x/n).
```
At t=0 every token is at depth zero, using its own distinct terminal slot. For t>=1 the depths are nondecreasing in x, each step along a token is one or two, and at any given depth there are at most ceil(n/t) tokens: the integer x lie in a half-open interval of length n/t. Since d(t,x)<=2t, the allocated ceil(2n/d(t,x)) slots suffice. Within equal depth use slots in increasing token order. At every fixed time the tokens are therefore distinct and appear in the same sorted order as x. These are synchronized paths; a physical stage need not be distinct across different times or different paths.

## 2. A single weight assignment with all allowed minors nonnegative

For the following auxiliary order index the physical slots 1,...,s by increasing backward depth, then by slot. Let B(i,j)=T^(ij) whenever d(j)-d(i) is one or two, and zero otherwise. Here T is a sufficiently large positive integer, and every permitted edge is present. Affix a common rational diagonal gamma by A=B+gamma I; reverse the auxiliary indexing if conventional chronological lower-triangular order is desired. Use b_i=1/n on depth zero and b_i=0 elsewhere.

Fix any square submatrix, with its row and column indices increasing. If there is no allowed perfect matching, its determinant is zero. Otherwise there is an allowed increasing matching: whenever two rows i<i' in the matching use columns j'>j in crossed order, the inequalities d(i)<=d(i'), d(j)<=d(j'), and both old differences in [1,2] imply both uncrossed differences in [1,2]. Indeed d(j)>=d(i')+1>=d(i)+1 and d(j)<=d(j')<=d(i)+2, while d(j')>=d(j)>=d(i')+1 and d(j')<=d(i)+2<=d(i')+2. Repeatedly uncross inversions. This argument applies to every minor, even with repeated depth labels among its distinct slots.

In the determinant polynomial in T, the increasing matching, when present, has strictly largest exponent: swapping an inverted assignment increases the sum of products i*j by a strictly positive integer, since the chosen physical indices are strictly increasing. The highest coefficient is +1. Thus for one sufficiently large integer T all minors are nonnegative, and each with an allowed matching is strictly positive. For example taking T>s! dominates every sum of lower-power terms; increase T further if needed. By Cauchy-Binet all B^h are totally nonnegative. For chosen r tokens, the matched step minors of their successive ordered stage sets are positive, hence the minor of B^h from their terminal set to their time-h set is positive. For h=0 this is the identity minor.

## 3. Actual clocks and rank of the actual probes

There are no assigned independent clock labels: c_i is exactly the row sum of A:
```
c_i = gamma + sum_(j:d(j)-d(i) in {1,2}) T^(ij).
```
For every depth d<=2H the sum is nonempty because depth d+1 is occupied. Its largest exponent is i times the last physical index in level min(d+2,2H+1). The latter index is nondecreasing with d and positive. Thus the largest exponent strictly increases with i among these levels, including all n depth-zero rows. In particular T>s ensures the sums, and hence c_i, strictly increase in their auxiliary index (each row has at most s terms and the leading exponent increases by at least one). No row scaling or external clock assignment is needed. The last depth's clock is gamma, but no B^h from terminal support with h<=H reaches that depth.

Factor the actual measured square into terminal probe, B^h, and predecessor probe. For any r terminal columns, the minor of [(1-c_i)^k b_i/k!]_(k,i) has constant sign (-1)^(r(r-1)/2) and is nonzero by the Vandermonde formula, since the c_i increase and b_i are positive. Any nonzero B^h minor from terminal has its columns in depths <=2h<=2H. The associated minor of [c_j^a/a!]_(j,a) is strictly positive, again by increasing actual clocks. Thus all nonzero terms of the double Cauchy-Binet sum have the same sign. One term is nonzero by the token matching minors above. This proves the stated actual square rank for all h,r, including h=0, without fitting any moment value.

For example with gamma=0 and sufficiently large T, every terminal clock is greater than 1, and the positive terminal weights sum to 1. Then b^T c>1, so the second-order literal clock moment b^T c=1/2 already fails. The construction therefore demonstrates exactly the information lost by retaining ranks rather than paid values. It does not rule out stronger full-order lower bounds for skip-two tableaux.
