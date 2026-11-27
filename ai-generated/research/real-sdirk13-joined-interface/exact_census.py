"""Optional restricted census on the one exact geometry; unresolved pivots are counted, never assumed zero."""
from check_reverse_bank import *
from collections import Counter
from collections import defaultdict
res=Counter()
weak=[]
for seq in permutations([0,4,5,6,7],4):
    labels=[3,2,1]+list(seq)
    for a,b in permutations([j for j in labels if j not in [3,7]],2):
        try:
            A,D,c,w1,w2,params=pay_reverse(labels,a,b)
            V,err=test_words(A,D,c,w1,w2)
            gate=mixed_probe(V,a,b)
            rank=lower_rank(V)
            if gate:
                res[f'nonzero mixed, rank >= {rank}']+=1
            else:
                res[f'open mixed, rank >= {rank}']+=1
                weak.append((labels,a,b))
        except AssertionError:
            res['unseparated arithmetic section']+=1
    if sum(res.values())%120<30:
        print(dict(res),flush=True)
print('TOTAL',sum(res.values()),dict(res),flush=True)
print('open regular cases',len(weak),weak[:20],flush=True)
