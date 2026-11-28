"""Count the literal clock-only SDD/DDD placements before scalar fits."""
from itertools import permutations,product,combinations
import sympy as S
H,v=S.symbols('H v')
def compute():
 out={}
 for front,rear in product('AS',repeat=2):
    yy=[H,H-v,H-2*v] if rear=='A' else [H,H-v,H+v-2]
    base=[('h=0',H),('m=0',H+2)]
    base += [(f'D{i+1} hits S first',t) for i,t in enumerate(yy)]
    base += [('duplicate D',a-b) for a,b in combinations(yy,2)]
    parity = [(f'D{i+1} centered',2*t-H) for i,t in enumerate(yy)]
    parity += [(f'D{i+1}/D{j+1} opposite',yy[i]+yy[j]-H) for i,j in combinations(range(3),2)]
    old,new,survive=[],[],[]
    for i,j in permutations(range(3),2):
        q= yy[j]-2*yy[i] if front=='A' else yy[j]+yy[i]-2
        aa=S.Poly(q,H,v)
        n=(i+1,j+1)
        assert aa.total_degree()==1
        guard=base+[('front first-departure',yy[i]-2)]
        if front=='A': guard += [('front arithmetic 3u−2',3*yy[i]-2)]
        if rear=='A':guard += [('rear arithmetic 3v−2',3*v-2)]
        if rear=='S':guard += [('rear star v=1',v-1),('rear star v=2',v-2)]
        bad=[a for a,b in guard if S.Poly(b,H,v).rem(aa).is_zero]
        if bad:old.append((n,bad));continue
        bad=[a for a,b in parity if S.Poly(b,H,v).rem(aa).is_zero]
        if bad:new.append((n,bad));continue
        survive.append((n,str(aa.as_expr())))
    out[front+rear]=old,new,survive
    print(front+rear, 'base',old,'parity',new,'survive',survive)
 expected={'AA':(2,2,2),'AS':(0,2,4),'SA':(0,0,6),'SS':(0,2,4)}
 assert {m:tuple(map(len,parts)) for m,parts in out.items()}==expected
 return out
if __name__=='__main__':compute()
