from scalar import *
from itertools import permutations
X0=tuple(map(F,('-1/2','0','1/4','1/3','1/2','2/3','3/4','1','3/2')))
W0=tuple(map(F,('-1/23625','481/7560','17408/23625','-729/1000','6/7','-729/1000','17408/23625','481/7560','-1/23625')))
C=dict(zip(X0,W0))
nodes=tuple(x for x in X0 if x not in (0,1))
b={x:1/(x*(1-x)*prod(x-z for z in nodes if z!=x))for x in nodes}
def dot(X,Y):return sum((a*b for a,b in zip(X,Y)),F(0))

def pack(first, order, dup=F(1,4), share=F(1), split=F(0), e1=F(1)):
    # first is earliest interior clock of full original weight.
    assert first==order[0] and set(order)==set(x for x in nodes if x!=1-dup)
    n = - C[first]*(1-first)**2/(2*b[first])
    cc=[F(1),*order,dup,1-dup,F(1)]
    w=[e1,*(share if x==dup else C[x] for x in order),C[dup]-share,C[1-dup],C[F(1)]-e1]
    D=[F(0),*(split if x==dup else n*b[x] for x in order),n*b[dup]-split,n*b[1-dup],F(0)]
    return cc,w,D

def assess(X,W,U):
    Y=[1-x for x in X]
    yd=[w*y for w,y in zip(W,Y)]
    y2=[w*y*y for w,y in zip(W,Y)]
    V=[F(0),*W[1:-1],F(0)]
    M=[ [r[i]for r in (U,[u*y for u,y in zip(U,Y)],V)]for i in range(1,4)]
    d3=det(M)
    d4=det([row[:4]for row in [W,yd,y2,U]])
    donors=[W,yd,y2,U,[w*y**3 for w,y in zip(W,Y)],[u*y for u,y in zip(U,Y)],
          [W[0],*([F(0)]*(len(X)-1))]]
    d7=det([row[:7] for row in donors])
    return d3,d4,d7

if __name__=='__main__':
    order=list(map(F,('-1/2','1/3','2/3','1/4','1/2','3/2')))
    for q in (F(1,4),F(3,4)):
        order[3]=q
        X,W,U=pack(order[0],order,q)
        print('known density',list(zip(X,W,U)))
        print('determinants at split 0',assess(X,W,U))
        X,W,U=pack(order[0],order,q,split=F(1))
        print('determinants at split 1',assess(X,W,U))
