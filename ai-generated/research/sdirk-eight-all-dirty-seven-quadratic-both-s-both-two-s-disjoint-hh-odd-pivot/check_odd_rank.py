from odd_rank import *

sys.path.insert(0,str(ROOT/'sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl-residual'))
from field_fmpq import Field
def cf(T):
    assert not T.degrees()[0]
    return CZ.from_dict({(s,z,0):int(g) for (i,s,z),g in T.to_dict().items()})
def certify():
    G,P,T,R0=odd_project()
    F0=G.factor()[1]
    assert [(f.total_degree(),e) for f,e in F0]==[(3,8),(3,10),(3,24),(6,24),(1,28)]
    for (Q,e),degree in zip(F0,[2,2,4,4,4],strict=True):
        K=Field(cf(Q))
        rows=[K.trans(cf(f)) for f in P]
        fieldrows=sorted(rows,key=len)
        gg=K.joint(fieldrows)
        before=len(gg)-1
        gs=[]
        for i,g in enumerate(T):
            n=len(gg)-1
            gg=K.discard(gg,K.trans(cf(g)))
            if len(gg)-1!=n:gs.append((i,len(gg)-1))
            if len(gg)==1:break
        print('s field',Q.total_degree(),e,'joint z gcd',before,'guards',gs,'left',len(gg)-1,flush=True)
        assert len(gg)==1 and before==degree and gs==[(0,0)]
    print('odd singleton coefficient rank loss impossible over characteristic zero',flush=True)
if __name__=='__main__':certify()
