"""Independent univariate elimination for HH lost R scale."""
from projection_rankzero import *
sys.path.insert(0,str(ROOT/'sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hl-residual'))
from field_fmpq import Field

def main():
    (M,E,G,Y),masks=frame()
    guards=sum(masks.values(),[])
    pure=[g for g in guards if not g.degrees()[1]]
    res=[strip(M.resultant(z,'a'),pure) for z in (E,G,Y)]
    assert all(res) and [p.total_degree() for p in res]==[663,639,505]
    P=res[0].gcd(res[1]).gcd(res[2])
    fs=P.factor()[1]
    assert [(f.total_degree(),m) for f,m in fs]==[(3,2),(6,2),(3,4),(1,6),(2,39),(3,39)]
    expected=[
      (2,[('front',3,0)]),(2,[('front',1,1),('front',3,0)]),
      (2,[('base',3,0)]),(4,[('base',3,2),('front',1,0)]),
      (6,[('base',3,3),('front',2,0)]),(6,[('base',3,3),('front',2,0)])]
    for (f,k),(degree,support) in zip(fs,expected,strict=True):
        K=Field(f)
        g=K.joint([K.trans(p) for p in (M,E,G,Y)])
        assert len(g)-1==degree
        removed=[]
        for name,group in masks.items():
            for i,p in enumerate(group):
                d=len(g)-1
                g=K.discard(g,K.trans(p))
                if len(g)-1!=d:removed.append((name,i,len(g)-1))
                if len(g)==1:break
            if len(g)==1:break
        assert removed==support and len(g)==1
        print('exact H degree/multiplicity',f.total_degree(),k,'common a degree',degree,'true guard removals',removed,flush=True)
    print('HH off-diagonal M=n=0: all characteristic-zero fields',flush=True)

if __name__=='__main__':main()
