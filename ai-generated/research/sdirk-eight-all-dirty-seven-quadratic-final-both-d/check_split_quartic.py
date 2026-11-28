"""Exhaust the split quadratic graph over all algebraic closures of Q."""
import split_projection as S
from fiber_tools import K_h, specialize, roots_small, gcd, strip, audit
from sympy.polys.rings import ring
from collections import Counter

def run():
    projs,pp,r_u,r_d=S.pi()
    th,pf,pb,ee=pp
    out=Counter();dcount=0
    gs=[S.num(g) for g in S.gs]
    for f,pow in projs:
        if f.total_degree()==60:continue
        K,h=K_h(f)
        R,t=ring('d',K)
        dd=gcd(specialize(th,R,[h,None,K.zero,K.zero]),specialize(r_d,R,[h,None,K.zero,K.zero]))
        print('split h degree',f.total_degree(),'d raw degree',dd.degree(),flush=True)
        dd=strip(dd,[t,t-R(h),t+R(h)])
        for L,d,em in roots_small(dd):
            dcount+=1
            a=em(h)
            U,u=ring('u',L)
            uu=gcd(specialize(pf,U,[a,d,None,L.zero]),specialize(r_u,U,[a,d,None,L.zero]))
            assert uu
            assert dd.degree()==2
            print('split quartic u raw',uu.degree(),flush=True)
            uu=strip(uu,[specialize(g,U,[a,d,None,L.zero]) for g in gs if g.degrees()[3]==0])
            print('split quartic u guarded',uu.degree(),flush=True)
            for M,u,mm in roots_small(uu):
                a1,d1=mm(a),mm(d)
                V,v=ring('v',M)
                vv=gcd(specialize(pb,V,[a1,d1,u,None]),specialize(ee,V,[a1,d1,u,None]))
                print('v raw',vv.degree(),flush=True)
                vv=strip(vv,[specialize(g,V,[a1,d1,u,None]) for g in gs])
                print('split quartic v guarded',vv.degree(),flush=True)
                for N,v,emb in roots_small(vv):
                    s=audit(N,emb(a1),emb(d1),emb(u),v,'split')
                    print(s,flush=True);out[s]+=1
    print('split endpoint+trace+fourth census',out,flush=True)
    assert dcount==2 and not out
if __name__=='__main__':run()
