"""Exhaust the even mesh, equal and unequal true arithmetic gaps."""
import even_projection as E
from fiber_tools import K_h, specialize, roots_small, gcd, strip, audit
from sympy.polys.rings import ring
from collections import Counter
from itertools import combinations
from scalar_geometry import D,k,N

def run():
    hit=Counter()
    proj,pp,gs,hs=E.equal()
    gg=[E.num(x) for x in gs]
    for f,e in proj.factor()[1]:
        K,h=K_h(f)
        R,t=ring('u',K)
        g=gcd(*(specialize(p,R,[h,None]) for p in pp))
        print('equal',f.total_degree(),'raw gcd',g.degree(),flush=True)
        g=strip(g,[specialize(j,R,[h,None]) for j in gg])
        print('equal',f.total_degree(),'guarded gcd',g.degree(),flush=True)
        for L,u,em in roots_small(g):
            y=audit(L,em(h),L.zero,u,u,'even')
            hit[y]+=1
            print(y,flush=True)
    assert hit=={'fourth rejects':1},hit
    p,pp,e2=E.distinct()
    other=Counter()
    for f,e in p.factor()[1]:
        K,h=K_h(f)
        R,t=ring('z',K)
        g=gcd(*(specialize(x,R,[h,None]) for x in pp))
        print('unequal',f.total_degree(),'sum degree',g.degree(),flush=True)
        for L,al,em in roots_small(g):
            h1=em(h)
            m=h1+1
            s=(21*m*m*h1*h1-15*m**4)/(35*h1*h1-21*m*m)
            be=(3*s-3*h1*h1+4*h1*al)/6
            Y,y=ring('u',L)
            yp=y*y-Y(al)*y+Y(be)
            z=Y(al)-y
            ss=[y-Y(h1),2*y-Y(h1),Y(h1)-z,Y(h1)-2*z,Y(-h1),Y(h1),Y.zero]
            guard=[a-b for (a,b) in combinations(ss,2)]
            guard+=[y-z,y,z,k(y),k(z),D(y),D(z),N(y),N(z),3*y-2,3*z-2]
            guard+=[x*x-Y(s) for x in ss[:4]]
            yq=strip(yp,guard)
            print('unequal pair poly',yp.degree(),'guarded',yq.degree(),flush=True)
            if not yq.degree():other['guarded pair empty']+=1
            for M,u,mm in roots_small(yq):
                v=mm(al)-u
                assert u!=v
                out=audit(M,mm(h1),M.zero,u,v,'even')
                other[out]+=1
                print(out,flush=True)
    print('unequal endpoint+trace+fourth census',other,flush=True)
    assert other=={'guarded pair empty':2},other
if __name__=='__main__':run()
