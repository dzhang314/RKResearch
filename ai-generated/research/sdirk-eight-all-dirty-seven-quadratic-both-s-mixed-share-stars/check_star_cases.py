"""Exact five star-containing mixed charts and two fixed number-field fibres."""
from projective_share import regular_projection
from field_fibres import field,spec,gcd,trim
from sympy.polys.rings import ring
from sympy import isprime
from flint import nmod_poly as NP
PROFILE={
 'SS':([(2,2)],[168,294,138,249]),
 'SA2':([],[375,636,407,684]),
 'SA3':([(12,4)],[393,663,353,603]),
 'A1S':([],[408,685,274,484]),
 'A2S':([],[350,596,284,497])}
def sp(P,prime,u,keep=1):
    ds=P.degrees()
    q=[0]*(ds[keep]+1)
    others=1-keep
    x=[pow(u,i,prime) for i in range(ds[others]+1)]
    for ix,a in P.to_dict().items():q[ix[keep]]+=int(a)*x[ix[others]]
    return NP(q,prime)
def reduce(P,p,u):
    cs=[]
    for i in range(P.degree()+1):
        a=P.get((i,),P.ring.domain.zero)
        co=a.to_list() if hasattr(a,'to_list') else [a]
        z=0
        for m in co:
            assert int(m.denominator)%p
            z=(z*u+int(m.numerator)*pow(int(m.denominator),-1,p))%p
        cs.append(z)
    return NP(cs,p)
def run(modes):
    count=0
    for mode in modes:
        factors,rows,masks,degrees=regular_projection(mode)
        assert degrees==PROFILE[mode][1]
        assert [(q.total_degree(),n) for q,n in factors]==PROFILE[mode][0]
        for q,n in factors:
            _,K,u=field(q);R,v=ring('v',K)
            f=lambda a:spec(a,R,u)
            E=f(rows[0]).monic()
            if mode=='SS':
                assert E
                G=E
                for P in rows[1:]:G=gcd(G,f(P)%E)
                assert G.degree()==1 and trim(G,f(masks['clocks'][10]))==R.one
            else:
                assert mode=='SA3' and E.degree()==17
                E=trim(E,f(masks['rear_taps'][4]))
                assert E.degree()==15
                p,h=37,14
                assert isprime(p)
                M=sp(q,p,0,0)
                assert M.degree()==12 and not M(h) and M.derivative()(h)
                red=reduce(E,p,h)
                assert red.degree()==15 and red.leading_coefficient()==1
                for P in rows[1:]:red=red.gcd(sp(P,p,h))
                assert red.degree()==0
            count+=1
            print(mode,'verified all roots of exact factor degree',q.total_degree(),flush=True)
    print('star-containing mixed one-shared cases verified',len(modes),'fibres',count,flush=True)
if __name__=='__main__':
    from sys import argv
    run(argv[1:] or list(PROFILE))
