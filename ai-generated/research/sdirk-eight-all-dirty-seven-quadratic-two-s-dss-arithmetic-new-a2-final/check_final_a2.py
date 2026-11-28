"""All twelve A2 swapped factors: eight direct places and four exact guard trims."""
from ingress import C,ingress
from primitive_projection import exact_projection
from flint import fmpq_poly,nmod_poly as NP
from sympy.polys.rings import ring
from math import isqrt
import sympy as S

def gcd_mon(a,b):
    while b:
        c=a%b
        a,b=b,(c.monic() if c else c)
    return a.monic() if a else a

def guarded(p,gs):
    for G in gs:
        while p:
            z=gcd_mon(p,G)
            if z.degree()==0:break
            p=p.exquo(z).monic()
    return p
def specialize_D(f,hR):
    K=hR.domain
    mod=fmpq_poly(list(reversed(K.mod.to_list())))
    cs={}
    for (i,j,k),a in f.to_dict().items():
        assert not k
        c=cs.setdefault(int(i),{})
        c[int(j)]=int(a)
    dt={}
    for i,c in cs.items():
        p=[0]*(max(c)+1)
        for j,a in c.items():p[j]=a
        q=fmpq_poly(p)%mod
        if q:dt[(i,)]=K.new(list(reversed(q.coeffs())))
    return hR.from_dict(dt)
def specialize(f,p,vs,keep):
    d=f.degrees()
    vals=[None if i==keep else [pow(v,j,p) for j in range(d[i]+1)] for i,v in enumerate(vs)]
    c=[0]*(d[keep]+1)
    for ix,z in f.to_dict().items():
        a=int(z)%p
        for j in range(3):
            if j!=keep:a=(a*vals[j][ix[j]])%p
        c[ix[keep]]+=a
    return NP(c,p)

def reduce(P,p,h):
    coeff=[]
    for i in range(P.degree()+1):
        a=P.get((i,),P.ring.domain.zero)
        vv=0
        if a:
            lst=a.to_list() if hasattr(a,'to_list') else [a]
            for c in lst:
                vv=(vv*h+int(c.numerator)*pow(int(c.denominator),-1,p))%p
        coeff.append(vv)
    return NP(coeff,p)
def actual(E,fc):
    mod=fmpq_poly(fc);dd={}
    for (i,j,k),a in E.to_dict().items():
        assert not k
        r=dd.setdefault(int(i),{})
        r[int(j)]=int(a)
    for i,a in sorted(dd.items(),reverse=True):
        b=[0]*(1+max(a))
        for j,z in a.items():b[j]=z
        if fmpq_poly(b)%mod:return i
    return -1


DIRECT={
 (3,30):(13,3,18,[11]), (3,60):(17,4,15,[]),
 (8,3):(101,67,18,[11]), (16,3):(17,15,18,[3]),
 (24,3):(29,25,18,[22]), (48,3):(101,52,18,[47]),
 (134,1):(31,7,18,[17]), (356,1):(11,7,18,[4]),
}
STATIC={
 (1,192):(11,10,18,12,('scale',)),
 (4,1):(23,12,18,17,('first graph value',)),
 (8,16):(103,37,18,16,('terminal Legendre','front Legendre')),
 (36,8):(31,10,18,17,('anchor slope','paid affine slope')),
}

def place(f,p,x,n):
    assert p>7 and all(p%j for j in range(2,1+isqrt(p)))
    q=specialize(f,p,[0,0,0],1)
    assert q.degree()==n and not q(x) and q.derivative()(x)
def run():
    rows,gs,Q,named=ingress()
    ff=exact_projection(rows,gs,Q,named)
    E,*vrows=rows
    seen=set()
    for coeff,n in ff:
        i=len(coeff)-1;tag=i,n
        assert tag not in seen
        seen.add(tag)
        f=C.from_dict({(0,j,0):c for j,c in enumerate(coeff) if c})
        if tag in DIRECT:
            p,d,ex,hs=DIRECT[tag]
            place(f,p,d,i)
            e=specialize(E,p,[0,d,0],0)
            assert actual(E,coeff)==e.degree()==ex>0
            G=e.gcd(specialize(Q,p,[0,d,0],0))
            hh=G.roots()
            assert sum(n for _,n in hh)==G.degree()
            assert sorted(int(y) for y,n in hh)==hs
            for h,_ in hh:
                vv=[specialize(z,p,[int(h),d,0],2) for z in vrows]
                assert any(z.degree()==z0.degrees()[2] and z.degree()>0 for z,z0 in zip(vv,vrows))
                t=vv[0]
                for v in vv[1:]:t=t.gcd(v)
                assert t.degree()==0
            print('fixed direct d place',tag,p,d,ex,hs,flush=True)
        else:
            p,d,deg1,deg2,keys=STATIC[tag]
            place(f,p,d,i)
            x=S.Symbol('d')
            fp=S.Poly.from_dict({(j,):c for j,c in enumerate(coeff) if c},x,domain=S.QQ)
            assert fp.is_irreducible
            K=S.QQ.algebraic_field((fp,x));T,H=ring('H',K)
            et=specialize_D(E,T).monic()
            assert et and et.degree()==deg1
            gg=[specialize_D(named[key],T).monic() for key in keys]
            if i==36:
                assert len(gg)==2
                ss=gcd_mon(*gg)
                assert ss.degree()==1
                gg=[ss]
            q=guarded(et,gg)
            assert q.degree()==deg2
            t=reduce(q,p,d)
            assert t.degree()==deg2 and t.gcd(specialize(Q,p,[0,d,0],0)).degree()==0
            print('exact static guard trim',tag,p,d,deg1,deg2,keys,flush=True)
    assert seen==set(DIRECT)|set(STATIC)
    print('all twelve true A2 outer factors excluded',flush=True)
if __name__=='__main__':run()
