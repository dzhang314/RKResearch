"""Fixed exact Hensel places for the terminal-new front-A3 branch."""
import sympy as S
from sympy.polys.rings import ring
from flint import fmpq_poly,nmod_poly as NP
from math import isqrt
from projection import project

def gcd(a,b):
    while b:a,b=b,a%b
    return a.monic() if a else a
def strip(a,gg):
    for g in gg:
        while a and (q:=gcd(a,g)).degree()>0:a=a.exquo(q)
    return a

def K_h(f):
    X=S.Symbol('h')
    p=S.Poly.from_dict({(int(ix[0]),):int(c) for ix,c in f.to_dict().items()},X,domain=S.QQ)
    assert p.is_irreducible
    if p.degree()==1:return S.QQ,S.QQ.convert(-p.nth(0)/p.nth(1))
    K=S.QQ.algebraic_field((p,X))
    return K,K.unit
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

def spH(f,U,h):
    K=U.domain
    md=fmpq_poly(list(reversed(K.mod.to_list()))) if hasattr(K,'mod') else fmpq_poly([-h,1])
    tab={}
    for (i,j,k),a in f.to_dict().items():
        assert not k
        b=tab.setdefault(int(j),{})
        b[int(i)]=int(a)
    vals={}
    for j,cs in tab.items():
        row=[0]*(max(cs)+1)
        for i,a in cs.items():row[i]=a
        x=fmpq_poly(row)%md
        if x:
            if hasattr(K,'mod'):vals[(j,)]=K.new(list(reversed(x.coeffs())))
            else:vals[(j,)]=K.convert(x[0])
    return U.from_dict(vals)

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

DIRECT={
 (3,1):(11,4,[0]),(12,3):(17,5,[8]),(24,3):(101,15,[59]),
 (56,1):(11,0,[4]),(170,1):(11,2,[7]),
}
TRIM={
 (4,1):(11,7,9,8,()),
 (18,8):(23,15,9,8,('anchor slope','paid affine slope')),
 (18,16):(31,1,9,7,('front arithmetic numerator','front kappa')),
}
def place(hf,p,h):
    assert p>7 and all(p%j for j in range(2,1+isqrt(p)))
    bar=specialize(hf,p,[0,0,0],0)
    assert bar.degree()==hf.total_degree() and bar(h)==0 and bar.derivative()(h)

def run():
    visited=set()
    [(phase,ff,rows,guards,Q,dt)]=project()
    assert phase=='A3'
    E,*vrows=rows
    for hf,n in ff:
        tag=(hf.total_degree(),n)
        assert tag not in visited
        visited.add(tag)
        K,H=K_h(hf);U,_u=ring('d',K)
        local=spH(E,U,H)
        if tag in TRIM:
            p,h,a,b,sel=TRIM[tag]
            assert local and local.degree()==a
            gg=[dt[-1][z] for z in sel] if sel else [z for z in guards if not z.degrees()[2]]
            assert all(not z.degrees()[2] for z in gg)
            t=strip(local,[spH(z,U,H) for z in gg]).monic()
            assert t and t.degree()==b
            place(hf,p,h)
            tbar=reduce(t,p,h)
            qbar=specialize(Q,p,[h,0,0],1)
            assert tbar.degree()==b and tbar.gcd(qbar).degree()==0
            print('static guard certificate',tag,p,h,a,b,flush=True)
        else:
            p,h,ds=DIRECT[tag]
            place(hf,p,h)
            e=specialize(E,p,[h,0,0],1)
            assert e and e.degree()==local.degree()>0
            a=e.gcd(specialize(Q,p,[h,0,0],1))
            roots=a.roots()
            assert sum(k for _,k in roots)==a.degree()
            assert sorted(int(x) for x,k in roots)==ds
            for d,k in roots:
                rr=[specialize(f,p,[h,int(d),0],2) for f in vrows]
                assert any(z.degree()==f.degrees()[2] and z.degree()>0 for z,f in zip(rr,vrows))
                joint=rr[0]
                for z in rr[1:]:joint=joint.gcd(z)
                assert joint.degree()==0
            print('direct finite place',tag,p,h,ds,flush=True)
    assert visited==set(DIRECT)|set(TRIM)
    print('all terminal-new front-A3 arithmetic-rear factors excluded')
if __name__=='__main__':run()
