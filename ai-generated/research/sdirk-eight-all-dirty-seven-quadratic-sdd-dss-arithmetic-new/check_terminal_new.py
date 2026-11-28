"""Exact small-field certificate and fixed, collision-safe Hensel places."""
import sympy as S
from sympy.polys.rings import ring
from flint import fmpq_poly,nmod_poly as NP
from math import isqrt
from projection import C,project

def K_h(f):
    x=S.Symbol('H')
    p=S.Poly.from_dict({(int(ix[0]),):int(c) for ix,c in f.to_dict().items()},x,domain=S.QQ)
    assert p.is_irreducible
    if p.degree()==1:return S.QQ,S.QQ.convert(-p.nth(0)/p.nth(1))
    K=S.QQ.algebraic_field((p,x))
    return K,K.unit

def gcd(p,q):
    while q:p,q=q,p%q
    return p.monic() if p else p

def strip(p,gs):
    for g in gs:
        while p and (d:=gcd(p,g)).degree()>0:p=p.exquo(d)
    return p

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

def collpoly(R,j):
    m=R.degrees()[2];res={}
    for (a,b,c),d in R.to_dict().items():
        z=(int(a+c),int(b),0)
        res[z]=res.get(z,0)+int(d)*j**int(m-c)
    return C.from_dict({i:a for i,a in res.items() if a})
def reduce_G(G,p,x):
    out=[]
    for i in range(G.degree()+1):
        a=G.get((i,),G.ring.domain.zero)
        if not a:
            out.append(0);continue
        v=0
        for c in a.to_list():
            v=(v*x+int(c.numerator)*pow(int(c.denominator),-1,p))%p
        out.append(v)
    return NP(out,p)
def cert(hf,rows,uvs,G,j,p,x):
    E,R,X,Y=rows
    f=specialize(hf,p,[0,0,0],0)
    if f.degree()!=hf.total_degree() or f(x) or not f.derivative()(x):return None
    c=specialize(E,p,[x,0,0],1)
    if c.degree()!=E.degrees()[1]:return None
    U=c.gcd(specialize(uvs[0],p,[x,0,0],1)).gcd(specialize(uvs[1],p,[x,0,0],1))
    ur=U.roots()
    if sum(a for _,a in ur)!=U.degree():return None
    try:gg=reduce_G(G,p,x)
    except ValueError:return None
    vv0=x*pow(j,-1,p)%p
    out=[]
    for u0,ex in ur:
        u0=int(u0)
        a=c.derivative()(u0);b=gg.derivative()(u0)
        if gg(u0) or not a or not b:return None
        vv=[specialize(w,p,[x,u0,0],2) for w in (R,X,Y)]
        if not any(a.degree()==w.degrees()[2] and a.degree()>0 for a,w in zip(vv,(R,X,Y))):return None
        V=vv[0].gcd(vv[1]).gcd(vv[2])
        if not V:return None
        vr=V.roots()
        if sum(e for _,e in vr)!=V.degree():return None
        if any(int(y)!=vv0 for y,e in vr):return None
        dd=vv[0].derivative()(vv0)
        if vr and not dd:return None
        out.append((u0,int(a),int(b),vv0,int(dd),V.degree()))
    return sorted(out)

SMALL={
 ('A',4,2):1,('A',4,9):1,('A',2,36):0,
 ('S',1,9):2,('S',4,9):2,('S',2,38):0,
}
LARGE={
 ('A',36):(2,1,13,10,[(4,10,1,5,1,1)]),
 ('A',42):(1,1,19,4,[(12,8,1,4,2,1)]),
 ('S',18):(2,2,29,12,[(8,28,14,6,7,1),(23,1,15,6,1,1)]),
 ('S',21):(1,2,59,45,[(5,49,8,45,26,1),(56,10,51,45,5,1)]),
}
def run():
    seen_small=set();seen_large=set()
    for fm,ff,rows,gs,uvs in project():
        E,R,A,B=rows
        for hf,n in ff:
            d=hf.total_degree()
            K,H=K_h(hf);U,u=ring('u',K)
            if d<=4:
                tag=fm,d,n
                assert tag not in seen_small
                seen_small.add(tag)
                t=lambda fl:spH(fl,U,H)
                e=t(E);a=t(uvs[0]);b=t(uvs[1])
                if e:
                    e=e.monic();a%=e;b%=e
                M=gcd(gcd(e,a),b)
                assert M and M.degree()==SMALL[tag]
                Q=strip(M,[t(z) for z in gs if not z.degrees()[2]])
                assert Q.degree()==0
                print('small exact',tag,'raw/guarded u degrees',M.degree(),Q.degree(),flush=True)
            else:
                tag=fm,d
                assert tag not in seen_large
                seen_large.add(tag)
                j,k,p,x,expect=LARGE[tag]
                assert p>7 and all(p%r for r in range(2,1+isqrt(p)))
                G=gcd(spH(E,U,H),spH(collpoly(R,j),U,H))
                assert G and G.degree()==k
                q=cert(hf,rows,uvs,G,j,p,x)
                assert q==expect,q
                print('exact Hensel collision',tag,'v=H/'+str(j),'at',p,x,q,flush=True)
    assert seen_small==set(SMALL) and seen_large==set(LARGE)
    print('terminal-new arithmetic: all ten projected factors excluded')
if __name__=='__main__':run()
