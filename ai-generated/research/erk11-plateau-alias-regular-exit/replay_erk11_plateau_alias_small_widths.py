"""Exact guard-only exits of the five small regular projection factors."""
from replay_erk11_plateau_alias_paid_pair import *
import json
from pathlib import Path
P=flint.fmpq_poly
from itertools import combinations

def exactfield(H):
    H=H/H[H.degree()]
    unit=P([1]);zero=P();av=P([0,1])
    def trim(w):
        while w and w[-1].is_zero():w.pop()
        return w
    def inv(x):
        s,t=x,H;u,v=unit,zero
        while t:
            q,r=divmod(s,t);s,t=t,r;u,v=v,(u-q*v)%H
        assert s.degree()==0 and s[0]!=0
        return (u/s[0])%H
    def monic(g):
        if not g:return g
        v=inv(g[-1]);return [(t*v)%H for t in g]
    def rem(f,g):
        f=f[:];w=inv(g[-1])
        while len(f)>=len(g):
            s=len(f)-len(g);c=(f[-1]*w)%H
            for i in range(len(g)-1):f[i+s]=(f[i+s]-c*g[i])%H
            f.pop();trim(f)
        return f
    def quotient(f,g):
        f=f[:];q=[zero]*(len(f)-len(g)+1);w=inv(g[-1])
        while len(f)>=len(g):
            j=len(f)-len(g);c=(f[-1]*w)%H;q[j]=c
            for i in range(len(g)-1):f[i+j]=(f[i+j]-c*g[i])%H
            f.pop();trim(f)
        assert not f
        return trim(q)
    def gcd(f,g):
        while g:f,g=g,rem(f,g)
        return monic(f)
    def at(f):
        B=f.to_dict();ad,bd=f.degrees()
        return trim([P([B.get((i,j),0) for i in range(ad+1)])%H for j in range(bd+1)])
    def linear(g):
        assert len(g)==2 and g[1]==unit
        return -g[0]
    def spec(f,dv):
        r=zero
        for t in reversed(at(f)):r=(r*dv+t)%H
        return r
    return at,gcd,inv,linear,spec,quotient

def unit_lift(H,D,Pmark):
    for prime in (17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107):
        C=flint.fmpz_mod_poly_ctx(prime)
        r=lambda c:int(c.numerator)*pow(int(c.denominator),-1,prime)%prime
        try:
            hm=C([r(c) for c in H.coeffs()])
            if hm.degree()!=H.degree() or hm.gcd(hm.derivative()).degree()!=0:continue
            for f,_ in hm.factor()[1]:
                K=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD')
                B=flint.fq_default_poly_ctx(K);u=K.gen()
                def ev(pp):
                    return B([sum((K(r(c))*u**j for j,c in enumerate(q.coeffs())),K.zero()) for q in pp])
                e,f0=ev(D),ev(Pmark)
                if e.degree()==len(D)-1 and e.gcd(f0).degree()==0:
                    return prime,f.degree()
        except (ValueError,ZeroDivisionError):continue
    raise AssertionError('live residue absent')

def verify(path):
    D,G,L,Z,b=build('d')
    guard_raw=[b[2][0]*b[-1][2],b[3][0]*b[-1][3],L['dt'],Z['dt'],L['G'][1],Z['G'][1]]
    guard=list(map(geometry,guard_raw))
    masks={(3,3):('width d=1',dd-1),(8,8):('left affine pivot',guard[4]),
           (12,6):('left initial slope',guard[0]),(12,7):('right initial slope',guard[1])}
    fc=json.loads(path.read_text())
    assert sorted((len(q)-1,n) for q,n in fc)==[(1,16),(3,3),(8,8),(12,6),(12,7),(815,1)]
    for hp,n in sorted(fc,key=lambda q:(len(q[0]),q[1])):
        H=P(list(map(flint.fmpq,hp)))
        if H.degree()==815:continue
        if H.degree()==1:
            assert H[0]==0
            print('degree-1 factor fixes a=0, forbidden.',flush=True)
            continue
        name,mask=masks[(H.degree(),n)]
        at,gcd,inv,line,spec,quo=exactfield(H)
        d0=gcd(at(D),at(mask))
        # Take the portion that also meets the true independent mark.
        d0=gcd(d0,at(G))
        assert len(d0)==2
        dv=line(d0)
        assert all(spec(f,dv).is_zero() for f in (D,G,mask))
        a1,b1=quo(at(D),d0),quo(at(G),d0)
        pm,df=unit_lift(H,a1,b1)
        print('width factor',H.degree(),'multiplicity',n,': exactly masked d root',name,
              '; remaining quotient gcd 1 at',pm,'component degree',df,flush=True)
    print('All smaller regular width factors are forbidden or accounted for by a named exceptional mask.',flush=True)

if __name__=='__main__':
    import sys
    verify(Path(sys.argv[1]))
