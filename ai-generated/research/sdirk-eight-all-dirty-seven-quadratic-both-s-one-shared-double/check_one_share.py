"""Exact physical charts and number-field gcds for the one-shared SDD/SDD proof."""
from projection_one import CASES,project,CZ
from sympy import QQ,Poly,Symbol,Rational
from sympy.polys.rings import ring
from flint import fmpq_poly

U=Symbol('u')
A4=U**4+36*U**3+66*U**2+36*U+6
A8=(3695*U**8+20700*U**7+41190*U**6+32580*U**5+1866*U**4
    -12312*U**3-7416*U**2-1728*U-144)
S4=35*U**4-140*U**3+90*U**2+100*U-37
S8=(5329*U**8-42632*U**7+120676*U**6-127208*U**5-7106*U**4
    +80680*U**3-17900*U**2-10040*U+505)
leg=(1,'legendre',0)
collision=(1,'clocks',10)
m2=(2,'clocks',0);m3=(3,'clocks',0);v3=(3,'rear_taps',0)
half=Rational(-1,2)
TABLE={
 'AS11':{4:(1,leg),8:(1,leg),-1:(12,m3),half:(12,m3)},
 'AS21':{4:(1,leg),8:(1,leg),-1:(12,v3),half:(12,m3)},
 'AA11':{4:(1,leg),8:(1,leg),-1:(8,m2),half:(12,m3)},
 'AA12':{4:(2,collision),8:(1,leg),-1:(12,m3),half:(12,m3)},
 'AA22':{4:(1,leg),8:(1,leg),-1:(12,v3),half:(8,m2)},
 'SS11':{4:(2,collision),8:(1,leg),-1:(8,m2),3:(12,m3)}}

def field(P):
    P0=Poly.from_dict({(int(i),):int(v) for (i,j),v in P.to_dict().items()},U,domain=QQ)
    assert P0.is_irreducible and P0.degree()==P.total_degree()
    if P0.degree()==1:return P0,QQ,QQ.convert(-P0.nth(0)/P0.nth(1))
    K=QQ.algebraic_field((P0,U))
    return P0,K,K.unit
def spec(P,R,u):
    K=R.domain
    h=fmpq_poly(list(reversed(K.mod.to_list()))) if hasattr(K,'mod') else fmpq_poly([-u,1])
    cs={}
    for (i,j),a in P.to_dict().items():cs.setdefault(int(j),{})[int(i)]=int(a)
    out={}
    for j,q in cs.items():
        coeff=[0]*(1+max(q))
        for i,c in q.items():coeff[i]=c
        rem=fmpq_poly(coeff)%h
        if rem:out[(j,)]=K.new(list(reversed(rem.coeffs()))) if hasattr(K,'mod') else K.convert(rem[0])
    return R.from_dict(out)
def gcd(a,b):
    while b:
        r=a%b
        a,b=b,(r.monic() if r else r)
    return a.monic() if a else a
def trim(a,mask):
    assert mask
    while (g:=gcd(a,mask)).degree()>0:a=a.exquo(g).monic()
    return a

def run(modes):
    count=0
    for mode in modes:
        ff,eq,G=project(mode)
        S=TABLE[mode];seen=set()
        for pr,n in ff:
            q,K,u=field(pr)
            d=q.degree()
            t=-q.nth(0)/q.nth(1) if d==1 else d
            if d>1:
                form=(S4 if d==4 else S8) if mode.startswith('SS') else (A4 if d==4 else A8)
                assert q.monic()==Poly(form,U,domain=QQ).monic()
            assert t not in seen;seen.add(t)
            n0,(d0,name,idx)=S[t]
            assert n0==n
            R,v=ring('v',K)
            f=lambda e:spec(e,R,u)
            E,X,Y=map(f,eq)
            if E:E=E.monic();X%=E;Y%=E
            g=gcd(gcd(E,X),Y)
            assert g.degree()==d0
            c=trim(g,f(G[name][idx]))
            assert c==R.one
            count+=1
            print(mode,'u factor',t,'gcd degree',d0,'removed by',name,idx,flush=True)
        assert seen==set(S)
    assert count==4*len(modes)
    print('one-shared exact SDD/SDD cases verified',len(modes),'fibres',count,flush=True)
if __name__=='__main__':
    from sys import argv
    run(argv[1:] or list(CASES))
