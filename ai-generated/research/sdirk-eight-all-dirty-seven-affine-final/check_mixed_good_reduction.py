"""Exact local obstruction at one good reduction of each irreducible mesh norm."""
from itertools import permutations
from mixed_sdd_norm import resultants
from exact_scalars import kk,l3,l4,kap,hub,num,den
import sympy as S

class Bad(Exception):pass

def mixed_phi(p,sm,roots,mf,mr,j):
    a,b,c=roots
    e=(b-2*a if mf=='A' else (2-a-b)*pow(4,-1,p))%p
    w=(e-roots[j])%p
    d=(1-e)%p
    z=(sm-e)%p
    ph=z*(w-4*d)+2*d*d if mr=='A' else z*w-d*d if mr=='S' else \
        2*z*(w-2*d)*(w**3-3*w*w*d+d**3)-d*d*(-2*d**3+w*d*d+4*w*w*d-w**3)
    return e,ph%p

def fields(p,sm,roots,e,mf,mr,j):
    def z(x):return x%p
    def I(x):
        if not z(x):raise Bad()
        return pow(z(x),-1,p)
    A=z(-(e+sm)*I(1-e));B=z((sm-e)*I(1-e))
    ell=z(2*I(1-e))
    if not z(e*A*B) or not z(kk(e,sm,1)*kk(-e,sm,1)):raise Bad()
    lam=z(-B*I(A))
    LP=lambda x:z(ell*(1+x)*I(2))
    R=lambda x:z((x-1+A)*I(2*A))
    L=lambda x:z(l4(z(2*x-ell),ell)*I(560))
    def q(u,mode):
        if not z(u*kap(u)):raise Bad()
        if mode=='A':
            if not z((3*u-2)*hub(u)*num(u)):raise Bad()
            return z(num(u)*I(hub(u)))
        if not z((u-1)*(u-2)):raise Bad()
        return z(kap(u))
    alpha,beta,_=roots
    xf1,xf2=LP(alpha),LP(beta)
    u=z(xf1-1)
    qf=q(u,mf)
    assert xf2==z(1+2*u if mf=='A' else 3-u)
    g1,g2=z(kap(u)*I(2)),z(qf*I(2))
    xrD=LP(-roots[j])
    if mr!='T':
        ur=z(2-I(B)); qr=q(ur,mr)
        xrS=z(1+ur)
        assert xrD==z(1+2*ur if mr=='A' else 3-ur)
        gr=z(qr*I(2))
    else:
        ur=z(xrD-1);qr=q(ur,'A')
        if not z(den(ur)):raise Bad()
        assert z(B*den(ur)-hub(ur))==0
        xrS=z(1+2*ur)
        gr=z(kap(ur)*I(2))
    ss=[1,z(ell-1),z(ell-xrS)]
    if len(set(ss))!=3 or any(x in map(LP,roots) for x in ss):raise Bad()
    assert R(ss[0])==I(2) and R(ss[1])==z(lam*I(2))
    assert R(ss[2])==z(lam*(kap(ur) if mr!='T' else qr)*I(2))
    vals=[z(L(x)*I(R(x))) for x in ss]
    def C(x):
        cs=0
        for i,t in enumerate(ss):
            c=vals[i]
            for k,w in enumerate(ss):
                if i!=k:c=z(c*(x-w)*I(t-w))
            cs+=c
        return z(cs)
    bb=z((L(xf1)-g1*C(xf1))*I(g1*(g1-R(xf1))))
    def U(x,g):return z(L(x)-g*C(x)-bb*g*(g-R(x)))
    # B=0 modulo p is not an allowed reason to reject.
    return U(xf2,g2),U(z(ell-xrD),z(lam*gr))

def audit(f,p,sm,mf,mr,j):
    zz,fp=f.clear_denoms()
    poly=[int(a)%p for a in fp.all_coeffs()]
    if not poly[0] or not (l3(sm,1)*l4(sm,1))%p:return None
    def Horner(c,x):
        z=0
        for v in c:z=(z*x+v)%p
        return z
    if Horner(poly,sm) or not Horner([c*(len(poly)-1-i)%p for i,c in enumerate(poly[:-1])],sm):
        return None
    zs=[k for k in range(p) if kk(k,sm,1)%p==0]
    if len(zs)!=3:return None
    goods=[]
    for roots in permutations(zs):
        e,phi=mixed_phi(p,sm,roots,mf,mr,j)
        if phi:continue
        try:
            a,b=fields(p,sm,roots,e,mf,mr,j)
        except Bad:return None
        if not(a or b):return None
        goods.append((roots,a,b))
    return goods if goods else None

LEDGER={
 ('A','A',0):(30,1,41,8, [((29,37,15),26,27)]),
 ('A','A',1):(30,1,31,29,[((11,14,12),29,5)]),
 ('A','A',2):(36,1,41,8, [((29,15,37),14,2)]),
 ('A','S',0):(30,1,13,11,[((11,3,4),2,1)]),
 ('A','S',1):(28,1,13,11,[((3,11,4),7,10)]),
 ('A','S',2):(36,1,13,2, [((2,10,9),1,1)]),
 ('A','T',0):(66,1,29,13,[((13,9,19),7,12)]),
 ('A','T',1):(66,1,31,11,[((12,29,14),16,11)]),
 ('A','T',2):(90,1,29,16,[((16,10,20),1,24)]),
 ('S','A',0):(30,1,29,16,[((10,16,20),1,10)]),
 ('S','A',1):(30,1,29,16,[((16,10,20),5,18)]),
 ('S','A',2):(18,2,41,12,[((4,33,26),27,37),((33,4,26),30,28)]),
 ('S','S',0):(30,1,41,26,[((4,33,12),24,8)]),
 ('S','S',1):(30,1,37,10,[((10,31,21),27,27)]),
 ('S','S',2):(18,2,37,27,[((6,27,16),7,8),((27,6,16),10,14)]),
 ('S','T',0):(66,1,53,8, [((16,11,5),3,18)]),
 ('S','T',1):(66,1,53,8, [((11,16,5),47,47)]),
 ('S','T',2):(45,2,59,5, [((39,41,44),9,42),((41,39,44),52,52)]),
}

if __name__=='__main__':
    found=set()
    for mf,mr,j,phi,n,fc in resultants():
        tag=(mf,mr,j)
        assert tag not in found
        found.add(tag)
        deg,m0,p,x,expected=LEDGER[tag]
        assert 7<p<60 and all(p%d for d in range(2,1+int(p**0.5)))
        assert len(fc)==1
        f,m=fc[0]
        assert f.degree()==deg and m==m0 and f.is_irreducible
        ans=audit(f,p,x,mf,mr,j)
        assert ans==expected
        print('fixed certificate',mf,mr,j,p,x,ans,flush=True)
    assert found==set(LEDGER) and len(found)==18
    print('verified every mixed ordered-root affine chart')
