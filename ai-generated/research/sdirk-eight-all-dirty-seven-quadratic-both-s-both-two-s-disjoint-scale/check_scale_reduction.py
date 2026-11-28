"""Exact det of the two paid scale lines with S offsets as coordinates."""
import sympy as S
from sympy.polys.rings import ring
H,a,b=S.symbols('H a b');m=1+H/2
D=lambda x:-2+x+4*x*x-x**3
N=lambda x:(1+4*x-4*x*x)*D(x)+4*x*x*(3*x-2)
k=lambda x:1+2*x-x*x
L=lambda x:35*(x-H/2)**4-30*m*m*(x-H/2)**2+3*m**4
T=H-a-b
def determinant(phase):
    F=k(a) if phase=='LL' else N(a/2)/D(a/2)
    G=N(b/2)/D(b/2) if phase=='HH' else k(b)
    n=S.cancel(a+b-2*H-H*(F-1)*(H-b)/a)
    v=S.cancel(a+b-2*H-H*(G-1)*(H-a)/b)
    U=H*(H-b)*L(a)-(H-a)*T*L(0)*F
    V=H*(H-a)*L(b)-(H-b)*T*L(0)*G
    q=b*n*G*U-a*v*F*V
    dd=S.cancel(q)
    W=H*a*b*(H-a)*(H-b)*(H-a-b)
    if phase!='HL':W*=a-b
    co=S.cancel(dd/W)
    w,dd=S.fraction(co)
    return S.Poly(w,H,a,b,domain=S.QQ).primitive()[1],dd

def gcd(a,b):
    while b:
        r=a%b
        a,b=b,(r.monic() if r else r)
    return a.monic() if a else a
def trim(f,G):
    for h in G:
        if not h:return f.ring.one
        while (d:=gcd(f,h)).degree()>0:f=f.exquo(d).monic()
    return f
def branch(ph):
    F,den=determinant(ph)
    cc=[v for v in S.Poly(F.as_expr(),b).all_coeffs() if v]
    C0=min(cc,key=lambda x:S.degree(x,a))
    pp=[S.resultant(C0,c,a) for c in cc if c!=C0]
    pp=[p for p in pp if p]
    ds=[S.degree(p,H) for p in pp]
    assert ds==([60,60] if ph=='HL' else [56]*7)
    zz=S.Poly(pp[0],H,domain=S.QQ)
    for p in pp[1:]:zz=zz.gcd(S.Poly(p,H,domain=S.QQ))
    fs=zz.factor_list()[1]
    assert [(q.degree(),m) for q,m in fs]==[(4,3),(8,1),(12,1)]
    for q,m in fs:
        if q.degree()==1:
            K=S.QQ
            hh=K.convert(-q.nth(0)/q.nth(1))
        else:
            K=S.QQ.algebraic_field((q,H));hh=K.unit
        R,w=ring('a',K)
        def val(c):
            P=S.Poly(c,H,a,domain=S.QQ)
            cs={}
            for (i,j),g in P.terms():cs[(j,)]=cs.get((j,),K.zero)+K.convert(g)*hh**int(i)
            return R.from_dict({ij:z for ij,z in cs.items() if z})
        gam=[val(c) for c in cc]
        E=R.zero
        for g in gam:E=gcd(E,g)
        assert E.degree()==(3 if q.degree()==4 else 1)
        name='D' if q.degree()==4 else 'N'
        mask=val(D(a/2) if name=='D' else N(a/2))
        assert mask and trim(E,[mask])==R.one
        print(ph,'H-degree',q.degree(),'exact all-degree-drop fibre rejected by',name,flush=True)

def main():
    P=2*H**4-4*H**3-72*H**2+104*H-128
    Q=-5*H**4+20*H**3+60*H**2+120*H-40
    assert S.gcd(P,Q)==1
    X=(a-2)*H*(H-b)-2*H+a+b
    Y=(b-2)*H*(H-a)-2*H+a+b
    assert S.expand(X-Y-(a-b)*H*(H-2))==0
    mm,nn=P*a+Q,(2-a)*Q-P
    assert S.expand(mm**2+2*mm*nn-nn**2-(Q**2-P*(P-2*Q))*k(a))==0
    for ph,ds in [('LL',(4,1,1)),('HL',(4,8,2)),('HH',(4,7,7))]:
        W,den=determinant(ph)
        assert tuple(W.degree(x) for x in (H,a,b))==ds
        dd=S.Poly(den,H,a,b,domain=S.QQ)
        for g in [D(a/2),D(b/2)]:
            P0=S.Poly(g,H,a,b,domain=S.QQ)
            while (z:=dd.gcd(P0)).total_degree()>0:dd=dd.exquo(z)
        assert dd.total_degree()==0
        if ph=='LL':
            Z=S.Poly(P*a*b+Q*(a+b)+P-2*Q,H,a,b,domain=S.QQ)
            assert W.monic()==Z.monic()
        if ph in ('LL','HH'):
            assert S.expand(W.as_expr()-W.as_expr().xreplace({a:b,b:a}))==0
        if ph!='LL':branch(ph)
        print(ph,'exact primitive degrees',ds,flush=True)
    print('complete nonzero partner polynomial reduction in all law pairs',flush=True)
if __name__=='__main__':main()
