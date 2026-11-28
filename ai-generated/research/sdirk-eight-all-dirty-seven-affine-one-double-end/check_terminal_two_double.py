"""Exact reverse chronology on S,D,D opposite a doubled endpoint."""
from itertools import permutations,combinations
from reconstruct_terminal_two_double import candidates
from exact_scalars import kap,hub,num
from sympy.polys.rings import ring

def egcd(a,b):
    while b:
        a,b=b,a%b
    return a.monic()

def phase(F,u,mode):
    if not u or not kap(u):return None
    if mode=='A':
        if 3*u==2*F.one:return None
        assert hub(u)
        q=num(u)/hub(u)
        return (1+2*u,q/2) if q else None
    if u in (F.one,2*F.one):return None
    return 3-u,kap(u)/2

def affine_two(rows,F):
    for (a,b,c),(d,e,f) in combinations(rows,2):
        det=a*e-b*d
        if det:
            B,t=(c*e-b*f)/det,(a*f-c*d)/det
            if not B or any(g*B+h*t!=i for g,h,i in rows):
                return None
            return (B,t)
    row=next(((a,b,c) for a,b,c in rows if a or b),None)
    if row is None:
        return None if any(c for a,b,c in rows) else 'free'
    a,b,c=row
    if any((a*i!=g*c if a else b*i!=h*c) for g,h,i in rows):
        return None
    if not b and not c:return None # fixes B=0
    return 'rank one'

def check_all():
 meshes=list(candidates())
 assert len(meshes)==6
 for mode,deg,F,ell,a,b,s,D,x2,x3,g2,g3 in meshes:
    RR,V=ring('v',F)
    x0=1-a
    xe=ell-1
    L=lambda x:((2*x-ell)**4*35-(2*x-ell)**2*(30*ell**2)+3*ell**4)/560
    R=lambda x:(x-1+a)*(F.one/(2*a))
    r0=F.one/2
    assert D[0]==xe and R(x0)==F.zero and L(x0)
    Dother=D[1:]
    assert all(L(d) for d in D)
    assert R(F.one)==F.one/2
    A2anc=g2*(g2-R(x2))
    assert A2anc
    # First and reverse second/third singleton case, with arithmetic
    # enforced by the nonconstant graph.
    phasepol=num(V)*(V+b)-kap(V)*hub(V)*(2*V+b)
    Y=[RR.one,-V+xe,-2*V+xe]
    guards=[V,kap(V),hub(V),num(V),3*V-2]+[R(y) for y in Y]+[Y[i]-Y[j] for i in range(3) for j in range(i+1,3)]
    guards+=[y-d for d in D for y in Y[1:]]
    assert all(guards)
    phasepol=phasepol.monic()
    for d in guards:
        while (ff:=egcd(phasepol,d)).degree()>0:phasepol=phasepol.exquo(ff)
    d_i=[]
    for i,y in enumerate(Y):
        guard=R(y)
        for j,zz in enumerate(Y):
            if i!=j:guard*=y-zz
        d_i.append(guard%phasepol)
    den=(d_i[0]*d_i[1]*d_i[2])%phasepol
    def cnum(x):
        ans=RR.zero
        for i,y in enumerate(Y):
            f=L(y)
            for j,zz in enumerate(Y):
                if i!=j:f=(f*(RR(x)-zz)*d_i[j])%phasepol
            ans=(ans+f)%phasepol
        return ans
    bnum=(den*L(x2)-cnum(x2)*g2)%phasepol
    gna=-V-b
    gde=kap(V)*(2*a)
    ex1=((den*L(x3)-cnum(x3)*g3)*A2anc-bnum*(g3*(g3-R(x3))))%phasepol
    ex2=(den*gde**2*(L(xe)*A2anc)-cnum(xe)*gna*gde*A2anc-bnum*gna*(gna-gde*R(xe)))%phasepol
    gcd_SS=egcd(egcd(phasepol,ex1),ex2)
    print(mode,deg,'reverse S,S gcd',gcd_SS.degree(),flush=True)
    assert gcd_SS.degree()==0

    # All mixed reverse cases. The forward double values and reverse
    # pair equations are genuinely affine in B and the one extra C tap.
    mixed=[]
    def mixed_fit(s_x,s_g,rev_d):
        if s_x==F.one or s_x in D or not R(s_x):return 'guard'
        lam=R(s_x)/s_g
        assert lam
        dr=[(x,g*lam) for x,g in rev_d]
        if any(g==R(x) for x,g in dr):return 'guard'
        fr=[(x2,g2),(x3,g3)]
        if any(x==y and g==w for x,g in dr for y,w in fr):return 'guard'
        L0,L1=L(F.one)/R(F.one),L(s_x)/R(s_x)
        slope=(L1-L0)/(s_x-1)
        C0=lambda x:(x-1)*slope+L0
        T=lambda x:(x-1)*(x-s_x)
        rows=[(g*(g-R(x)),g*T(x),L(x)-g*C0(x)) for x,g in fr+dr]
        return 'excluded' if affine_two(rows,F) is None else 'survive'

    for y in Dother:
      xrev=ell-y
      for typ in ('A','S'):
        # Reverse D,S.
        vf=xrev-1
        fp=phase(F,vf,typ)
        if fp is not None:
            xr3,q=fp
            mixed.append(('D,S',mixed_fit(ell-xr3,q,[(xe,r0),(y,kap(vf)/2)])))
        # Reverse S,D.
        vr=(xrev-1)/2 if typ=='A' else 3-xrev
        fr=phase(F,vr,typ)
        if fr is not None:
            xr3,q=fr
            assert xr3==xrev
            mixed.append(('S,D',mixed_fit(xe-vr,kap(vr)/2,[(xe,r0),(y,q)])))

    for d2,d3 in permutations(Dother,2):
      xr2,xr3=ell-d2,ell-d3
      vr=xr2-1
      for typ in ('A','S'):
        ph=phase(F,vr,typ)
        if ph is None or ph[0]!=xr3:continue
        raise AssertionError('a literal reverse D,D phase survived')
    print(mode,deg,'mixed fits',mixed,'no D,D phase',flush=True)
    assert len(mixed)==8 and all(y=='excluded' for x,y in mixed)
 print('verified both singleton/doubled physical endpoints are impossible in the affine graph')

if __name__=='__main__':
    check_all()
