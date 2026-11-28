
"""Complete exact four-row forward/reverse fits on the finite five-double mesh census."""
import sympy as S
from sympy.polys.rings import ring
from itertools import permutations
from time import monotonic
M,U,V,W=S.symbols('m u j z')
QQ=S.QQ
def mpoly(coeffs,var):
    return S.Poly(coeffs,var).monic()
def kexpr(k, pol, at):
    return sum((k.convert(S.Rational(c))*at**i for i,c in enumerate(pol)),k.zero)
def hf(x):return -2+x+4*x*x-x**3
def ka(x):return 1+2*x-x*x
def qnu(x):return (1+4*x-4*x*x)*hf(x)+4*x*x*(3*x-2)
def fo(poly):
    return S.Poly(poly,M,domain=QQ).monic()
# In the five quartic diagonal fields, the indicated signed j is one
# of the meshes found from a literal opener; its negative is the same mesh.
modes=[
 ('A_h_j',8*M**4-56*M**3+112*M*M-84*M+21,3*(M-1)),
 ('A_j_0',2*M**4-14*M**3-21*M*M+28*M-7,-(M-1)/2),
 ('A_j_minusj',8*M**4-56*M**3+28*M-7,-(M-1)/3),
 ('S_h_j',120*M**4-1008*M**3+2744*M*M-2800*M+875,5-3*M),
 ('S_0_j',50*M**4-462*M**3+1463*M*M-1680*M+560,4-2*M),
]
# Check the parametrization of the candidate mesh exactly in each field.
def meshes():
    for label,cf,jf in modes:
        F=fo(cf); assert F.is_irreducible
        K=QQ.algebraic_field((F,M));m=K.unit
        j=kexpr(K,S.Poly(jf,M).all_coeffs()[::-1],m)
        yield label,K,m,m-1,j
    for la,m,rad in [('S_5_3',S.Rational(5,3),S.Rational(485,231)),
                     ('S_2',S.Rational(2),S.Rational(156,49))]:
        F=S.Poly(V**2-rad,V)
        assert F.is_irreducible
        K=QQ.algebraic_field((F,V)); j=K.unit; m=K.convert(m)
        yield la,K,m,m-1,j
    for la,form,lin in [
        ('half_A',U**4-S.Rational(3,4)*U**2+S.Rational(3,28),2*U),
        ('half_S',U**4-4*U**3+S.Rational(14,5)*U**2+S.Rational(12,5)*U-S.Rational(69,35),2-U)
    ]:
        F=S.Poly(form,U)
        assert F.is_irreducible
        K=QQ.algebraic_field((F,U)); u=K.unit
        jj=kexpr(K,S.Poly(lin,U).all_coeffs()[::-1],u)
        yield la,K,K.one,u,jj

# A simple primitive-element check for the degree-7 double-midpoint case.
def mid_mesh():
    F=fo(2*M**7-38*M**6+270*M**5-882*M**4+1365*M**3-985*M**2+315*M-35)
    assert F.is_irreducible
    E=QQ.algebraic_field((F,M));m=E.unit;b=m-1
    den=35*b*b-21*m*m
    assert den
    rad=(21*m*m*b*b-15*m**4)/den
    R,j=ring('j',E)
    fact=(j*j-rad).factor_list()[1]
    if len(fact)==2:
        pol=fact[0][0]; assert pol.degree()==1
        yield 'mid_AA',E,m,b,-pol.get((0,),E.zero)/pol.get((1,),E.one)
        return
    assert len(fact)==1 and fact[0][0].degree()==2
    eD=35*(M-1)**2-21*M**2
    eN=21*M**2*(M-1)**2-15*M**4
    G=S.Poly(S.resultant(F,eD*(W-M)**2-4*eN,M),W).monic()
    assert G.degree()==14 and G.is_irreducible
    mod=j*j-rad; primitive=R(m)+2*j
    def vec(p):
        return S.Matrix([
            S.Rational(str((p.get((i,),E.zero).to_list()[::-1]+[0]*7)[k]))
            for i in range(2) for k in range(7)
        ])
    C=S.Matrix.hstack(*(vec(primitive**i%mod) for i in range(14))).inv()
    mv,jv=C*vec(R(m)),C*vec(j)
    def ck(coeff):
        return sum((R(E.convert(c))*primitive**i%mod for i,c in enumerate(coeff)),R.zero)%mod
    assert ck(mv)==R(m) and ck(jv)==j and not ck(G.all_coeffs()[::-1])
    K=QQ.algebraic_field((G,W));w=K.unit
    m=kexpr(K,mv,w);j=kexpr(K,jv,w)
    assert m+2*j==w
    yield 'mid_AA',K,m,m-1,j

def read_case(label,K,m,h,j):
    c0,c1,c2=K.zero,K.one,K.convert(2)
    D=2*m
    assert m and h and j and h!=j and h!=-j
    assert not (15*m**4-21*m*m*(h*h+j*j)+35*h*h*j*j)
    XX=[m+x for x in [c0,h,-h,j,-j]]
    assert c1 in XX and D-c1 in XX
    R,T=ring('T',K)
    L4=lambda t:t**4-K.convert(S.Rational(6,7))*m*m*t*t+K.convert(S.Rational(3,35))*m**4
    assert all(L4(x-m) for x in XX)
    def val(p,t):
        return sum((c*t**i for (i,),c in p.items()),K.zero)
    def poly(xs,ys):
        P=R.zero
        for i,x in enumerate(xs):
            row=R.one
            for j0,y in enumerate(xs):
                if j0!=i:row*=((T-y)/R(x-y))
            P+=ys[i]*row
        assert all(val(P,x)==y for x,y in zip(xs,ys))
        return P
    def prim(P):
        return R.from_dict({(i+1,):v/K.convert(i+1) for (i,),v in P.items()})
    ff=[]; freeg=[]
    for a,b in permutations([y for y in XX if y!=c1],2):
        u=a-c1;k=ka(u)
        if not k:continue
        flags=[]
        if b==2*a-c1 and 3*u!=c2:
            hh=hf(u)
            assert hh
            q=qnu(u)/hh
            if q:flags.append(('A',q))
        if a+b==2*c2 and u!=c1 and u!=c2:
            flags.append(('S',k))
        for name,q in flags:
            ns=[c1,a,b];gs=[c1/c2,k/c2,q/c2]
            A0=poly([x-m for x in ns],[L4(x-m)/g for x,g in zip(ns,gs)])
            Pg=poly([x-m for x in ns],gs)
            T0=poly(ns,gs); J0=prim(T0)
            b0=T0.get((1,),c0); c00=T0.get((2,),c0)
            for s in XX:
                l=c1+(s-c1)/k
                delta=K.convert(S.Rational(4,3))+2*(k+c1)*(s-c1)/(3*k)
                den=c1-l+b0+c00*delta
                num=val(T0-J0,s)
                if not den:
                    if not num:
                        freeg.append((ns,s,name))
                        ff.append((name,ns+[s],gs+[None],A0,Pg,None))
                    continue
                g=num/den
                if not g or (s in ns and gs[ns.index(s)]==g):continue
                t=s-m
                dv=g-val(Pg,t); nv=L4(t)/g-val(A0,t)
                if not dv:
                    if not nv: ff.append((name,ns+[s],gs+[g],A0,Pg,None))
                    continue
                if not nv: continue # B=0
                B=nv/dv
                ff.append((name,ns+[s],gs+[g],A0,Pg,B))
    # Both free cases are retained as necessary fits, not specialized.
    expected={
        'A_h_j':4,'A_j_0':4,'A_j_minusj':4,'S_h_j':6,'S_0_j':6,
        'S_5_3':4,'S_2':5,'half_A':4,'half_S':4,'mid_AA':2
    }
    assert len(ff)==expected[label]
    if label=='S_2':
        assert freeg==[([c1,c2,K.convert(3)],c2,'A')]
        assert sum(profile[-1] is None for profile in ff)==1
    else:
        assert not freeg and all(profile[-1] is not None for profile in ff)
    print(label,'degree',K.mod.degree(),'four-prefix fits',len(ff),
          'free g',len(freeg),'free B',sum(x[-1] is None for x in ff),flush=True)
    def reflect(a):
        return R.from_dict({(i,):(-1)**i*v for (i,),v in a.items()})
    sols=[]
    for k,(bf,xf,gf,lf,pf,Bf) in enumerate(ff):
      for j,(br,xr,gr,lr,pr,Br) in enumerate(ff):
        # These are physical submissions and must not use any clock >2 times.
        cc=xf+[D-x for x in xr]
        if any(cc.count(d)>2 for d in XX):continue
        if Bf is None and Br is None:
            sols.append(('both-free',k,j));continue
        # L is the nonzero residual scale 2G, forward g = L * reverse g.
        # Store all necessary polynomial equalities, just in L.
        eq=[]
        if Bf is not None and Br is not None:
            eq.append(T*T-R(Br/Bf))
            Afx=reflect(lf-Bf*pf); Ar=lr-Br*pr
            eq.extend([T*Afx.get((i,),c0)-Ar.get((i,),c0) for i in range(3)])
        elif Bf is not None:
            Afx=reflect(lf-Bf*pf)
            eq.extend([T*Afx.get((i,),c0)-lr.get((i,),c0)+T*T*Bf*pr.get((i,),c0) for i in range(3)])
        else:
            Ar=lr-Br*pr
            lf,pf1=reflect(lf),reflect(pf)
            eq.extend([T*Ar.get((i,),c0)-T*T*lf.get((i,),c0)+Br*pf1.get((i,),c0) for i in range(3)])
        e=[p for p in eq if p]
        if not e:
            sols.append(('all-scales',k,j));continue
        g=e[0]
        for v in e[1:]: g=g.gcd(v)
        while g and not g.get((0,),c0):g//=T
        if g.degree()==0:continue
        keep=[]
        for f,_ in g.factor_list()[1]:
            if f.degree()==1:
                x0=-f.get((0,),c0)/f.get((1,),c1)
                if any(y==D-z and gy is not None and gz is not None and gy==x0*gz for y,gy in zip(xf,gf) for z,gz in zip(xr,gr)):
                    continue
            keep.append(f.degree())
        if keep:
            sols.append((k,j,keep))
    print(label,'surviving end combinations',sols,flush=True)
    assert not sols

if __name__=='__main__':
    for case in meshes():
        read_case(*case)
    for case in mid_mesh():
        read_case(*case)

    print('verified all exact five-double end fits excluded',flush=True)
