"""Exact standalone opposite central orientation exit.
Dependencies: SymPy and python-flint 0.9 (or compatible).
Width projections are reconstructed over the integers with certified l1
bounds, followed by an exact degree-84 coefficient-fiber check and lift.
"""
from math import gcd,lcm,factorial
import flint
import sympy as sy
from sympy import QQ
from sympy.polys.rings import ring
from functools import reduce
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],[-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]
T4=[1,-32,216,-480,330]
U4=[[1,-32,216,-480,330],[-32,992,-6480,13920,-9240],[216,-6480,41040,-85680,55440],[-480,13920,-85680,174720,-110880],[330,-9240,55440,-110880,69300]]
def ev(cs,q):return sum(c*q**i for i,c in enumerate(cs))
def dot(g,h):return sum(g[i]*N[i][j]*h[j] for i in range(5) for j in range(5))
def integ(f,j=0):return sum(c/(q[0]+j+1) for q,c in f.items())
def at(f,z):return sum(c*z**q[0] for q,c in f.items())
def hom(f,z,zD):
    n=f.degree()
    return sum(T(c)*z**i[0]*zD**(n-i[0]) for i,c in f.items())
def common_model(K):
    ar,a0=ring('a',K)
    global T
    T,x=ring('x',ar)
    W,X=ring('X',T)
    a=T(a0); b=2-a; h=a/2; d=a-1
    V=X**2*(X-a)**2
    U=(1-X)**2*(X-d)**2
    prim=lambda f:sum(c*X**(q[0]+1)/(q[0]+1) for q,c in f.items())
    P=prim(V)
    _Q=prim(U)
    Q=W(sum(_Q.values()))-_Q
    H=integ(P*U);C1=integ(P*U,1);C2=integ(V*Q,1);J=integ(P*Q)
    I0,I1,I2=[integ(V*U,j) for j in range(3)]
    A=H*H-J*I0;B=J*I1-H*C1;C=J*I1-H*C2;D=C1*C2-J*I2
    Del=A*D-B*C
    E=A*x+C;Y=-(B*x+D);II=E*(I2-x*I1)+Y*(x*I0-I1)
    al=E*C1-Y*H;be=C2-x*H
    P5=(X-a)*(X-h)*(X-d)*(X-x)*(E*X-Y)
    mo=[integ(X*(1-X)*P5,j) for j in range(4)]
    EL=lambda q:[q**(i+1) for i in range(5)]
    ER=lambda q:[(1-q)*q**i for i in range(5)]
    dl0=[T.one]+[T.zero]*4;dl1=[(i+1)*a**i for i in range(5)]
    dr0=[T.one]*5;dr1=[d**i-(b*i*d**(i-1) if i else 0) for i in range(5)]
    Dx=[a**5*q-30*at(P,x)*r for q,r in zip(EL(x),EL(a))]
    Fx=[b**5*q-30*at(Q,x)*r for q,r in zip(ER(x),ER(d))]
    K0,K1=[dot(Dx,r).exquo(a*x*(a-x)) for r in [dr0,dr1]]
    KL0,KL1=[dot(l,Fx).exquo(b*(1-x)*(x-d)) for l in [dl0,dl1]]
    Ta,Tb=ev(T4,a),ev(T4,b)
    Uab=ev([ev(row,b) for row in U4],a)
    return locals()

def build():
    B=common_model(QQ)
    T=B['x'].ring
    a,b,h,d,x,E,Y,I0,I1,I2,H,C1,C2=[B[k] for k in ('a','b','h','d','x','E','Y','I0','I1','I2','H','C1','C2')]
    V,P,Q=B['V'],B['P'],B['Q']
    ddL=[B['dl0'],B['dl1']];ddR=[B['dr0'],B['dr1']]
    leftA=[dot(B['EL'](a),r) for r in ddR]
    rightB=[dot(l,B['ER'](d)) for l in ddL]
    R,t,z=ring('t,z',T)
    Z=lambda f:R(f)
    Ta,Tb,Uab=B['Ta'],B['Tb'],B['Uab']
    l0=(Z(a)-t)*Z(a*E-Y)
    l1=-t*Z(Y)
    r0=(t-Z(d))*Z(x-d)
    r1=-(1-t)*Z(1-x)
    P2=l0*r0+Z(Ta)*l1*r0+Z(Tb)*l0*r1+Z(Uab)*l1*r1
    K0y,K1y=[hom(B[k],Y,E) for k in ('K0','K1')]
    IL=Z(I2-x*I1)+z*Z(x*I0-I1)
    IR=Z(E*I2-Y*I1)+z*Z(Y*I0-E*I1)
    ML=Z(a)*IL*(r0*Z(K0y)+r1*Z(K1y)) + 30*Z(Y*(a*E-Y)*(Y-x*E))*(Z(C1)-z*Z(H))*(r0*Z(leftA[0])+r1*Z(leftA[1]))
    MR=Z(b)*IR*(l0*Z(B['KL0'])+l1*Z(B['KL1'])) + 30*Z((1-x)*(x-d)*(x*E-Y))*(Z(C2)-z*Z(H))*(l0*Z(rightB[0])+l1*Z(rightB[1]))
    m0,m1,m2,m3=B['mo']
    D2=m0*m2-m1*m1; D1=m0*m3-m1*m2; D0=m1*m3-m2*m2
    assert all(q.degrees()==(1,1) for q in [ML,MR])
    get=lambda q,i,j:q.get((i,j),T.zero)
    def red(q):
        return (get(q,1,0)-get(q,0,1),
            D2*get(q,0,0)+D1*get(q,0,1)+D0*get(q,1,1))
    AL,BL=red(ML);AR,BR=red(MR)
    AP=D2*get(P2,1,0)+D1*get(P2,2,0)
    BP=D2*get(P2,0,0)-D0*get(P2,2,0)
    R12=AL*BR-AR*BL
    RL= D2*AL*BP-AP*BL
    RR= D2*AR*BP-AP*BR
    QL= BL**2+D1*AL*BL+D0*D2*AL**2
    QR= BR**2+D1*AR*BR+D0*D2*AR**2
    return locals()

def data():
    B=build()
    ctx=flint.fmpq_mpoly_ctx.get(('a','x'))
    rat=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    ff=lambda p:ctx.from_dict({(j,i):rat(c) for (i,),v in p.items() for (j,),c in v.items()})
    F=[(k,ff(B[k])) for k in ('R12','RL','RR','QL','QR')]
    a,b=ff(B["a"]),ff(B["b"])
    B0={k:p for k,p in F}
    divisors=[a*a*b**n for n in (4,2,4,2,6)]
    ans={}
    for (k,f),g in zip(F,divisors):
        assert not f%g
        ans[k]=f//g
    assert [p.degrees() for p in ans.values()]==[(83,14),(94,15),(83,15),(116,18),(94,18)]
    return B,ctx,ans

def primitive(f):
    q=f.to_dict()
    L=lcm(*(int(c.denominator) for c in q.values()))
    b={k:int(v.numerator)*(L//int(v.denominator)) for k,v in q.items()}
    d=gcd(*b.values())
    return {k:v//d for k,v in b.items()}

def l1(f):return sum(abs(n) for n in f.values())
def dx(f):return max(i[1] for i in f)
def da(f):return max(i[0] for i in f)

def verify_projection(F, f84):
    A=primitive(F["R12"])
    U={k:primitive(F[k]) for k in ("RL","RR","QL")}
    bounds={k:factorial(dx(A)+dx(f))*l1(A)**dx(f)*l1(f)**dx(A)
            for k,f in U.items()}
    assert [v.bit_length() for v in bounds.values()]==[8157,7775,9835]
    degrees={k:da(A)*dx(f)+da(f)*dx(A) for k,f in U.items()}
    buffers={k:[0]*(degrees[k]+1) for k in U}
    p=2**61-1
    M=1
    count=0
    while M<=2*max(bounds.values()):
        p=int(sy.nextprime(p))
        assert flint.fmpz(p).is_prime()
        C=flint.nmod_mpoly_ctx.get(("x","a"),p)
        into=lambda f:C.from_dict({(j,i):v%p for (i,j),v in f.items()})
        x0=into(A)
        vals={k:into(f) for k,f in U.items()}
        if x0.degrees()[0]!=dx(A) or any(vals[k].degrees()[0]!=dx(U[k]) for k in U):
            continue
        inv=pow(M%p,-1,p)
        for k,T in vals.items():
            R=x0.resultant(T,"x")
            assert all(not t[0] and t[1]<=degrees[k] for t in R.to_dict())
            res={i[1]:int(c) for i,c in R.to_dict().items()}
            buf=buffers[k]
            for j in range(len(buf)):
                buf[j]+=M*(((res.get(j,0)-buf[j])%p)*inv%p)
        M*=p
        count+=1
    assert all(M>2*v for v in bounds.values())
    polies={}
    for k,buf in buffers.items():
        coeff=[n-M if 2*n>M else n for n in buf]
        assert all(abs(n)<=bounds[k] for n in coeff)
        polies[k]=flint.fmpz_poly(coeff)
    assert [q.degree() for q in polies.values()]==[2424,2298,2936]
    rd=polies["RL"].gcd(polies["RR"]).gcd(polies["QL"])
    assert rd.degree()==862
    a=flint.fmpq_poly([0,1])
    f4=33*a**4-132*a**3+176*a**2-88*a+16
    f6=2475*a**6-14850*a**5+34140*a**4-37560*a**3+20136*a**2-4752*a+352
    expected=a**112*(a-2)**74*(f4/f4[4])**49*(f6/f6[6])**52*f84**2
    rd=flint.fmpq_poly(rd)
    assert rd/rd[rd.degree()]==expected
    print("exact width projection gcd degree 862, prime count",count)

def verify_nodal_width(B,C,P):
    cv=lambda c:flint.fmpq(int(c.numerator),int(c.denominator))
    ff=lambda p:C.from_dict({(j,i):cv(c) for (i,),u in p.items() for (j,),c in u.items()})
    D0,D1,D2=[ff(B[k]) for k in ('D0','D1','D2')]
    a,x=C.gens()
    rr=[D2.resultant(D1,'x'),D2.resultant(D0,'x'),D1.resultant(D0,'x')]
    assert all(r.degrees()==(168,0) for r in rr)
    g=reduce(lambda f,h:f.gcd(h),rr)
    fs=g.factor()[1]
    assert sorted((f.degrees()[0],k) for f,k in fs)==[(1,8),(1,8),(4,4),(6,4),(84,1)]
    f84=next(f for f,k in fs if f.degrees()==(84,0))
    F=flint.fmpq_poly([f84.to_dict().get((i,0),0) for i in range(85)])
    F=F/F[84]
    c=flint.fmpq_poly([0,1])
    f4=33*c**4-132*c**3+176*c**2-88*c+16
    f6=2475*c**6-14850*c**5+34140*c**4-37560*c**3+20136*c**2-4752*c+352
    gm=flint.fmpq_poly([g.to_dict().get((j,0),0) for j in range(g.degrees()[0]+1)])
    assert gm/gm[gm.degree()]==c**8*(c-2)**8*(f4/f4[4])**4*(f6/f6[6])**4*F
    pline=[t for t in B['D2'].subresultants(B['D1']) if t.degree()==1][-1]
    ac=lambda poly:flint.fmpq_poly([cv(poly.get((j,),0)) for j in range(poly.degree()+1)])
    L=ac(pline[(1,)])%F
    N=ac(pline[(0,)])%F
    p=101;ctx=flint.fmpz_mod_poly_ctx(p)
    red=lambda q:int(q.numerator)%p*pow(int(q.denominator),-1,p)%p
    rp=lambda u:ctx([red(q) for q in u.coeffs()])
    Fp=rp(F)
    assert rp(L).gcd(Fp).degree()==0
    assert rp(c*(c-2)).gcd(Fp).degree()==0
    def subst(poly):
        n=poly.degree()
        return sum((ac(c)*pow(-N,j[0])*pow(L,n-j[0]))%F for j,c in poly.items())%F
    assert not any(subst(B[k]) for k in ('D0','D1','D2'))
    print('exact X=-N/L is a simultaneous nodal root; L unit at 101')

    mods=Fp.factor()[1]
    assert sorted((f.degree(),k) for f,k in mods)==[(1,1),(1,1),(2,1),(2,1),(78,1)]
    for f,k in mods:
        K=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD')
        R=flint.fq_default_poly_ctx(K)
        A=K.gen()
        py=lambda p: sum((K(red(c))*A**j for j,c in enumerate(p.coeffs())),K.zero())
        u=R([py(N)/py(L),K.one()])
        def lift(f):
            h=[K.zero()]*(f.degrees()[1]+1)
            for (i,j),c in f.to_dict().items(): h[j]+=K(red(c))*A**i
            return R(h)
        polies=[lift(P[s]) for s in ('R12','RL','RR','QL','QR')]
        assert [f.degree() for f in polies]==[14,15,15,18,18]
        powers=[1,2,2,2,2]
        for q,n in zip(polies,powers):
            assert not q % (u**n)
        quot=[q//(u**n) for q,n in zip(polies,powers)]
        assert [q.degree() for q in quot]==[13,13,13,16,16]
        assert reduce(lambda f,h:f.gcd(h),quot).degree()==0
        print('component',f.degree(),'quotient arithmetic unit ideal',flush=True)
    return F

if __name__=="__main__":
    B,C,P=data()
    f84=verify_nodal_width(B,C,P)
    verify_projection(P,f84)
