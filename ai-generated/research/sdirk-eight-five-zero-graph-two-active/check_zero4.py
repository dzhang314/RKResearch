"""Finite genuine two-active graph frame, first zero at physical 4."""
from sympy.polys.rings import ring
import sympy as S
from itertools import permutations
v=S.symbols('v')
f=S.Poly(4*v**3-12*v*v+3*v+2,v)
assert f.is_irreducible
K=S.QQ.algebraic_field((f,v));V=K.unit
C=lambda a,b=1:K.convert(S.Rational(a,b))
L=lambda t,D:70*t**4-140*D*t**3+90*D**2*t*t-20*D**3*t+D**4
h=lambda u:-2+u+4*u*u-u**3
kappa=lambda u:1+2*u-u*u
def det(M):
 a,b,c=M
 return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
for front in ('star','arith'):
    # x_i=alpha_i+beta_i*u, first three physically off and distinct.
    cf=[(1,0),(1,1),(3,-1) if front=='star' else (1,2)]
    for i,j in permutations(range(3),2):
        # i pairs with terminal stage 10, j with stage 9.
        ai,bi=cf[i];aj,bj=cf[j]
        U=(V-ai+aj)/K.convert(bi-bj)
        xs=[a+b*U for a,b in cf]
        D=xs[i]+1
        assert xs[j]==D-1-V
        T=D-1-2*V
        if not D or len(set(xs)) != 3 or not kappa(U):
            print(front,(i+1,j+1),"literal guard",flush=True);continue
        assert L(T,D), (front,i,j,"Gaussian ordinary rear point")
        if front=='star':
            p=[C(-1),C(2),C(-1,2)]
        else:
            hu=h(U)
            if not hu:
                assert 3*U-2
                print(front,(i+1,j+1),"front denominator",flush=True);continue
            b=(3*U-2)/hu
            p=[-1+b*(1+U),2-b*(2+U),C(-1,2)+b]
        assert p[0]+p[1]+p[2]==C(1,2)
        R,B,A=ring(f"b{front}{i}{j},a{front}{i}{j}",K)
        RA=R.drop(0)
        Jraw=lambda k,t:sum((z*t**(n+k+1)*C(1,n+k+1) for n,z in enumerate(p)),R.zero)
        evraw=lambda t:sum((z*t**n for n,z in enumerate(p)),R.zero)
        gate=Jraw(0,A)-evraw(A)
        assert gate
        ms=[R(D**(k+2)*C(1,k+3))-(A+T)*D**(k+1)*C(1,k+2)+A*T*D**k*C(1,k+1) for k in range(6)]
        mm=[[ms[i+j] for j in range(3)] for i in range(3)]
        Delta=det(mm)
        A0=gate.drop(0);olds=A0.degree()
        gs=[A,A-T,L(A,D),evraw(A),Delta]
        dropped=[]
        for raw in gs:
            ct=0;zz=raw.drop(0)
            while True:
                c=A0.gcd(zz)
                if c.degree()==0:break
                A0=A0//c;ct+=c.degree()
            dropped.append(ct)
        if A0.degree()==0:
            print(front,(i+1,j+1),"no first zero roots",olds,dropped,flush=True);continue
        A0=A0.monic();Ma=R.from_dict({(0,n):z for (n,),z in A0.items()})
        Delta%=Ma
        num=[]
        for q in range(3):
            X=[r[:] for r in mm]
            for k in range(3):X[k][q]=-ms[k+3]
            num.append(det(X)%Ma)
        q,ell,k=num
        QB=B**3+k*B*B+ell*Delta*B+q*Delta**2
        def rd(x):return (R(x)%QB)%Ma
        a=rd(Delta*A);b=rd(B);g=rd(Delta);d=rd(D*Delta)
        profile=[rd(z*g**(2-i)) for i,z in enumerate(p)]
        def ev(t):return rd(sum(z*t**n for n,z in enumerate(profile)))
        def J(i,t):return rd(sum(z*t**(n+i+1)*C(1,n+i+1) for n,z in enumerate(profile)))
        la=rd(L(a,d));lb=rd(L(b,d))
        F=rd(la*(a*(J(0,b)-g*ev(b))+g*b*ev(b)-J(1,b))-lb*(g*a*ev(a)-J(1,a)))
        def Norm(u):
            cols=[rd(u*B**k) for k in range(3)]
            mat=[[R.from_dict({(0,n):c for (i,n),c in col.items() if i==k}) for k in range(3)] for col in cols]
            return (det(mat)%Ma).drop(0)
        needed=A0.gcd(Norm(F))
        print(front,(i+1,j+1),"first degree",olds,"dropped",dropped,"left",A0.degree(),"second-gate gcd",needed.degree(),flush=True)
        assert needed.degree()==0
