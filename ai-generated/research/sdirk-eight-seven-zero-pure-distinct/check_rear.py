"""Exact simple reductions of the fixed forward clock tower for all rear phases."""
import sympy as S
from flint import nmod_poly
from forward_clock_tower import make_tower

def rr(a,p):
    s=S.Rational(str(a))
    return int(s.p)*pow(int(s.q),-1,p)%p

def evk(a,z,p):
    k=0
    for c in a.to_list():
        k=(z*k+rr(c,p))%p
    return k

def fmt(P,p):
    return nmod_poly([rr(c,p) for c in reversed(P.all_coeffs())],p)

def check_arithmetic_or_silent(p,a,b,D,mode):
    """In the live arithmetic or silent case, test the known gap polynomial
    against the augmented rank determinant for two as-yet unknown labels."""
    w=nmod_poly([0,1],p);one=nmod_poly([1],p)
    s=one*(D-1);t=s-w;r=s-2*w
    def prod(seq):
        m=[one]
        for q in seq:
            nxt=[m[0]*(-q)]
            for j in range(1,len(m)):
                nxt.append(m[j-1]-m[j]*q)
            nxt.append(m[-1])
            m=nxt
        return m
    def I(m,j):
        return sum((c*(pow(D,k+j,p)*pow(k+j+1,-1,p)%p) for k,c in enumerate(m)),nmod_poly([],p))
    P5=prod([a,b,s,t,r]);Ps=prod([a,b,t,r]);Pt=prod([a,b,s,r]);Pr=prod([a,b,s,t])
    KK=one+2*w-w*w
    H=w**3-4*w*w-w+2
    Q=4*w**3-12*w*w+3*w+2
    M0=[I(P5,i) for i in range(3)]
    M1=[KK*I(Pt,i)-I(Ps,i) for i in range(3)]
    if mode=="silent":
        M2=[I(Pr,i) for i in range(3)]
        cond=H
    else:
        M2=[-KK*Q*I(Pr,i)-H*I(Ps,i) for i in range(3)]
        cond=8*w**6-44*w**5+22*w**4+97*w**3-55*w*w-13*w+6
    a,b,c=M0;d,e,f=M1;g,h,i=M2
    det=a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
    assert cond.degree()==(3 if mode=="silent" else 6)
    return cond.gcd(det).degree()==0, (det.degree(),cond.gcd(det).degree())

def check_star(p,a,b,D,d):
    """In star, difference of the two equal reverse cardinal numerators
    cancels the squared displacement out of both ordinary recovery rows."""
    X=nmod_poly([0,1],p)
    s=(D-1)%p;m=(D-2)%p
    F=(X-a)*(X-b)*(X-s)
    def I(P):
        return sum(int(P[i])*pow(D,i,p)*pow(i+1,-1,p) for i in range(P.degree()+1))%p
    W=F*(X-m)*(X-m)
    f0,f1,f2=[I(F*X**i) for i in range(3)]
    g0,g1,g2=[I(W*X**i) for i in range(3)]
    delt=(f0*g1-f1*g0)%p
    if not delt:
        return False, (0,)
    iv=pow(delt,-1,p)
    q0=(f1*g2-f2*g1)*iv%p
    q1=(f2*g0-f0*g2)*iv%p
    U=X*X+q1*X+q0
    S3=(X-a)*(X-b)*(X-d)
    J=nmod_poly([0]+[int(S3[i])*pow(i+1,-1,p)%p for i in range(S3.degree()+1)],p)
    L=lambda t:70*t**4-140*D*t**3+90*D*D*t*t-20*D**3*t+D**4
    G=int(L(a)%p)*(S3-J)+int(J(a))*L(X)
    return U.gcd(G).degree()==0, (delt, q1,q0,U.gcd(G).degree())


CERT={
 0:{"silent":(61,29,38,52,4,(4,0)),
    "arithmetic":(61,29,38,52,4,(9,0)),
    "star":(61,29,38,52,4,(22,27,12,0))},
 1:{"silent":(41,29,35,35,17,(4,0)),
    "arithmetic":(41,29,35,35,17,(9,0)),
    "star":(41,29,35,35,26,(38,3,1,0))}
}
def run(side):
    K,g,u,b,a,d,R,D,fs=make_tower(side)
    [(phi,e)]=fs
    assert e==1 and phi.degree()==4
    phi=phi.monic()
    for mode,(p,z,u_res,b_res,Ds,expected) in CERT[side].items():
        gz=fmt(g,p)
        assert gz.degree()==9 and not gz(z) and gz.derivative()(z)
        ph=nmod_poly([evk(phi.get((i,),K.zero),z,p) for i in range(5)],p)
        assert ph.degree()==4 and not ph(Ds) and ph.derivative()(Ds) and Ds
        uu,bb,aa,dd=[evk(q,z,p) for q in (u,b,a,d)]
        assert uu==u_res and bb==b_res and (uu+bb)%p==z
        assert aa==(1+2*uu)%p and dd==(1+side*uu)%p
        ans,aux=(check_star(p,aa,bb,Ds,dd) if mode=='star' else check_arithmetic_or_silent(p,aa,bb,Ds,mode))
        assert ans and aux==expected
        print(side,mode,"verified exact-field residue",CERT[side][mode],flush=True)
if __name__=="__main__":
    for i in (0,1):run(i)
