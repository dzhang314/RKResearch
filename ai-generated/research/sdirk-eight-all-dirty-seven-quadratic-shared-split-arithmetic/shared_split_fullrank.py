"""Normalized symmetric graph/remainder/Vieta projection for the true rank-two fit."""
from flint import fmpz_mpoly_ctx as Ctx
ctx=Ctx.get(('m','p'),'lex')
m,p=ctx.gens()
N=8*m**3-16*m*m*p-22*m*m+6*m*p*p+23*m*p+36*m+8*p*p-36*p-16
M=8*m**3-8*m*m*p+14*m*m+2*m*p*p-83*m*p-12*m-16*p**3+72*p*p+32*p
J=2*(8*m*m-16*m*p+14*m+6*p*p-27*p-12)
E=m*m-4*p
DD=(-6*m+9*p+4)*(-2*m+p+4)
C=35*M*M+42*M*N+15*N*N-21*E*J*J
H0=M*M*N-M*(E*(J*J-3*J*N+2*N*N)-5*p*N*N)+4*p*p*N**3
H1=E*J*(J-N)*(J-2*N)+M*(3*N-2*J)*N+p*(6*N-5*J)*N*N
F=5*J*H0+(5*M+3*N)*H1
def prod(a,b,c):
    return a*a*p*p+a*b*p*m+a*c*(m*m-2*p)+b*b*p+b*c*m+c*c
Wprod=prod(N-J,0,M+J*p)
Dprod=prod(J-N-M,2*M,-J*p)
V=20*p*p*Wprod*(35*M*M-3*N*N)*J-9*Dprod*H1

def strip(f):
    for g in (N,p,J,E,DD,35*M*M-3*N*N):
        while (h:=f.gcd(g)).total_degree()>0:
            q,r=divmod(f,h)
            assert not r
            f=q
    return f
C=strip(C);F=strip(F);V=strip(V)
if __name__=='__main__':
    print('bidegrees',[(s.degrees(),s.total_degree()) for s in [C,F,V]],flush=True)
    g=C.resultant(F,'p')
    print('first projected degree',g.total_degree(),flush=True)
    h=C.resultant(V,'p')
    print('second projected degree',h.total_degree(),flush=True)
    u=g.gcd(h)
    print('gcd projection',u.factor(),flush=True)
    assert { (q.total_degree(), e) for q,e in u.factor()[1]}=={(1,16),(8,1),(3,2),(1,6)}
