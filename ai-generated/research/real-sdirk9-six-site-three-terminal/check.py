from sympy import Poly,symbols
from itertools import combinations
from functools import reduce,lru_cache
z=symbols('Z')
x=symbols('x')

def seed(p):
    return Poly(x**3-9*x*x+18*x-6,x,modulus=p)

def first_port(s,p):
    return Poly(x**4-(8*s*pow(3,-1,p)+8)*x**3+(2*s*s+16*s+12)*x*x
                -(8*s*s+16*s)*x+4*s*s,x,modulus=p)

def shifted_second(s,v,p):
    r=2*(3*s-v)%p
    assert r
    q=v*(2*s-v)*pow(r,-1,p)%p
    k=Poly((x-s)*(x-v)*(x-q),x,modulus=p)
    j=Poly(0,x,modulus=p)
    for (i,),a in k.terms():
        j+=Poly(int(a)*pow(i+1,-1,p)*x**(i+1),x,modulus=p)
    F=(j-k).exquo(Poly(x-v,x,modulus=p))
    assert F.degree()==3
    return F.monic()

def simple(F,a,p):
    assert int(F.eval(a))%p==0 and int(F.diff().eval(a))%p!=0

def irreducible(F,p,prime_divisor):
    # In the two cases n=3,4, n has exactly one distinct prime divisor.
    n=F.degree()
    X=Poly(x,x,modulus=p)
    def powX(m):
        W=Poly(1,x,modulus=p);B=X
        while m:
            if m&1:W=(W*B).rem(F)
            B=(B*B).rem(F)
            m>>=1
        return W
    assert powX(p**n)==X
    assert F.gcd(powX(p**(n//prime_divisor))-X).degree()==0
def screen(p,v,w):
    Q=lambda u:Poly(u,z,modulus=p)
    o=Q(1);n=Q(0);x=Q(z)
    def ymul(a,b):
        c=[n]*(len(a)+len(b)-1)
        for j,x in enumerate(a):
            for k,y in enumerate(b):c[j+k]+=x*y
        return c
    def ymoment(a,j=0):
        return sum((v*pow(i+j+1,-1,p)for i,v in enumerate(a)),n)
    def JP(a):
        return [n]+[u*pow(i+1,-1,p)for i,u in enumerate(a)]
    @lru_cache(None)
    def det(M):
        if len(M)<2:return M[0][0] if M else o
        s=n
        for j,u in enumerate(M[0]):
            if not u.is_zero:s+=(-1)**j*u*det(tuple(row[:j]+row[j+1:] for row in M[1:]))
        return s
    def rows(f,G):
        return [ymoment(ymul(G,f),j)for j in range(3)]+[ymoment(ymul(G,JP(f)),j)for j in range(2)]
    def matrix(G,vec):
        return list(map(tuple,zip(*(rows(q,G) for q in vec))))
    def minors45(M):
        return [det(tuple(M[j] for j in R))for R in combinations(range(5),4)]
    def noy(v,w):
        ga=pow(1+v,-1,p)
        ar=Q(ga);br=Q(1-ga*w);cr=x
        G=ymul(ymul([-ar,o],[-br,o]),[-cr,o])
        return minors45(matrix(G,[[n]*i+[o]for i in range(4)]))
    def live(v,w):
        ar=o-v*x;br=o-w*x;cr=x
        G=ymul(ymul([-ar,o],[-br,o]),[-cr,o])
        return minors45(matrix(G,[[n]*i+[o]for i in range(4)]))
    def terminal(v,w):
        ar=o-v*x;br=o-w*x
        G0=ymul([-ar,o],[-br,o]);G1=[n]+G0
        fs=[[n]*i+[-x,o]for i in range(3)]
        B=matrix(G1,fs);A=matrix(G0,fs)
        R=[b+a for b,a in zip(B,A)] # [q0,q1,q2,-c*q0,-c*q1,-c*q2]
        C=[(-1)**j*det(tuple(row[:j]+row[j+1:]for row in R))for j in range(6)]
        return [C[i]*C[j+3]-C[j]*C[i+3]for i,j in combinations(range(3),2)]
    return [noy(v,w),noy(w,v),live(v,w),terminal(v,w)]

def coeffs(f):
    return [int(f.nth(i))%37 for i in range(f.degree()+1)]

def main():
    import sys
    assert all(n**3-9*n*n+18*n-6 for n in [-6,-3,-2,-1,1,2,3,6])
    simple(seed(31),11,31)
    irreducible(first_port(11,31),31,2)
    simple(seed(17),16,17)
    simple(first_port(16,17),1,17)
    irreducible(shifted_second(16,1,17),17,3)
    simple(seed(37),8,37)
    simple(first_port(8,37),3,37)
    simple(shifted_second(8,3,37),19,37)
    assert (1+3)*(1+19)%37
    if '--lean-data' not in sys.argv:
        print('Cubic irreducible over Q; mod-31 and mod-17 irreducibility tests passed; all three residue roots at p=37 simple.')
    for n,(family,(i,j),deg) in enumerate(zip(screen(37,3,19),
            [(0,1),(0,1),(1,3),(0,2)],[4,4,11,30])):
        f,g=family[i],family[j]
        assert f.degree()==g.degree()==deg
        U,V,h=f.gcdex(g)
        assert h.as_expr()==1 and U*f+V*g==h
        if '--lean-data' in sys.argv:
            for label,F in [('f',f),('g',g),('u',U),('v',V)]:
                print(f'def {label}{n} : P := {coeffs(F)}')
        else:
            print(f'role {n}: exact degree-{deg} coprime residue pair; Bézout verified.')
if __name__=='__main__':
    main()
