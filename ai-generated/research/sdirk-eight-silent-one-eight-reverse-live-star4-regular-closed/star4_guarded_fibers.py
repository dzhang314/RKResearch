"""Exact characteristic-zero fourth guards, followed by complete local proof."""
from star4_actual_fifth import *
from flint import fmpq_poly

class Field:
    def __init__(self,M):
        self.M=M*(1/M[M.degree()])
    def __call__(self,x):
        if isinstance(x,Elem):
            assert x.A is self
            return x
        if not isinstance(x,fmpq_poly):
            x=fmpq_poly([x])
        return Elem(x%self.M,self)
class Elem:
    def __init__(self,x,K):self.x,self.A=x,K
    def __bool__(self):return bool(self.x)
    def __eq__(self,z):return self.x==self.A(z).x
    def __add__(self,z):return self.A(self.x+self.A(z).x)
    __radd__=__add__
    def __neg__(self):return self.A(-self.x)
    def __sub__(self,z):return self.A(self.x-self.A(z).x)
    def __rsub__(self,z):return self.A(self.A(z).x-self.x)
    def __mul__(self,z):return self.A(self.x*self.A(z).x)
    __rmul__=__mul__
    def inv(self):
        d,u,_=self.x.xgcd(self.A.M)
        if d!=fmpq_poly([1]):raise ArithmeticError('exact gamma algebra nonunit')
        return self.A(u)
    def __truediv__(self,z):return self*self.A(z).inv()
    def __rtruediv__(self,z):return self.A(z)*self.inv()

def gpoly(P):
    cf={}
    for (iv,is0,ig,it),a in P.to_dict().items():
        assert iv==is0==it==0
        cf[ig]=a
    return fmpq_poly([cf.get(i,0) for i in range(max(cf,default=-1)+1)])

@lru_cache(None)
def bounds():
    P,Q,A,B,H,D,(a,b,q,A0,B0,x)=exact_model()
    _,_,_,L1,(aa,bb,cq,La,Lb,A0o,B0o)=profile(True)
    m=1-2*g
    cc=lambda z:red(B*(z-m)**2+g*g*A)
    J=[
      ('regular_scale',D),
      ('early_clock',red((s-A0)*(s-B0))),
      ('x_equals_q',x-q),
      ('quintic',H[-1]),
      ('terminal_defect',ev(H,x)),
      ('tail_B',B),
      ('gap_w0',A),('gap_w1',red(A+B)),('gap_w2',red(A+2*B)),
      ('rear_equals_literal',red(cc(a)*cc(b))),
      ('rear_equals_silent_q',cc(q)),
    ]
    gg=red(g*La*Lb*(x-a)*(x-b))
    F0,F1=[tuple(gpoly(e) for e in Co(Z1,1)) for Z1 in (P,Q)]
    return F0,F1,gpoly(gg),[(name,tuple(gpoly(e) for e in Co(v,1))) for name,v in J]

def norm(a,p):
    return int(a.p)*pow(int(a.q),-1,p)%p

def modQ(M,p):
    return nmod_poly([norm(a,p) for a in M],p)

def modcoef(v,K,gg,p):
    w=K(0)
    for a in list(v.x)[::-1]:
        w=w*gg+norm(a,p)
    return w

def all_mod(F,p,t,guarded=None,verbose=False):
    P,Q,*_=exact_model()
    FF=modQ(F,p)
    assert FF.degree()==F.degree() and FF.leading_coefficient()==1
    counts=0;bad=[]
    for T,e in FF.factor()[1]:
        K=Bfield(T,p,t);gg=K(nmod_poly([0,1],p))
        if guarded is None:
            PP=sv(P,K,gg,p,t);QQ=sv(Q,K,gg,p,t)
            if len(PP)!=11 and len(QQ)!=25:
                bad.append((T.degree(),-1,-1))
                continue
        else:
            PP=[modcoef(z,K,gg,p) for z in guarded]
            assert PP and PP[-1]==1
            QQ=sv(Q,K,gg,p,t)
        W=gcdp(PP,QQ)
        if len(W)<=1:
            counts+=1;continue
        d=tests_in_s(K,gg,W,p,t)
        if len(d)>1:
            bad.append((T.degree(),len(W)-1,len(d)-1))
        else:counts+=1
    if verbose or not bad:
        print('independent fifth exact factor replay',F.degree(),p,t,'covered factors',counts,'nonfinal',bad,flush=True)
    return not bad,counts


PLAN={
    (28,1):('regular_scale',1,2),
    (131,1):(None,0,4),
    (35,2):('regular_scale',1,4),
    (9,2):('x_equals_q',1,4),
    (27,6):('terminal_defect',3,4),
    (1,7):('gap_w2',3,1),
    (2,7):('gap_w2',3,2),
    (4,9):('gap_w2',3,2),
    (21,24):('rear_equals_literal',3,2),
    (1,24):('rear_equals_literal',6,1),
    (4,27):('identical_gap_w2',0,0),
    (3,32):('actual_cubic_leading',2,0),
}

def one_factor(M,e,p,t):
    d=M.degree();K=Field(M)
    P0,Q0,_,basis=bounds()
    branch,n0,spl=PLAN[d,e]
    gs=dict(basis)
    if branch is None:
        okay,n=all_mod(M,p,t)
        assert okay and n==spl
        return
    P,Q=map(lambda b:trim(list(map(K,b))),(P0,Q0))
    if branch=='identical_gap_w2':
        assert not trim(list(map(K,gs['gap_w2'])))
        print('exact gamma factor forces actual forbidden k=0',d,e,flush=True)
        return
    if branch=='actual_cubic_leading':
        Qgamma=fmpq_poly([1,-12,60,-120])
        assert M==Qgamma*(1/Qgamma[3])
        assert (len(P)-1,len(Q)-1)==(6,16)
        S=gcdp(P,Q);assert len(S)==3
        H=trim(list(map(K,gs['quintic'])))
        removed=0
        while len(S)>1:
            J=gcdp(S,H)
            assert len(J)>1
            T,R0=qr(S,J);assert not R0 and T
            removed+=len(J)-1;S=T
        assert removed==n0==2
        print('exact common fourth leading cubic has all common support in the nonzero quintic guard',d,e,flush=True)
        return
    assert P
    G=trim(list(map(K,gs[branch])));assert G
    removed=0
    while len(P)>1:
        D=gcdp(P,G)
        if len(D)<=1:break
        Z,R0=qr(P,D);assert not R0 and Z
        removed+=len(D)-1;P=Z
    assert removed==n0
    print('exact true fourth guard',d,e,branch,removed,len(P)-1,flush=True)
    S=sc(P,P[-1].inv())
    ok,n=all_mod(M,p,t,S)
    assert ok and n==spl
