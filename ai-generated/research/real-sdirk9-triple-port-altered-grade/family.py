#!/usr/bin/env python3
import itertools
from fractions import Fraction

def pmul(f,g):
    z=f[0]*0
    h=[z]*(len(f)+len(g)-1)
    for i,x in enumerate(f):
        for j,y in enumerate(g): h[i+j]=h[i+j]+x*y
    return h
def peval(f,x):
    v=x*0
    for a in reversed(f): v=v*x+a
    return v
def shift(f,x):
    return peval([x*0]+[v/(i+1) for i,v in enumerate(f)],x)-peval(f,x)
def card(X,i):
    t=X[i];u=t*0+1
    f=[u]
    for j,x in enumerate(X):
        if i==j: continue
        k=u/(t-x)
        f=pmul(f,[-k*x,k])
    return f
def def_at(x): return 2*x-1-x*x/2

def front(a,d):
    one=a*0+1
    b=2*a-1
    eta=2*def_at(a)
    X=[one,a,b]
    f=-2*(a-1)*(3*a-5)/(a*a*a-7*a*a+10*a-2)
    g=[one/2,eta/2,def_at(b)+f*(a-1)]
    H=[one*0 for _ in range(3)]
    for i in range(3):
        for k,v in enumerate(card(X,i)): H[k]=H[k]+g[i]*v
    m=[d-1,d*d/2-d,d*d*d/3-d*d]
    k=2*(1+d+(d-1)/eta)/3
    g4=-sum(x*y for x,y in zip(H,m))/(H[1]+k*H[2]-(d-1)/eta)
    return X+[d],g+[g4],f,H,m,k

def gates(a,d,v):
    X,g,*_=front(a,d)
    weights=[shift(card(X,i),v) for i in range(4)]
    return (sum(x*y for x,y in zip(weights,g)),
            sum(x*y*t for x,y,t in zip(weights,g,X)))

class Jet:
    p=37
    def __init__(self,v,d=(0,0,0)):
        self.v=int(v)%self.p; self.d=tuple(int(x)%self.p for x in d)
    def __repr__(self): return repr((self.v,self.d))
    def __int__(self): return self.v
    def __add__(self,o):
        if not isinstance(o,Jet): o=Jet(o)
        return Jet(self.v+o.v,[a+b for a,b in zip(self.d,o.d)])
    __radd__=__add__
    def __sub__(self,o): return self+-o
    def __rsub__(self,o): return -self+o
    def __neg__(self): return Jet(-self.v,[-a for a in self.d])
    def __mul__(self,o):
        if not isinstance(o,Jet): o=Jet(o)
        return Jet(self.v*o.v,[self.v*b+o.v*a for a,b in zip(self.d,o.d)])
    __rmul__=__mul__
    def __truediv__(self,o):
        if not isinstance(o,Jet): o=Jet(o)
        w=pow(o.v,-1,self.p)
        return self*Jet(w,[-w*w*d for d in o.d])
    def __rtruediv__(self,o): return Jet(o)/self

def old_d(s,v):
    m0 = v*v/2-(s+1)*v+s
    m1 = v*v*v/3-(s/2+1)*v*v+s*v
    return (3*s*m0-(2*s+9)*m1)/(s*m0-3*m1)

def residue(p,s,v,w):
    Jet.p=p
    S,V=map(Jet,[s,v])
    d=old_d(S,V)
    a=(1+S)/2
    G,H=gates(Jet(a.v,(1,0,0)),Jet(d.v,(0,1,0)),Jet(V.v,(0,0,1)))
    Jac=(G.d[1]*H.d[2]-G.d[2]*H.d[1])%p
    movable=(G.d[0]*H.d[1]-G.d[1]*H.d[0])%p
    return int(a),int(d),G,H,Jac,movable

def main():
    from prior_field import seed, first_port, shifted_second, simple
    for p,s,v,w in [(13,9,6,2),(37,8,3,19),(43,26,16,39)]:
        simple(seed(p),s,p); simple(first_port(s,p),v,p)
        simple(shifted_second(s,v,p),w,p)
        try: R=residue(p,s,v,w)
        except (ArithmeticError,ValueError) as e: print(p,type(e).__name__,e);continue
        print(p,R)
        if R[-1] and R[-2] and R[2].v==R[3].v==0:
            print("certifying residue",p,s,v,w);break
    else: raise RuntimeError("No good residue")
if __name__=='__main__': main()
