"""Exact generic A(1)≠0 reciprocal minors on a fixed c,g,R slice."""
from fractions import Fraction as F
from argparse import ArgumentParser
from itertools import combinations
import sympy as S
from sympy.polys.matrices import DomainMatrix
from spectrum import nodes,moment,require,Reject
from unified import tail,matrix

t=S.Symbol("tau")
ring=S.QQ.poly_ring(t)
q=lambda a:ring.convert(S.Rational(a.numerator,a.denominator))
x=ring.gens[0]
Z=ring.zero

def multiply(a,b):
    c=[Z]*(len(a)+len(b)-1)
    for i,u in enumerate(a):
        for j,v in enumerate(b): c[i+j]+=u*v
    return c

def scheme(c,g,R):
    data=tail(c,g,R)
    require(not data["origin"],"A(1)=0 requires zero-score branch analysis")
    A=matrix(data,F(0))
    B=matrix(data,F(1))
    rows=[[q(a)+x*q(b-a) for a,b in zip(l0,l1)] for l0,l1 in zip(A,B)]
    u,v,w=rows[0]; j,k,l=rows[2]
    Delta=u*k-v*j
    require(Delta,"head_pivot_identically_zero")
    Nu_s=v*l-w*k
    Nu_p=w*j-u*l
    D7=multiply(multiply([Nu_p,-Nu_s,Delta],[x,-q(c)+q(data["omega"])*x,ring.one]),
                [q(a) for a in data["T"]])
    assert D7[-1]==Delta and len(D7)==8
    p3=nodes([F(0),F(1),c])
    mu=[sum((D7[j]*q(moment(p3,j-1-i)) for j in range(i+1,8)),Z)
        for i in range(7)]
    col=[mu]
    for j in range(4):
        prev=col[-1]
        nxt=[Delta*v-prev[-1]*w for v,w in zip([Z]+prev,D7)]
        assert not nxt[-1]
        col.append(nxt[:-1])
    a,b=data["k"],data["ell"]
    col.append([Z,q(a*a),q(2*a*b),q(b*b),Z,Z,Z])
    data["Delta"]=Delta
    data["D7num"]=D7
    return data,col

def scalar_slice(c,g,R):
    data,cols=scheme(c,g,R)
    G=ring.zero
    deg=[]
    for ii in range(7):
        rows=[[col[j] for col in cols] for j in range(7) if j!=ii]
        cross=DomainMatrix(rows,(6,6),ring).det()
        G=ring.gcd(G,cross)
        deg.append(cross.degree() if cross else None)
    require(G,"all minors identically zero")
    Del=data["Delta"]*x
    g=G
    while True:
        div=ring.gcd(g,Del)
        if div.degree()==0:break
        g=ring.exquo(g,div)
    gp=S.Poly(ring.to_sympy(g),t,domain=S.QQ)
    r=gp.ground_roots()
    return data,deg,G,gp,r

def main():
    ap=ArgumentParser()
    ap.add_argument("--c",default="1/2");ap.add_argument("--g",default="2/3");ap.add_argument("--R",default="1/4")
    args=ap.parse_args()
    c,g,R=map(F,[args.c,args.g,args.R])
    d,ds,G,h,r=scalar_slice(c,g,R)
    print("fixed outer tail:",c,g,R," h,f=",d["h"],d["f"])
    print("minor degrees:",ds)
    print("gcd degree before excluding pivot and tau=0:",G.degree())
    print("remaining exact primitive polynomial:",h.clear_denoms()[1].primitive()[1].as_expr())
    print("remaining rational roots:",r)

if __name__=="__main__": main()
