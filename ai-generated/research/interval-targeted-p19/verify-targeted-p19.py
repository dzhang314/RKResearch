#!/usr/bin/env python3
"""One prescribed reachable elliptic point; dyadic and q-local proof, no scan."""
import contextlib
import io
import runpy
import sys
from pathlib import Path

here=Path(__file__).resolve().parent
if len(sys.argv)==3:
    continuation,pencil=map(Path,sys.argv[1:])
else:
    continuation=here.parent/"interval-component-continuation/verify-continuation.py"
    pencil=here/"verify-interval-pencil-768.py"
saved_argv=sys.argv[:]
try:
    sys.argv=[str(continuation),str(pencil)]
    with contextlib.redirect_stdout(io.StringIO()):
        E=runpy.run_path(str(continuation))
finally:
    sys.argv=saved_argv

I,F,Q=E["I"],E["F"],E["Q"]
data,nodal,moment,params=E["data"],E["nodal"],E["moment"],E["params"]
ec_cert,exact_checks,real_window=E["ec_cert"],E["exact_checks"],E["real_window"]
triple=E["triple"]
labels,xs=E["labels"],E["xs"]
labF,xsF=E["labmod"],E["xmod"]


def need(b,why):
    if not b:
        raise AssertionError(why)


def less(x,y):
    return x.u<y.l


def buffered_pair(xs,labels):
    h,C=data(xs,I)
    o,z=I.c(1),I.c(0)
    entries=sorted(zip(labels,xs,C),key=lambda t:t[1].l)
    need(all(less(x[1],y[1]) for x,y in zip(entries,entries[1:])), "exact distinct sort")
    left=best=None
    for label,x,c in entries:
        if label in ("m3","p3"):
            continue
        need(x.between(z,o),"interior prefix buffers")
        q=h/c
        need(q.positive() or q.negative(),"signed ratio")
        rho=(-q if q.negative() else q)/(x*(o-x))
        if q.negative():
            r=x+rho
            if left is None or less(r,left[1]):
                left=(label,r)
            else:
                need(less(left[1],r),"resolve ordered left-buffer comparison")
        elif left is not None:
            s=x-rho-left[1]
            if best is None or less(best[2],s):
                best=(left[0],label,s)
            else:
                need(less(s,best[2]),"resolve best additive slack")
    need(best is not None and best[2].positive(),"positive best interval margin")
    return best


def model(R,a,b):
    k,o=R.c,R.c(1)
    alpha,beta=b-a-o,a*(k(2)*b+o)
    eta,theta=k(4)*a*b*(a-b),-k(4)*a*a*b*(b+o)
    return alpha,beta,eta,alpha*alpha-k(4)*beta,k(2)*alpha*eta-k(4)*theta,eta*eta


def times(R,n,A,B,D):
    """Left-to-right exact binary group law, on the open affine formulas."""
    k=R.c
    chooses=bin(n)[3:]
    count=[0,0]
    px,py=D
    for digit in chooses:
        slope=(k(3)*px*px+k(2)*A*px+B)/(k(2)*py)
        xx=slope*slope-A-k(2)*px
        yy=slope*(px-xx)-py
        px,py=xx,yy
        count[0]+=1
        if digit=="1":
            x,y=D
            slope=(py-y)/(px-x)
            xx=slope*slope-A-px-x
            yy=slope*(px-xx)-py
            px,py=xx,yy
            count[1]+=1
    return (px,py),tuple(count)


def split(R,u,v,d,a,b,m):
    k,o=R.c,R.c(1)
    alpha,beta,eta,A,B,C=model(R,a,b)
    (X,Y),counts=times(R,abs(m),A,B,(k(0),-eta if m>0 else eta))
    if R is F:
        need(Y*Y==X**3+A*X*X+B*X+C,"exact affine point on E modulo q")
    x=(Y-alpha*X-eta)/(k(2)*X)
    U=X/k(2)-(x*x+alpha*x+beta)
    L=x*x+(a+b-o)*x-a
    y=(U+L)/(k(2)*x*(x-o))
    s=x+a/x+b/(x-o)
    z=o+s-x-y
    if R is F:
        need(x*y*z==a and (x-o)*(y-o)*(z-o)==-b,"pencil product cross checks")
    return [u+d*x,u+d*y,u+d*z],u+d*s,(X,Y),counts


def replace_named(labels,xs,new,ul,vl,j):
    keep=[i for i,l in enumerate(labels) if l not in (ul,vl)]
    return [labels[i] for i in keep]+[f"{j}{c}" for c in "abc"],[xs[i] for i in keep]+new


need(E["last_verified"]==18 and labels==labF and exact_checks(F,xsF)==844394583,"p18 provider pin")
ul,vl,slack=buffered_pair(xs,labels)
need((ul,vl)==("7b","6a"),"fixed chosen interior pair")
u,v,d,a,b=params(xs,labels,I,ul,vl)
uF,vF,dF,aF,bF=params(xsF,labF,F,ul,vl)
ru,rv=d*d*a,d*d*b
f0,f1=real_window(I,u,v,ru,rv)
h,_=data(xs,I)
t0=moment(nodal(xs,I),I,3)/h-u-v
need(ru.negative() and rv.negative() and (f1-f0).positive() and t0.between(f0,f1),
     "all-split reachable window and small-defect room")
print("Pinned order 18 / 16 interval sites; positive best-buffer pair:",ul,vl,slack.bracket())
print("First pair width and zero-defect parameter:",(f1-f0).bracket(),t0.bracket())
print("First pair exact nontorsion model and multiples mod q:",ec_cert(F,aF,bF))
rf=triple(I,u,d,a,b)
need(rf[0].negative(),"rank-free route is demonstrably exterior")
print("Rank-free triple enclosures (10^6 scaled):",[x.bracket() for x in rf])
# Finite phase planning chooses j=13 at approximant 129/137 of phi(2D).
# The actual certificate below does not trust that approximation as a proof.
k=13*pow(129,-1,137)%137
need(k==84,"frozen one congruence, no alternative group point")
m=2*k
new,tau,P,moves=split(I,u,v,d,a,b,m)
newF,tauF,PF,movesF=split(F,uF,vF,dF,aF,bF,m)
need(moves==movesF==(7,2),"literal one group addition chain")
need(tau.between(I.c(1,2),I.c(27,50)) and all(x.between(I.c(0),I.c(1)) for x in new),
     "direct exact inside-component physical enclosures for one targeted point")
need(less(v,new[0]) and less(u,new[1]) and less(new[1],v) and less(new[2],u),
     "ordered tuple is (right,middle,left)")
print(f"One targeted [{m}]D, binary chain doubles/adds={moves}; E mod q:",tuple(x.x for x in PF))
print("Actual physical tau and sorted-branch triple (right,middle,left):",tau.bracket(),[x.bracket() for x in new])
l19,x19=replace_named(labels,xs,new,ul,vl,9)
l19F,x19F=replace_named(labF,xsF,newF,ul,vl,9)
need(l19==l19F and len(l19)==17 and all(l in l19 for l in ("m3","p3")),"width and endpoint labels")
h19=exact_checks(F,x19F)
need(h19==1698450493,"literal actual first failure")
print("PASS exact interval order 19 / 17 contributing sites; first defect mod q =",h19)
ratio=data(x19,I)[0]/h
need(ratio.positive(),"chosen side of zero defect")
p2=("9b","9a")  # middle,right
i2=params(x19,l19,I,*p2)
m2=params(x19F,l19F,F,*p2)
u2,v2,d2,a2,b2=i2
ru2,rv2=d2*d2*a2,d2*d2*b2
f02,f12=real_window(I,u2,v2,ru2,rv2)
need(ru2.negative() and rv2.negative() and (f12-f02).positive(),"actual next all-split window")
print("Next adjacent pair",p2,"delta, window:",ratio.bracket(),f02.bracket(),f12.bracket())
print("Actual next pair nontorsion model and multiples mod q:",ec_cert(F,m2[3],m2[4]))
