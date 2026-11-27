from flint import nmod_poly
from math import prod
p=997; a,b,diag,silent=89,337,591,470
R=nmod_poly([0,1],p)
iv=lambda x:pow(int(x)%p,-1,p)
M=lambda x:int(x)%p
j=lambda f:nmod_poly([0]+[M(f[i]*iv(i+1)) for i in range(len(f))],p)
gauss=(70*R**4-140*R**3+90*R**2-20*R+1)*iv(70)
r=gauss//((R-a)*(R-b))
assert gauss%((R-a)*(R-b))==0
rt=int(r(diag));rr=int(r(1-diag))
gamma2=diag*diag*iv(2)%p
g=lambda c:gamma2*int(r(c))*iv(rt)%p
def c3(u,w,d):
    r3=M(2*u*(3*u-2)*iv(-2+u+4*u*u-u**3)) if d else 0
    return ([1,1+u,1+w],[iv(2),M((1+2*u-u*u)*iv(2)),M((1+2*w-w*w+2*r3*u)*iv(2))])
def gate(T,u):
    k=M(1+2*u-u*u)
    D=4*iv(3)+(2*(k+1)*iv(3*k))*(R-1)
    L=1+(R-1)*iv(k)
    F=j(T)-T
    G=1-L+int(T[1])+int(T[2])*D
    return F,G
def interp(sites,vals):
    ans=nmod_poly([],p)
    for i,x in enumerate(sites):
        v=prod((R-y for j,y in enumerate(sites) if j!=i),start=nmod_poly([1],p))
        ans+=M(vals[i]*iv(v(x)))*v
    return ans
A,G=c3(543,2*543,True)
B,H=c3(137,274,True)
X=[M(diag*x) for x in A]
Y=[M(1-diag*x) for x in B]
assert X[1]==silent
assert [(x,g(x)) for i,x in enumerate(X) if i!=1]==[(x,M(diag*diag*G[i])) for i,x in enumerate(X) if i!=1]
for br in ('left','right'):
    u=543 if br=='left' else 137
    T=interp(A,G) if br=='left' else interp(B,H)
    Ft,Gt=gate(T,u)
    gg=r(diag*R)*iv(2*rt) if br=='left' else r(1-diag*R)*iv(2*rr)
    print(br,'actual normalized first3',A if br=='left' else B,'fourth poly',Ft+Gt*gg,'roots',(Ft+Gt*gg).roots(),flush=True)
    if br=='left':
        A4=[M(x*diag) for x,k in (Ft+Gt*gg).roots() if M(x) not in set(map(M,[A[0],A[2]]))]
        assert A4==[562]
    else:
        assert (Ft+Gt*gg).degree()==3
        assert {int(x) for x,e in (Ft+Gt*gg).roots()}==set(B)
        assert Ft(M((1-b)*iv(diag)))==0
ca=gauss//(R-a);cb=gauss//(R-b)
ba=M(j(ca)(1)*iv(ca(a)));bb=M(j(cb)(1)*iv(cb(b)))
I=lambda f:M(j(f)(1)-ba*f(a)-bb*f(b))
print('known corners c',X,Y,A4,'zero weights',ba,bb)
for x4 in A4:
    pegs=[X[0],X[2],x4,*Y]
    Q=prod((R-x for x in pegs),start=nmod_poly([1],p))
    print('six actual pegs',pegs,'nodal pair',I(Q),I(R*Q),flush=True)
    assert (I(Q),I(R*Q))==(572,968)
    site=M(I(R*Q)*iv(I(Q)))
    print('last graph clock',site,'g',g(site),flush=True)
    assert site==922 and all(x!=site for x in pegs)
    active=pegs+[site]
    weights=[]
    for i,x in enumerate(active):
        z=prod((R-y for j,y in enumerate(active) if j!=i),start=nmod_poly([1],p))
        weights.append(M(I(z)*iv(z(x))))
    assert weights==[868,467,699,986,273,29,168]


for q0,last,mask,diff in [
    ([492,746,665,771,659,0],89,[0,0,0,0,1],166),
    ([83,981,98,355,328,0],922,[739,0,2,505,1],650)
]:
    cc=[591,470,349,562,last]
    gg=[664,97,603,835,0 if last==89 else 672]
    V=[lambda c,g:1,lambda c,g:c,lambda c,g:c*c,lambda c,g:c**3,
       lambda c,g:g,lambda c,g:c*g]
    vv=[M(sum(s*val(c,g) for s,val in zip(q0,V))) for c,g in zip(cc,gg)]
    assert vv==[0,0,0,0,1]
    rhs=[M(diag*vv[i]-sum(q0[k]*pow(c,k+1,p)*iv(k+1) for k in range(4)))
         for i,c in enumerate(cc)]
    for j in (0,1,2,4):
        assert sum(s*g*V[j](c,g) for s,c,g in zip(mask,cc,gg))%p==0
    assert sum(s*v for s,v in zip(mask,rhs))%p==diff!=0
print('F997: both all-moment placements fail actual row-five rank')
