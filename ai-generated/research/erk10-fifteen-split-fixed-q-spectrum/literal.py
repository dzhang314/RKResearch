"""Conditional literal fixed-q construction and independent tree replay."""
from fractions import Fraction as F
from spectrum import (val,mul,primitive,derivative,scale,nodes,require,Reject,distinct)

def lin(mat,rhs,k):
    rows=[list(row)+[b] for row,b in zip(mat,rhs)]
    for j in range(k):
        p=next((i for i in range(j,len(rows)) if rows[i][j]),None)
        require(p is not None,"rank_in_linear_builder")
        rows[j],rows[p]=rows[p],rows[j]
        a=rows[j][j]
        rows[j]=[u/a for u in rows[j]]
        for i in range(len(rows)):
            if i==j: continue
            a=rows[i][j]
            if a: rows[i]=[x-a*y for x,y in zip(rows[i],rows[j])]
    require(all(not row[-1] for row in rows[k:]),"inconsistent_literal_tap")
    return [r[-1] for r in rows[:k]]

def read(row,xs): return sum((u*v for u,v in zip(row,xs)),F(0))

def model(A,xs,f):
    return [read(r,[val(f,x) for x in xs])-val(primitive(f),x)
            for r,x in zip(A,xs)]

def fixed_t(r,v,dh):
    av=v**3*(3*v-4*r)/12
    bv=v**2*(3*r-2*v)/6
    den=bv-dh*r**3/6
    require(den,"no_other_root_for_fixed_q")
    return (-av-dh*r**4/12)/den

def host_system(r,v,z,dh,dg):
    t=fixed_t(r,v,dh)
    require(t,"other_root_zero")
    s,p=(2*r-t)/3,r*(2*r-t)/(3*t)
    P=nodes([F(0),r,t])
    require(distinct([F(0),s,p,r]) and val(P,s),"bad_old_fixed_q_guards")
    JP=primitive(P)
    require(val(JP,r),"JP_host_zero")
    f=[F(0),-2*r/3,F(1)]; Jf=primitive(f)
    av=val(Jf,v)/val(f,r)
    rs=val(JP,z)-val(JP,r)*dg
    if val(P,v): bv=rs/val(P,v)
    else:
        require(not rs,"third_host_law_degenerate")
        bv=F(0)
    az=(val(Jf,z)-bv*val(f,v))/val(f,r)
    return t,s,p,f,P,(av,az,bv)

def high_reverse(s,z,desired):
    ys,w,u=z["ys"],z["w"],z["u"]
    a,b,c,d,e,f,g,h,R=s["ordinary"]
    M,N,PZ,QZ,k=s["M"],s["N"],s["PZ"],s["QZ"],s["k"]
    mp=scale(derivative(M),F(1,4))
    Lu=[wi*val(mp,y)+(2-c/a)*(y-c)*ui for y,wi,ui in zip(ys,w,u)]
    Z=[wi*val(M,y)-(y-c)*val(N,y)*ui for y,wi,ui in zip(ys,w,u)]
    G=[(y-d)*l for y,l in zip(ys,Lu)]
    P=lambda Y:2*Y/3+k*(4*(b/a)/3-2)*(Y-1)
    D=3*(b/a)*k-2*(c/a)*k+c/a
    Q0=lambda Y:k*(Y-1)+(b/a)*k*(Y-1)*(Y-b/a)/D
    R0=lambda Y:Y*Y/2+k*((b/a)**2-2)*(Y-1)-(b/a)*k*((b/a)*k-(c/a)*k-c/a+2)*(Y-1)*(Y-b/a)/D
    ins=[]; out=[]
    for i,(y,wi,ui,zz,gg) in enumerate(zip(ys,w,u,Z,G)):
        tz=wi*val(PZ,y)+ui*val(QZ,y)
        ins.append([wi,y*wi,y*y*wi,y**3*wi,ui,y*ui,zz,gg])
        out.append([wi*y,wi*y*y/2+ui,wi*y**3/3+ui*a*P(y/a),
                    wi*y**4/4+ui*a*a*R0(y/a),
                    ui*k*(y-a),ui*a*a*Q0(y/a),
                    tz,((y-d)*zz-tz)/4])
    av,az,bv=desired
    K=[]
    for j in range(11):
        l=min(j,8)
        extra=[] if j<=8 else ([bv] if j==9 else [az,av])
        rhs=[out[j][k]-sum(q*ins[l+r][k] for r,q in enumerate(extra))
             for k in range(8)]
        mat=[[ins[i][k] for i in range(l)] for k in range(8)]
        row=lin(mat,rhs,l)+extra+[F(0)]*(11-j)
        K.append(row)
    assert all([read(row,[v[k] for v in ins]) for k in range(8)]==out[j]
               for j,row in enumerate(K))
    return K

def build_opening(r,t,s,p,E=F(1,8)):
    require(E and s and p and r and distinct([s,p,r]),"opening_distinct")
    alpha=p*p*(3*s-2*p)/s**3
    Aos=[[F(0)]*5 for _ in range(5)]
    Aos[1][0]=E
    Aos[2][1]=s*s/(2*E)
    Aos[2][0]=s-Aos[2][1]
    Aos[3][1]=alpha*Aos[2][1]
    Aos[3][2]=(p*p/2-E*Aos[3][1])/s
    Aos[3][0]=p-Aos[3][1]-Aos[3][2]
    q1,q2=lin([[s,p],[s*s,p*p]],[r*r/2,r**3/3],2)
    Aos[4][:4]=[r-q1-q2,F(0),q1,q2]
    mat=[[F(1),F(0),F(0)],[1-alpha,p-alpha*s,p*p-alpha*s*s],[F(1),r,r*r]]
    Pi=[lin(mat,rr,3) for rr in ([F(1),F(0),F(0)],
        [F(0),F(0),F(0)],[F(0),-alpha,F(0)],[F(0),F(1),F(0)],
        [F(0),F(0),F(1)])]
    assert all(v==0 for v in model([[F(0)]],[r],Pi[4]))
    assert val(Pi[4],r)==1
    assert all(val(Pi[j],r)==0 for j in range(4))
    assert all(Aos[4][j]==val(primitive(Pi[j]),r) for j in range(4))
    return Aos,Pi,[F(0),E,s,p,r]

def attach(B,xraw,old):
    Ao,Pi,co=old
    n=len(xraw)
    A=[row+[F(0)]*(n-1) for row in Ao]
    for i in range(1,n):
        oi=[val(primitive(f),xraw[i])
              -sum(B[i][j]*val(f,xraw[j]) for j in range(1,i)) for f in Pi]
        require(oi[-1]==B[i][0],"literal_old_host_mismatch")
        A.append(oi+list(B[i][1:]))
    xs=co+xraw[1:]
    assert all(sum(row,F(0))==x for row,x in zip(A,xs))
    return A,xs

def full(s,z,E=F(1,8)):
    ys=z["ys"]
    r,v,g=(1-y for y in ys[-1:-4:-1])
    t,c_s,c_p,F2,P,desired=host_system(r,v,g,z["eta"][9],z["eta"][8])
    K=high_reverse(s,z,desired)
    B=[[K[10-j][10-i] for j in range(11)] for i in range(11)]
    xr=[1-y for y in ys[::-1]]
    assert all(not x for x in model(B,xr,F2))
    JP_r=val(primitive(P),r)
    assert model(B,xr,P)==[-JP_r*q for q in z["eta"][::-1]]
    A,x=attach(B,xr,build_opening(r,t,c_s,c_p,E))
    w=[s["w"][F(1)]]+[F(0)]*4+z["w"][-2::-1]
    assert len(w)==len(A)==15
    return A,w,x

def rooted(A,xs,w=None,maxorder=10):
    n=len(A)
    sizes=[1]; fact=[1]; children=[()]
    prof=[[F(1)]*n]
    def gen(rem,start,m):
        if rem==0:
            yield ()
        else:
            for j in range(start,m):
                if sizes[j]>rem: break
                for v in gen(rem-sizes[j],j,m):
                    yield (j,)+v
    counts={1:1}
    for order in range(2,maxorder+1):
        m=len(sizes)
        for v in gen(order-1,0,m):
            q=[F(1)]*n
            fac=order
            for j in v:
                fac*=fact[j]
                q=[a*read(row,prof[j]) for a,row in zip(q,A)]
            sizes.append(order); children.append(v); fact.append(fac); prof.append(q)
        counts[order]=len(sizes)-m
    if w is not None:
        for i,v in enumerate(prof):
            err=read(w,v)-F(1,fact[i])
            if err: return (sizes[i],i,err),counts
    return None if w is not None else (sizes,fact,prof,children),counts

def selftest():
    r,t,s,p=map(F,["9/4","3/2","1","3/2"])
    v,z=F(2,3),F(5,4)
    F2=[F(0),-2*r/3,F(1)]
    P=nodes([F(0),r,t])
    dr=val(primitive(P),r)
    Dh=val(primitive(P),v)/dr
    bv=F(2,5)
    Dg=(val(primitive(P),z)-bv*val(P,v))/dr
    tt,ss,pp,ff,PP,(av,az,bv2)=host_system(r,v,z,Dh,Dg)
    assert [tt,ss,pp,ff,PP,bv2]==[t,s,p,F2,P,bv]
    B=[[F(0)]*3,[av,F(0),F(0)],[az,bv,F(0)]]
    A,x=attach(B,[r,v,z],build_opening(r,t,s,p))
    (size,fac,actual,children),cnt=rooted(A,x,maxorder=5)
    for m,g,vec in zip(size,fac,actual):
        # Output density is m times the reciprocal nominal stage factor.
        err=[vec[i]-x[i]**(m-1)*m/g for i in range(4,7)]
        if m<=4: assert all(q==0 for q in err)
        else: assert err==[err[0],Dh*err[0],Dg*err[0]]
    assert cnt=={1:1,2:1,3:2,4:4,5:9}
    assert any(q[4]!=x[4]**4*5/g for m,g,q in zip(size,fac,actual) if m==5)
    print("fixed-q literal 7-row fixture: physical decoder, all 17 low profiles, and size-five host line exact")

if __name__=="__main__":
    selftest()
