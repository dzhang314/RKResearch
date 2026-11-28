import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'dirk11-thirteen-fourth-clean'))
from replay_mod101 import *
F60,(c0,c1),j5=receipt()
T=F.start(103,F60);u=-ev(c0,T)/ev(c1,T);v=u*T;w=u*T*(1+T)/(4*T-1-T*T)
R,k,f,b0,b1,h,pp,qq,dv,z=geometry(u,v,w)
for s in R:
    a=dot(taps(R,b1(s)),[q**4 for q in R])-b1(s)[3]
    a.inv()
print('three repeated-column degree-four guards all units in rank 60',flush=True)
la=-J5(u)/J4(u);s=-(F(j5.nth(4))+42*la)/132-u-v-w
q=(F(j5.nth(3))-84*la)/132-u*v-u*w-v*w-(u+v+w)*s
A=Q((s,q),F(0),F(1));u,v,w,b=cast(A,u,v,w,s-A)
poly,opt=optional4(u,v,w,A)
p2,p1,p0=poly
C=Q((-p1/p2,p0/p2),A*0,A*0+1)
u,v,w,a,b=cast(C,u,v,w,A,b);ka=C
R,k,f,b0,b1,h,pp,qq,dv,z=geometry(u,v,w)
R4=R+[a]; k4=k+[ka];t4=taps(R4,[r+ka*l for r,l in zip(b0(a),b1(a))])
pa=dot(t4,[r*x for r,x in zip(R4,k4)])/ka;qa=(dot(t4,[r**5 for r in R4])-a**6/6)/ka
dh=h(a)/ka-lag(a,R,dv);chi=(qa-lag(a,R,qq))/dh
rho2=lambda s:lag(s,R,qq)-chi*lag(s,R,dv)
for s in R4:
    a=dot(taps(R4,b1(s)),[r**5 for r in R4])-rho2(s)
    a.inv()
print('four repeated-column degree-five guards all units in rank 240',flush=True)
print('Checked primitive residue inverses:',F.inverse_count)
