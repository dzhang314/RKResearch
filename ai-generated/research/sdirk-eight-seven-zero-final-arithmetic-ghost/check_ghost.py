"""Geometric check of dominant exact front-star diagonal factors."""
from itertools import permutations,combinations
from flint import fmpq_poly, fmpq, nmod_poly,fq_default_ctx,fq_default_poly_ctx
from sympy import primerange
from math import lcm
from ghost_projection import arrays,main,aGuard,sGuard126,sGuard198
Hinv=[[16,-120,240,-140],[-120,1200,-2700,1680],[240,-2700,6480,-4200],[-140,1680,-4200,2800]]
def mod(f,p):
 return nmod_poly([int(c.numerator)*pow(int(c.denominator),-1,p)%p for c in f.coeffs()],p)
def front(g,Fq,P,pp):
    z=Fq(0);one=Fq(1);x=P([0,1])
    stats=[0,0,0];bad=[]
    U=x;H=-2+U+4*U*U-U**3
    p0=[-g*g,2*g,-one/2]
    p1=[g*g,-2*g,one];p2=[g*g,-g,z]
    ps=[H*p0[i]+(3*U-2)*(p1[i]+U*p2[i]) for i in range(3)]
    ds=[P([g]),g*(1+U),g*(1+2*U)]
    r0,r1,r2=ds
    rs=[-r0*r1*r2,r0*r1+r0*r2+r1*r2,-r0-r1-r2,P([1])]
    def v(ar,t):return sum((c*t**j for j,c in enumerate(ar)),P([]))
    def jv(ar,t,k=0):return sum((c*t**(i+k+1)/Fq(i+k+1) for i,c in enumerate(ar)),P([]))
    def L4(t):return 70*t**4-140*t**3+90*t*t-20*t+1
    for a,b,c in permutations(pp):
        la,lb,lc=L4(a),L4(b),L4(c)
        pa,pb,pc=[v(ps,t) for t in (a,b,c)]
        ra,rb,rc=[v(rs,t) for t in (a,b,c)]
        ja,jb,jc=[jv(ps,t) for t in (a,b,c)]
        jta,jtb,jtc=[jv(ps,t,1) for t in (a,b,c)]
        jra,jrb,jrc=[jv(rs,t) for t in (a,b,c)]
        q0=ja-g*pa
        q1=la*(g*(b-a)*pb+a*jb-jtb)-lb*(g*a*pa-jta)
        q2=la*(pa*(g*rb-jrb)+(jb-g*pb)*ra)-lb*pa*(g*ra-jra)
        if max(q0.degree(),q1.degree())!=3:
            # A nonzero cleared graph cofactor rejects even without a unit u pivot.
            bx=[p0,p1,p2]
            fx=[jv(bb,a)-g*v(bb,a) for bb in bx]
            gx=[la*(g*(b-a)*v(bb,b)+a*jv(bb,b)-jv(bb,b,1))-lb*(g*a*v(bb,a)-jv(bb,a,1)) for bb in bx]
            d=fx[1]*gx[2]-fx[2]*gx[1]
            np=fx[2]*gx[0]-fx[0]*gx[2]
            nq=fx[0]*gx[1]-fx[1]*gx[0]
            if not (-2*np**3+nq*np*np+4*nq*nq*np-nq**3-(3*nq-2*np)*np*d).is_zero():
                stats[0]+=1
                continue
            return None
        stats[0]+=1
        cmn=q0.gcd(q1)
        if not cmn.degree():continue
        cmn=cmn.gcd(q2)
        stats[1]+=1
        if not cmn.degree():continue
        stats[2]+=1
        lc1=la*(jtc-g*c*pc)+(g*a*pa-jta)*lc
        lc2=la*(jrc-g*rc)+(g*ra-jra)*lc
        q3=pa*(la*b*pb*lc2-lc1*la*rb)-pb*(la*a*pa*lc2-lc1*la*ra)+(jc-g*pc)*(la*a*pa*la*rb-la*b*pb*la*ra)
        cmn=cmn.gcd(q3)
        if cmn.degree():bad.append(str(cmn))
    return stats,bad


from collections import Counter
reasons=Counter()
def fail(s):
 reasons[s]+=1
 return None

def test(g,Fq,P,data,tags,onlyguards):
 zero=Fq(0);one=Fq(1)
 if g==zero:return fail('gamma zero')
 x=P([0,1])
 vh=x**3-4*x*x-x+2
 vrs=vh.roots()
 if len(vrs)!=3 or any(m!=1 for _,m in vrs):return fail('rear gaps')
 vs=[v for v,m in vrs]
 def eva(n,v):
    vals=data[n];return vals[0]+v*vals[1]+v*v*vals[2]
 counts=[sum(eva(i,v)==zero for v in vs) for i in (0,4,5)]
 if counts[0]!=(1 if 'a' in tags else 0):return fail('leading count')
 if not onlyguards and (counts[1:]!=[int('disc' in tags),int('zero' in tags)]):
    return fail('outer degeneracy count')
 s_count=0
 if 's' in tags and 'a' not in tags:
    for v in vs:
      a0,b0,c0=[eva(i,v) for i in range(3)]
      if a0==zero:return fail('intersecting leading')
      ee=(a0*x*x+b0*x+c0).roots()
      if len(ee)!=2 or any(m!=1 for _,m in ee):return fail('S norm e split')
      al=(1+2*v-v*v)/(2*v*v);be=-one/(v*v)
      mm=[g**j*(al+be*(1+v)**j) for j in range(4)]
      p3=P([sum((Fq(w[j])*mm[j] for j in range(4)),zero) for w in Hinv])
      s_count+=sum(p3(g*e)==zero for e,_ in ee)
 out=[0,0,0];errors=[]
 for v in vs:
   A,B,C=[eva(i,v) for i in range(3)]
   sNorm=eva(3,v)
   # Subchart projected degree-zero from the exact ordered-pair norm.
   if not onlyguards and A!=zero and sNorm!=zero and eva(6,v)!=zero:
      continue
   if A==zero:
      if B==zero:return fail('linear pivot')
      es=[(-C/B,1)]
   else:
      es=(A*x*x+B*x+C).roots()
      if len(es)!=2 or any(m!=1 for _,m in es):return fail('e split')
   t=1+v
   kap=1+2*v-v*v
   alpha=kap/(2*v*v);beta=-one/(v*v)
   q=-kap*(one/3+v/2)/(2*v)
   FF=1+v-(3+2*v)*x+(2+v/2)*x*x-x**3/3
   WW,rem=divmod(FF*(alpha*(x-t)+beta*(x-1))+q,(x-1)*(x-t))
   assert rem.is_zero() and WW.degree()==2
   moment=[g**j*(alpha+beta*t**j) for j in range(4)]
   ss=[sum((Fq(w[j])*moment[j] for j in range(4)),zero) for w in Hinv]
   ll=[one/70,-Fq(2)/7,Fq(9)/7,-Fq(2),one]
   S=P(ss);L=P(ll)
   def cm(p,e):
      return sum((c*e**i/Fq(j-i) for j,c in enumerate(p) for i in range(j)),zero)
   skipD=0;skipL=0
   for e,_ in es:
      at=g*e
      f=g**3*FF(e);w=g*g*WW(e)
      l0=L(at);s0=S(at)
      ll0=f*cm(ll,at)
      ss0=f*cm(ss,at)+w
      if s0!=zero:
        psi=-l0/s0
        if ll0+psi*ss0!=zero:
           continue
      elif ss0!=zero:
        psi=-ll0/ss0
        if l0!=zero:continue
      elif 's' in tags and 'a' not in tags and s_count==1 and l0!=zero:
        # Exactly one zero of the exact monic e/v-scale norm with nonzero L.
        continue
      else:
        return fail('both psi pivots: L0=' + str(l0==zero) + ' C0=' + str(ll0==zero))
      if psi==zero and not onlyguards and 'zero' in tags and eva(5,v)==zero:
          skipL+=1
          continue
      p4=L+psi*S
      rr=p4.roots()
      if sum(m for _,m in rr)!=4:return fail('early splitting')
      if len(rr)<4:
          if not onlyguards and 'disc' in tags and eva(4,v)==zero:
             skipD+=1
             continue
          return fail('early repeated')
      pp=[one-z for z,m in rr if z!=at]
      assert len(pp)==3
      res=front(g,Fq,P,pp)
      if res is None:return fail('front unit')
      stats,bad=res
      out=[x+y for x,y in zip(out,stats)];errors+=bad
   if not onlyguards and 'disc' in tags and eva(4,v)==zero:
      if skipD!=1:return fail('unique repeated e')
   if not onlyguards and 'zero' in tags and eva(5,v)==zero:
      if skipL!=1:return fail('unique zero e')
 return out,errors


CERTS=(
    (main[1836],101,[64,1],set(),False,[12,1,0]),
    (main[144],101,[79,1],{'disc'},False,[6,0,0]),
    (main[36],101,[46,1],{'zero'},False,[6,0,0]),
    (aGuard,101,[96,1],{'a'},True,[30,0,0]),
    (sGuard198,101,[50,1],{'s'},True,[36,0,0]),
    (sGuard126,101,[16,94,1],{'s'},True,[30,0,0]),
)
for f,pr,loc,tags,guards,expected in CERTS:
    pf=nmod_poly(loc,pr)
    fp=mod(f,pr)
    vp=nmod_poly([2,-1,-4,1],pr)
    assert fp.degree()==f.degree() and fp%pf==0 and fp.derivative().gcd(pf).degree()==0
    assert sorted((x.degree(),j) for x,j in pf.factor()[1])==[(pf.degree(),1)]
    assert vp.derivative().gcd(vp).degree()==0
    vdeg=lcm(*(fa.degree() for fa,e in vp.factor()[1]))
    G=fq_default_ctx(pr,12*lcm(pf.degree(),vdeg),var='a')
    assert G.modulus().is_irreducible()
    P=fq_default_poly_ctx(G)
    gs=P(loc).roots()
    assert len(gs)==pf.degree() and all(m==1 for _,m in gs)
    md=[[mod(a,pr)%pf for a in cluster] for cluster in arrays]
    for gamma,_ in gs:
        data=[[P([int(k) for k in f.coeffs()])(gamma) for f in co] for co in md]
        st,bad=test(gamma,G,P,data,tags,guards)
        assert st==expected and not bad
    print('fixed ghost fibre',f.degree(),tags,pr,loc,'directed pairs',expected,flush=True)
