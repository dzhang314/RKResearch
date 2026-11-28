#include <array>
#include <algorithm>
#include <cassert>
#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

template<int P> struct Census {
  using I = long long;
  static constexpr int maxd=16;
  struct Poly { std::array<int,maxd> v{}; int n=0; };
  struct Pt { int n,d; };
  struct Hp { int s,p,q; };
  struct Branch {
    bool exist=false, affineDistinct=false, projectiveDistinct=false, flat=false,
      pole=false, collision=false, ambiguous=false, loss=false, rankdrop=false,
      firstFull=false, regular=false;
    I tuples=0;
    void collect(const Branch& b) {
      exist|=b.exist; affineDistinct|=b.affineDistinct;
      projectiveDistinct|=b.projectiveDistinct; flat|=b.flat;
      pole|=b.pole; collision|=b.collision; ambiguous|=b.ambiguous;
      loss|=b.loss; rankdrop|=b.rankdrop; firstFull|=b.firstFull;
      regular|=b.regular;tuples+=b.tuples;
    }
  };
  struct Status { Branch generic, origin; };
  std::array<int,P> inv{},sq{};
  std::array<I,30> count{};
  std::vector<Pt> points;
  std::vector<Hp> heads;
  std::vector<std::array<int,8>> firstRegular,firstOrigin;
  bool emitRegular=false, emitMap=false;
  static int z(int x) { x%=P; return x<0?x+P:x; }
  static int add(int a,int b) { return z(a+b); }
  static int mul(int a,int b) { return z(a*b); }
  static int pow(int a,int n) { int h=1; while(n--) h=mul(h,a); return h; }
  static bool nz(const Poly& f) { for(int i=0;i<=f.n;++i) if(f.v[i])return true;return false; }
  Poly pol(std::initializer_list<int> a) const {
    Poly x; x.n=int(a.size())-1;
    int j=0; for(int b:a)x.v[j++]=z(b);
    return x;
  }
  Poly sc(Poly a,int s) const { for(int i=0;i<=a.n;++i)a.v[i]=mul(a.v[i],s);return a; }
  Poly plus(Poly a,const Poly& b) const {
    a.n=std::max(a.n,b.n);
    for(int i=0;i<=b.n;++i)a.v[i]=add(a.v[i],b.v[i]);
    return a;
  }
  Poly prod(const Poly& a,const Poly& b) const {
    Poly w; w.n=a.n+b.n; assert(w.n<maxd);
    for(int i=0;i<=a.n;++i)if(a.v[i])
      for(int j=0;j<=b.n;++j)w.v[i+j]=add(w.v[i+j],mul(a.v[i],b.v[j]));
    return w;
  }
  int mom(const Poly& a,int j=0) const {
    int x=0;assert(a.n+j+1<P);
    for(int i=0;i<=a.n;++i)x=add(x,mul(a.v[i],inv[i+j+1]));
    return x;
  }
  Poly J(const Poly& a) const {
    Poly b; b.n=a.n+1;
    for(int i=0;i<=a.n;++i)b.v[i+1]=mul(a.v[i],inv[i+1]);
    return b;
  }
  Poly point(int p) const {return pol({-points[p].n,points[p].d});}
  int hom(const Poly& a,int pt,int deg) const {
    int N=points[pt].n,D=points[pt].d;
    int nr=0;
    for(int j=0;j<=std::min(deg,a.n);++j)nr=add(nr,mul(a.v[j],mul(pow(N,j),pow(D,deg-j))));
    return nr;
  }
  int id(int a,int b) const {
    a=z(a);b=z(b);
    return b ? mul(a,inv[b]) : a ? P : -1;
  }
  std::vector<int> options(int a,int b) const {
    int j=id(a,b);
    if(j>=0)return {j};
    std::vector<int> r; for(int i=0;i<=P;++i)r.push_back(i);return r;
  }
  Poly V(Pt c) const {
    int A=c.n,B=c.d;
    auto h=[&](int k0,int k1,int k2,int k3) {
      return z(k0*pow(A,3)+k1*mul(pow(A,2),B)+k2*mul(A,pow(B,2))+k3*pow(B,3));
    };
    return pol({h(75,-108,45,-5),h(-525,732,-291,30),
                h(1050,-1428,549,-54),h(-630,840,-315,30)});
  }
  int omega(Pt c) const {
    int A=c.n,B=c.d;
    return z(210*pow(A,3)-336*mul(pow(A,2),B)+168*mul(A,pow(B,2))-28*pow(B,3));
  }
  int rank(std::array<std::array<int,7>,7> a,int cols) const {
    int r=0;
    for(int j=0;j<cols;++j) {
      int k=r; while(k<7&&!a[k][j])++k;
      if(k==7)continue;
      std::swap(a[r],a[k]); int u=inv[a[r][j]];
      for(int i=r+1;i<7;++i) if(a[i][j]) {
        int g=mul(a[i][j],u);
        for(int l=j+1;l<cols;++l)a[i][l]=z(a[i][l]-g*a[r][l]);
        a[i][j]=0;
      }
      ++r;
    }
    return r;
  }
  bool split(const Poly& a) const {
    return sq[z(a.v[1]*a.v[1]-4*a.v[0]*a.v[2])];
  }
  std::vector<int> qr(const Poly& a) const {
    std::vector<int> r;
    for(int i=0;i<=P;++i) if(!hom(a,i,2))r.push_back(i);
    if(r.size()==1)r.push_back(r[0]);
    assert(r.size()==2);
    return r;
  }
  static bool geomDistinct(const std::vector<int>& x) {
    auto z=x;std::sort(z.begin(),z.end());return std::adjacent_find(z.begin(),z.end())==z.end();
  }
  static bool geomFinite(const std::vector<int>& x) {
    return std::find(x.begin(),x.end(),P)==x.end();
  }
  std::vector<Hp> headPoints(const std::array<int,3>& a,const std::array<int,3>& b,int& ra) const {
    std::array<int,3> c={z(a[1]*b[2]-a[2]*b[1]),z(a[2]*b[0]-a[0]*b[2]),z(a[0]*b[1]-a[1]*b[0])};
    if(c[0]||c[1]||c[2]) {
      ra=2;
      return {{c[0],c[1],c[2]}};
    }
    auto p=(a[0]||a[1]||a[2])?a:b;
    if(!(p[0]||p[1]||p[2])){ra=0;return heads;}
    ra=1;std::vector<Hp> v;
    for(auto h:heads)if(!z(p[0]*h.s+p[1]*h.p+p[2]*h.q))v.push_back(h);
    return v;
  }
  std::array<Poly,5> cols(const Poly& D,const Poly& p3) const {
    // Homogeneous replacement for all Δⁱ-scaled remainders.
    std::array<Poly,5> f;
    for(int j=0;j<5;++j) {
      f[j].n=6;
      for(int i=0;i<=6;++i)
        for(int z0=i+1;z0<=7;++z0)
          f[j].v[i]=add(f[j].v[i],mul(D.v[z0],mom(p3,j+z0-1-i)));
      for(int j0=0;j0<j;++j0)
        f[j].v[j-1-j0]=z(f[j].v[j-1-j0]-mom(prod(p3,D),j0));
    }
    return f;
  }
  bool alignment(const Poly& mu,const Poly& V0,const Poly& aff,std::array<int,3> fs) const {
    int A[3],B[3];
    for(int j=0;j<3;++j) {
      auto q=points[fs[j]];
      A[j]=mul(hom(mu,fs[j],6),hom(V0,fs[j],3));
      B[j]=mul(q.n,mul(hom(aff,fs[j],1),pow(q.d,7)));
    }
    return !z(A[0]*B[1]-A[1]*B[0])&&!z(A[0]*B[2]-A[2]*B[0])&&!z(A[1]*B[2]-A[2]*B[1]);
  }

  std::array<int,2> phase(const Poly& mu,const Poly& v,const Poly& a,
                          const Poly& rt,const std::array<int,7>& zs,
                          bool ge,bool orig) const {
    std::array<std::array<int,7>,7> m{}, n{};
    for(int i=0;i<7;++i) {
      int q=zs[i];
      auto pn=points[q];
      int muv=hom(mu,q,6), ah=hom(a,q,1);
      // Every row has homogeneous degree ten in the site coordinate.
      m[i][0]=n[i][0]=mul(muv,hom(rt,q,4));
      m[i][1]=mul(pn.n,mul(mul(ah,ah),pow(pn.d,7)));
      m[i][2]=n[i][3]=mul(muv,mul(ah,hom(v,q,3)));
      n[i][1]=mul(mul(pn.n,z(pn.d-pn.n)),pow(pn.d,8));
      n[i][2]=mul(mul(mul(pn.n,pn.n),z(pn.d-pn.n)),pow(pn.d,7));
    }
    return {(!ge||rank(m,3)<=2),(!orig||rank(n,4)<=3)};
  }
  Status choices(int ci,int gi,int ri,int hi,int fi,bool amb) {
    const Pt Pc=points[ci], Pr=points[ri];
    int C=Pc.n,D=Pc.d,R=Pr.n,RD=Pr.d,D2=mul(D,D),D3=mul(D2,D),D4=mul(D3,D);
    Poly xc=point(ci),xr=point(ri),xg=point(gi),xh=point(hi),xf=point(fi);
    Poly T3=prod(prod(xf,xg),xh);
    Poly S4=prod(prod(pol({1,-1}),xg),prod(xh,xr));
    Poly p3=prod(pol({0,-1,1}),xc);
    Poly vcalc=V(Pc);
    int om=omega(Pc);
    int ks=mom(prod(prod(p3,xc),prod(xr,T3)));
    int js=mom(prod(prod(prod(S4,xf),pol({0,1})),prod(xc,pol({D3,om}))));
    Poly ah=pol({mul(mul(C,D2),ks),z(C*js-2*D3*ks)});
    bool flatOrigin=!add(ah.v[0],ah.v[1]);
    bool lostA=!nz(ah);
    Poly phBase=prod(prod(pol({-1,1}),xc),plus(sc(vcalc,T3.v[0]),sc(T3,z(-vcalc.v[0]))));
    Poly eb=prod(p3,T3);
    Poly rT=prod(xr,T3);
    std::array<Poly,2> deBases={pol({0,-mul(C,D2),D3}),pol({D3,om,0})};
    // Avoid redoing the short formal moments at every tau.
    std::array<int,2> E0{},E1{},L0{},L1{},L2{};
    for(int j=0;j<2;++j) {
      auto ep=prod(eb,deBases[j]), ph=prod(phBase,deBases[j]);
      E0[j]=mom(ep);E1[j]=mom(ep,1);
      L0[j]=mom(ph);L1[j]=mom(ph,1);L2[j]=mom(ph,2);
    }
    Status res;
    for(int ti=0;ti<=P;++ti) {
      auto T=points[ti].n,U=points[ti].d;
      Poly de=plus(sc(deBases[0],U),sc(deBases[1],T));
      if(!split(de))continue;
      bool lostDe=!nz(de);
      int E=add(mul(U,E0[0]),mul(T,E0[1]));
      int G=add(mul(U,E1[0]),mul(T,E1[1]));
      // Homogeneous first row; every term has the same scale over Q.
      std::array<int,3> row={
        z(E*R*mul(C,C)-2*T*C*mul(D3,ks)),
        z(-E*R*mul(C,D)-E*RD*mul(C,C)+G*RD*mul(C,D)+4*T*mul(D4,ks)-T*C*mul(D,js)),
        z(-G*R*mul(C,C)+T*mul(C,C)*mul(D2,ks))
      };
      std::array<int,3> card={
        z(-U*L1[0]-T*L1[1]),z(U*L0[0]+T*L0[1]),z(U*L2[0]+T*L2[1])};
      int rr;
      auto ho=headPoints(row,card,rr);
      std::vector<int> dr;
      if(!lostDe)dr=qr(de);
      Poly dt=prod(de,T3);
      for(const auto& sh:ho){
        Poly ab=pol({sh.p,-sh.s,sh.q});
        if(!split(ab))continue;
        ++count[16]; // all projective scalar skeletons
        Poly den=prod(ab,dt);
        auto cas=cols(den,p3);
        bool ge=alignment(cas[0],vcalc,ah,{fi,gi,hi});
        bool orr=flatOrigin;
        if(ge||orr){
          std::array<std::array<int,7>,7> ma{};
          for(int j=0;j<5;++j)for(int i=0;i<7;++i)ma[i][j]=cas[j].v[i];
          int rank5=rank(ma,5);
          if(ge && rank5==5) {
            ma[1][5]=mul(ah.v[0],ah.v[0]);
            ma[2][5]=mul(2,mul(ah.v[0],ah.v[1]));
            ma[3][5]=mul(ah.v[1],ah.v[1]);
            ge=rank(ma,6)<=5;
          }
          if(orr && rank5==5) {
            ma[1][5]=1;ma[2][5]=P-1;ma[3][5]=0;
            ma[2][6]=1;ma[3][6]=P-1;
            orr=rank(ma,7)<=6;
          }
          if(ge||orr) {
            auto ar=qr(ab);
            count[17]+=ge; count[18]+=orr;
            if(!lostDe) {
              auto ok=phase(cas[0],vcalc,ah,rT,
                            {ar[0],ar[1],dr[0],dr[1],fi,gi,hi},ge,orr);
              ge=ge&&ok[0];orr=orr&&ok[1];
            }
            if(!ge&&!orr)continue;
            std::vector<int> sites={0,1,ci,gi,ri,hi,fi,ar[0],ar[1]};
            if(!lostDe){sites.push_back(dr[0]);sites.push_back(dr[1]);}
            bool gd=!lostDe&&geomDistinct(sites);
            bool gf=geomFinite(sites);
            Branch v;v.exist=true;v.tuples=1;v.flat=!ti;
            v.projectiveDistinct=gd;v.affineDistinct=gd&&gf;
            v.pole=!gf||ti==P||!sh.q||!U;
            v.collision=!gd;v.ambiguous=amb;v.loss=lostA||lostDe;
            v.rankdrop=rr<2;v.firstFull=rank5==5;
            v.regular=v.affineDistinct&&!v.loss&&!v.ambiguous&&!v.rankdrop&&v.firstFull;
            if(ge)res.generic.collect(v);
            if(orr)res.origin.collect(v);
            if(emitRegular&&v.affineDistinct)
              std::cout<<"CANDIDATE "<<ci<<" "<<gi<<" "<<ri<<" "<<hi<<" "<<fi
                <<" "<<ti<<" "<<ar[0]<<" "<<ar[1]<<" "<<dr[0]<<" "<<dr[1]
                <<" "<<ge<<" "<<orr<<" "<<rank5<<"\n";
            if(ge&&v.affineDistinct&&v.firstFull&&firstRegular.size()<10)
              firstRegular.push_back({ci,gi,ri,hi,fi,ti,ar[0],ar[1]});
            if(orr&&v.affineDistinct&&v.firstFull&&firstOrigin.size()<10)
              firstOrigin.push_back({ci,gi,ri,hi,fi,ti,ar[0],ar[1]});
          }
        }
      }
    }
    return res;
  }

  Census(){
    for(int i=1;i<P;++i)for(int j=1;j<P;++j)if(mul(i,j)==1){inv[i]=j;break;}
    for(int i=0;i<P;++i)sq[mul(i,i)]=1;
    for(int i=0;i<P;++i)points.push_back({i,1});
    points.push_back({1,0});
    for(int i=0;i<P;++i)for(int j=0;j<P;++j)heads.push_back({i,j,1});
    for(int i=0;i<P;++i)heads.push_back({i,1,0});
    heads.push_back({1,0,0});
  }
  static void addBranch(std::array<I,10>& a,const Branch& b) {
    a[0]+=b.exist; a[1]+=b.affineDistinct; a[2]+=b.projectiveDistinct;
    a[3]+=b.flat; a[4]+=b.pole; a[5]+=b.collision;
    a[6]+=b.ambiguous; a[7]+=b.loss; a[8]+=b.rankdrop; a[9]+=b.firstFull;
  }
  void run(bool centerOnly=false){
    std::array<I,10> G{},O{},GF{},OF{};
    I gt=0,ot=0,both=0,closed=0,finiteClosed=0,clean=0,cleanClosed=0;
    std::array<I,5> types{};
    std::string maprow;
    for(int ci=0;ci<=P;++ci)for(int gi=0;gi<=P;++gi)for(int ri=0;ri<=P;++ri){
      if(centerOnly && (ci!=15||gi!=20||ri!=22))continue;
      ++count[0];
      Poly mc=prod(pol({0,0,1}),prod(point(ci),point(ci)));
      auto W=prod(pol({1,-1}),J(mc));
      auto Hc=prod(W,prod(point(gi),point(ri)));
      auto hs=options(mom(Hc,1),mom(Hc));
      bool ambh=hs.size()>1,ambf=false;
      Status out;
      if(ambh)++count[1];
      for(int hi:hs){
        auto Fm=prod(prod(pol({1,-1}),mc),prod(prod(point(gi),point(ri)),point(hi)));
        auto fs=options(mom(Fm,1),mom(Fm));
        bool aa=fs.size()>1;
        ambf|=aa;
        for(int fi:fs) {
          ++count[2];
          auto a=choices(ci,gi,ri,hi,fi,ambh||aa);
          out.generic.collect(a.generic);out.origin.collect(a.origin);
        }
      }
      if(ambf)++count[3];
      gt+=out.generic.tuples;ot+=out.origin.tuples;
      both+=out.generic.exist&&out.origin.exist;
      bool cl=!out.generic.exist&&!out.origin.exist;
      closed+=cl;
      int cls=cl?0:(out.generic.regular||out.origin.regular)?1:
        (out.generic.affineDistinct||out.origin.affineDistinct)?2:
        (out.generic.projectiveDistinct||out.origin.projectiveDistinct)?3:4;
      ++types[cls];
      if(emitMap){
        if(!ri)maprow.clear();
        int bits=int(out.generic.exist)+2*int(out.origin.exist)+4*int(out.generic.regular)
                     +8*int(out.origin.regular);
        maprow.push_back("0123456789abcdef"[bits]);
        if(ri==P)std::cout<<"MAP "<<ci<<" "<<gi<<" "<<maprow<<"\n";
      }
      bool finite=ci<P&&gi<P&&ri<P;
      if(finite) {addBranch(GF,out.generic);addBranch(OF,out.origin); finiteClosed+=cl;}
      if(!ambh&&!ambf) {++clean;cleanClosed+=cl;}
      addBranch(G,out.generic);addBranch(O,out.origin);
      if((ci==15&&gi==20&&ri==22)&&P==29)
        std::cout<<"center (15,20,22): generic="<<out.generic.exist
                 <<" origin="<<out.origin.exist<<"\n";
    }
    std::cout<<"prime "<<P<<"\nouter projective triples "<<count[0]
       <<"\nambiguous h outer triples "<<count[1]
       <<"\nambiguous f outer triples "<<count[3]<<"\nprojective (outer,h,f) sextuples "<<count[2]
       <<"\nproved closed outer triples "<<closed
       <<"\nproved closed finite-outer triples "<<finiteClosed
       <<"\nnonambiguous outer / closed "<<clean<<" "<<cleanClosed
       <<"\nouter survivors in both branches "<<both
       <<"\nprojective scalar candidates before nonlinear filter "<<count[16]
       <<"\nprojective reciprocal survivors before true phase generic / origin "<<count[17]<<" "<<count[18]
       <<"\nprojective nonlinear survivors after true phase generic / origin "<<gt<<" "<<ot<<"\n";
    std::cout<<"disjoint outer classes: closed "<<types[0]
       <<", finite regular "<<types[1]<<", finite distinct but nonregular "<<types[2]
       <<", projective distinct with a pole required "<<types[3]
       <<", only collisions/scale loss "<<types[4]<<"\n";
    const char* tags[10]={"any","all finite and distinct","projectively distinct",
      "tau=0 residue","at least one pole","collision or lost de",
      "h/f ambiguity","scale lost","head row rank drop","reciprocal column rank five"};
    for(int j=0;j<10;++j)
      std::cout<<tags[j]<<": generic "<<G[j]<<", origin "<<O[j]
               <<" (finite outer "<<GF[j]<<", "<<OF[j]<<")\n";
    for(const auto& eg:firstRegular){std::cout<<"regular generic example";for(int a:eg)std::cout<<" "<<a;std::cout<<"\n";}
    for(const auto& eg:firstOrigin){std::cout<<"regular origin example";for(int a:eg)std::cout<<" "<<a;std::cout<<"\n";}
  }
};

int main(int argc,char**argv){
  Census<29> c;
  c.emitRegular=argc>1&&std::string(argv[1])=="--regular";
  c.emitMap=argc>1&&std::string(argv[1])=="--map";
  c.run(argc>1&&std::string(argv[1])=="--center");
}
