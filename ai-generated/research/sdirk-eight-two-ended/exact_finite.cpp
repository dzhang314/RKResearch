#include <algorithm>
#include <array>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <vector>
using namespace std;
int p;
int red(long long x){x%=p;return x<0?x+p:x;}
int iv[257];
int divs(int a,int b){assert(red(b));return red((long long)red(a)*iv[red(b)]);}
int pp(int a,int n){int b=1;for(int i=0;i<n;i++)b=red(b*a);return b;}
struct Pair{int x,g;bool operator==(const Pair&b)const{return x==b.x&&g==b.g;}};
struct Mat{int r,c;int a[11][17]{};};
int rowred(Mat& m, int* ans, vector<vector<int>>* ker=nullptr){
 int j=0;int cols[16];
 for(int k=0;k<m.c&&j<m.r;k++){
  int h=j;while(h<m.r&&!m.a[h][k])h++;
  if(h==m.r)continue;
  for(int t=k;t<=m.c;t++)swap(m.a[h][t],m.a[j][t]);
  int u=iv[m.a[j][k]];
  for(int t=k;t<=m.c;t++)m.a[j][t]=red(m.a[j][t]*u);
  for(int l=0;l<m.r;l++)if(l!=j&&m.a[l][k]){
   int z=m.a[l][k];
   for(int t=k;t<=m.c;t++)m.a[l][t]=red(m.a[l][t]-z*m.a[j][t]);
  }
  cols[j++]=k;
 }
 for(int h=j;h<m.r;h++)if(m.a[h][m.c])return -1;
 for(int z=0;z<m.c;z++)ans[z]=0;
 for(int k=0;k<j;k++)ans[cols[k]]=m.a[k][m.c];
 if(ker){
  for(int c=0;c<m.c;c++){
   if(find(cols,cols+j,c)!=cols+j)continue;
   vector<int> k(m.c);k[c]=1;
   for(int i=0;i<j;i++)k[cols[i]]=red(-m.a[i][c]);
   ker->push_back(k);
  }
 }
 return j;
}
struct Uv{int a[4],b[6];};
bool fits(const Pair* s,int count,int m,Uv& r, vector<vector<int>>& ka,vector<vector<int>>& kb){
 Mat A{count,4},B{count,6};
 int n3=divs(3*m*m,5),n4=divs(6*m*m,7),n0=divs(3*pp(m,4),35);
 for(int i=0;i<count;i++){
  int t=red(s[i].x-m),g=s[i].g;
  if(!g)return false;
  A.a[i][0]=1;A.a[i][1]=t;A.a[i][2]=pp(t,2);A.a[i][3]=g;
  A.a[i][4]=divs(pp(t,4)-n4*t*t+n0,g);
  B.a[i][0]=1;B.a[i][1]=t;B.a[i][2]=pp(t,2);B.a[i][3]=pp(t,3);B.a[i][4]=g;B.a[i][5]=red(t*g);
  B.a[i][6]=divs(t*(t*t-n3),g);
 }
 return rowred(A,r.a,&ka)>=0&&rowred(B,r.b,&kb)>=0;
}
bool leading(const Uv& r){
 if(!r.a[3])return false;
 auto b=r.b;
 if(!b[3]&&!b[5])return false;
 if(b[3]&&b[5]){
  int q=divs(-b[3],b[5]);
  if(!red(1-r.a[2]*q-r.a[3]*q*q))return false;
 }
 return true;
}
int isfourth(const Pair& d,const Pair* s){
 int u=red(s[1].x-1),v=red(s[2].x-1),k=red(2*s[1].g);
 if(!u||!v||u==v||!k)return false;
 int x=d.x,g=d.g;
 int x1=divs(s[1].g-iv[2],u),x2=divs(s[2].g-iv[2],v);
 int c=divs(x2-x1,v-u),b=red(x1-c*(1+s[1].x)),a=red(iv[2]-b-c);
 int j=red(a*x+divs(b*x*x,2)+divs(c*x*x*x,3));
 int gg=red(1+divs(x-1,k));
 int dd=red(divs(4,3)+divs(2*(k+1)*(x-1),3*k));
 return red(g-(a+b*x+c*x*x)+j-g*(gg-b-c*dd))==0;
}
void ww(const vector<Pair>& s,int m,const Uv& r, int *weights){
 int n3=divs(3*m*m,5),n4=divs(6*m*m,7),norm=divs(pp(2*m,6),2800);
 auto a=r.a;auto b=r.b;
 for(int i=0;i<10;i++){
  int t=red(s[i].x-m),g=s[i].g;
  int Ux=red(4*pp(t,3)-2*n4*t-g*(a[1]+2*a[2]*t));
  int Ug=red(-a[0]-a[1]*t-a[2]*t*t-2*a[3]*g);
  int Vx=red(3*t*t-n3-g*(b[1]+2*b[2]*t+3*b[3]*t*t+b[5]*g));
  int Vg=red(-b[0]-b[1]*t-b[2]*t*t-b[3]*t*t*t-2*g*(b[4]+b[5]*t));
  int J=red(Ux*Vg-Ug*Vx);
  weights[i]=J?divs(-norm,g*J):0;
 }
}
int np[7]={1,2,4,6,9,12,16};
bool chrono(const vector<Pair>& s,int m,int A[10][10]){
 int X[10][16],J[10][16];
 for(int i=0;i<10;i++){
  int a=s[i].x,b=s[i].g,j=0;
  for(int r=0;r<=6;r++)for(int t=0;2*t<=r;t++){
   X[i][j]=red(pp(a,r-2*t)*pp(b,t));
   J[i][j]=t?0:divs(pp(a,r+1),r+1);
   j++;
  }
 }
 int V[10][10],Y[10][10];
 for(int i=0;i<10;i++){
  Mat s0{i+1,0};
  int deg=-1,f[16],q[16];
  for(int r=0;r<=6;r++){
   s0.c=np[r];
   for(int j=0;j<=i;j++){
    copy(X[j],X[j]+np[r],s0.a[j]);
    s0.a[j][np[r]]=j==i;
   }
   if(rowred(s0,f)>=0){deg=r;break;}
  }
  if(deg<0)return false;
  for(int j=0;j<10;j++){
   int vx=0,yx=0;
   for(int k=0;k<np[deg];k++){vx+=X[j][k]*f[k];yx+=J[j][k]*f[k];}
   V[i][j]=red(vx);Y[i][j]=red(yx);
  }
  s0.c=deg?np[deg-1]:0;
  for(int j=0;j<=i;j++){
   copy(X[j],X[j]+s0.c,s0.a[j]);
   s0.a[j][s0.c]=divs((j==i)-Y[i][j],s[j].g);
  }
  if(rowred(s0,q)<0)return false;
  for(int j=0;j<10;j++){
   int yx=0;
   for(int k=0;k<s0.c;k++)yx+=X[j][k]*q[k];
   Y[i][j]=red(Y[i][j]+s[j].g*red(yx));
  }
 }
 for(int i=0;i<10;i++){
  Mat s0{10,10};
  for(int j=0;j<10;j++){
   copy(V[j],V[j]+10,s0.a[j]);s0.a[j][10]=Y[j][i];
  }
  int a[16];
  assert(rowred(s0,a)==10);
  for(int j=0;j<10;j++){
   if(j>=i)assert(a[j]==(j==i));
   A[i][j]=divs(a[j],2*m);
  }
 }
 return true;
}

bool verify(const vector<Pair>& ss,int m,const Uv& a){
 int A[10][10],weights[10];ww(ss,m,a,weights);
 if(find(weights,weights+10,0)!=weights+10||!chrono(ss,m,A))return false;
 printf("FOUND p=%d\n",p);
 for(int i=0;i<10;i++){for(int j=0;j<10;j++)printf("%d ",A[i][j]);printf("| %d\n",weights[i]);}
 return true;
}
vector<Pair> common(const Pair* known,int len,int m,const Uv& a){
 vector<Pair> other;
 int n3=divs(3*m*m,5),n4=divs(6*m*m,7),n0=divs(3*pp(m,4),35);
 for(int x=0;x<p;x++){
  int t=red(x-m),l=red(pp(t,4)-n4*t*t+n0),h=red(t*(t*t-n3)),f3=red(a.b[0]+a.b[1]*t+a.b[2]*t*t+a.b[3]*t*t*t),f4=red(a.a[0]+a.a[1]*t+a.a[2]*t*t);
  for(int g=1;g<p;g++) if(!red(l-g*(f4+a.a[3]*g))&&!red(h-g*(f3+(a.b[4]+a.b[5]*t)*g))){
   Pair d={x,g};if(find(known,known+len,d)==known+len)other.push_back(d);
  }
 }
 return other;
}
vector<Pair> fourths(const Pair* s){
 vector<Pair> out;
 for(int x=0;x<p;x++){
  // The membership test is affine in the residual; solve it exactly rather than sampling.
  for(int g=1;g<p;g++)if(isfourth({x,g},s))out.push_back({x,g});
 }
 return out;
}
vector<vector<int>> expand(const int* a,int len,const vector<vector<int>>& ker){
 vector<vector<int>> x(1,vector<int>(a,a+len));
 for(auto b:ker){
  size_t k=x.size();
  for(int t=1;t<p;t++)for(size_t j=0;j<k;j++){
   auto v=x[j];
   for(int i=0;i<len;i++)v[i]=red(v[i]+t*b[i]);
   x.push_back(v);
  }
 }
 return x;
}
int main(int ac,char**av){
 assert(ac==2);
 p=atoi(av[1]);
 for(int i=1;i<p;i++)for(int j=1;j<p;j++)if(red(i*j)==1)iv[i]=j;
 long trials=0,fit=0,singular=0,corner=0,actual=0,representations=0;
 for(int m=1;m<p;m++)
 for(int s=0;s<=1;s++)for(int t=0;t<=1;t++)
 for(int u=1;u<p;u++)for(int v=1;v<p;v++){
  int d1=red(-2+u+4*u*u-u*u*u),d2=red(-2+v+4*v*v-v*v*v);
  if((!s&&(u==1||u==2))||(!t&&(v==1||v==2))||(s&&(!d1||!red(3*u-2)))||(t&&(!d2||!red(3*v-2))))continue;
  int w=red(s?2*u:2-u),z=red(t?2*v:2-v);
  int r=s?divs(2*u*(3*u-2),d1):0,q=t?divs(2*v*(3*v-2),d2):0;
  int g2=divs(1+2*u-u*u,2),g3=divs(1+2*w-w*w+2*r*u,2);
  int h2=red(1+2*v-v*v),h3=red(1+2*z-z*z+2*q*v);
  if(!g2||!g3||!h2||!h3)continue;
  Pair forw[3]={{1,iv[2]},{red(1+u),g2},{red(1+w),g3}};
  Pair refl[3]={{1,iv[2]},{red(1+v),divs(h2,2)},{red(1+z),divs(h3,2)}};
  vector<Pair> f;vector<Pair> g;
  for(int G=1;G<p;G++){
   Pair known[8]={forw[0],forw[1],forw[2],{red(2*m-1),G},{red(2*m-1-v),red(h2*G)},{red(2*m-1-z),red(h3*G)}};
   bool unique=true;
   for(int j=0;j<6;j++)for(int l=0;l<j;l++)if(known[j]==known[l])unique=false;
   if(!unique)continue;
   trials++;Uv a;
   vector<vector<int>> ka,kb;
   if(!fits(known,6,m,a,ka,kb))continue;
   if(ka.empty()&&kb.empty()){
    fit++;
    if(!leading(a))continue;
    auto other=common(known,6,m,a);
    if(other.size()!=4)continue;
    corner++;
    int pi[4]={0,1,2,3};
    do {
     if(!isfourth(other[pi[0]],known))continue;
     auto d7=other[pi[3]];
     if(!isfourth({red(2*m-d7.x),divs(d7.g,2*G)},refl))continue;
     actual++;
     vector<Pair> ss(known,known+3);
     for(auto j:pi)ss.push_back(other[j]);
     for(int j=5;j>=3;j--)ss.push_back(known[j]);
     if(verify(ss,m,a))return 1;
    }while(next_permutation(pi,pi+4));
   }else{
    singular++;
    if(f.empty())f=fourths(forw);
    if(g.empty())g=fourths(refl);
    for(auto d4:f){
     if(find(known,known+6,d4)!=known+6)continue;
     known[6]=d4;
     for(auto rel:g){
      Pair d7={red(2*m-rel.x),red(2*G*rel.g)};
      if(find(known,known+7,d7)!=known+7)continue;
      known[7]=d7;
      vector<vector<int>> ka2,kb2;
      if(!fits(known,8,m,a,ka2,kb2))continue;
      auto U=expand(a.a,4,ka2),V=expand(a.b,6,kb2);
      for(auto aa:U)for(auto bb:V){
       copy(aa.begin(),aa.end(),a.a);copy(bb.begin(),bb.end(),a.b);
       representations++;
       if(!leading(a))continue;
       auto mid=common(known,8,m,a);
       if(mid.size()!=2)continue;
       for(int j=0;j<2;j++){
        vector<Pair> ss(known,known+3);
        ss.push_back(d4);ss.push_back(mid[j]);ss.push_back(mid[1-j]);ss.push_back(d7);
        for(int k=5;k>=3;k--)ss.push_back(known[k]);
        actual++;
        if(verify(ss,m,a))return 1;
       }
      }
     }
    }
   }
  }
 }
 printf("p=%d trials=%ld unique=%ld singular=%ld eight-pair completions=%ld unique corners=%ld bothfourth=%ld, no candidate\n",p,trials,fit,singular,representations,corner,actual);
}
