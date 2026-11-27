#include <algorithm>
#include <array>
#include <cmath>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>
using I = __int128;
using i64 = long long;
int mod(i64 a,int p){a%=p;return a<0?a+p:a;}
int inv(int a,int p){for(int i=1;i<p;++i)if(a*i%p==1)return i;return 0;}
bool smooth(i64 n){for(auto p:{2,3,5,7})while(n%p==0)n/=p;return n==1;}
std::pair<i64,i64> red(i64 a,i64 b){
    i64 g=std::gcd(a,b); if(b<0)g=-g;return {a/g,b/g};
}
constexpr std::array<int,5> ps{11,13,19,23,31};
constexpr int np=ps.size();
struct Node{int m,n; std::array<int,np> r;};
int main(int argc,char**argv) {
    int N=argc>1?std::atoi(argv[1]):1500;
    bool ok[np][32][32]{},use[np][32]{};
    for(int k=0;k<np;++k){
        int p=ps[k];
        for(int i=0;i<p;++i)for(int j=i+1;j<p;++j)for(int l=j+1;l<p;++l)for(int v=l+1;v<p;++v){
            std::array<int,4> a{i,j,l,v};
            if(i==0 || i==1 || j==1 || l==1 || v==1 || v==p-1)continue;
            int S=i+j+l+v,S2=i*j+i*l+i*v+j*l+j*v+l*v;
            int S3=i*j*l+i*j*v+i*l*v+j*l*v,V=i*j*l*v;
            if(mod(7*S2+35LL*V+3,p) || mod(3*S+7*S3,p))continue;
            for(int r:a)for(int s:a)if(r!=s)ok[k][r][s]=use[k][r]=true;
        }
    }
    using bucket_t=std::array<std::array<std::vector<Node>,32>,32>;
    bucket_t bucket;
    bool sq63[63]{},sq64[64]{},sq65[65]{};
    for(int i=0;i<65;++i){sq63[(i*i)%63]=true;sq64[(i*i)%64]=true;sq65[(i*i)%65]=true;}
    int count=0;
    for(int den=1;den<=N;++den)if(smooth(den)&&den%7){
      std::array<int,np> inverses;
      for(int k=0;k<np;++k)inverses[k]=inv(den%ps[k],ps[k]);
      for(int num=-N;num<=N;++num)if(num&&std::abs(num)!=den&&std::gcd(num,den)==1){
        Node A{num,den};
        bool all=true;
        for(int k=0;k<np;++k){
            A.r[k]=mod(num*inverses[k],ps[k]);
            if(!use[k][A.r[k]]){all=false;break;}
        }
        if(all){bucket[A.r[0]][A.r[1]].push_back(A);++count;}
      }
    }
    std::set<std::array<std::pair<i64,i64>,4>> candidates;
    i64 valid=0,squares=0;
    for(int i=0;i<ps[0];++i)for(int j=0;j<ps[1];++j)
    for(int k=i+1;k<ps[0];++k)if(ok[0][i][k])
    for(int l=0;l<ps[1];++l)if(ok[1][j][l]){
      for(const Node&A:bucket[i][j])for(const Node&B:bucket[k][l]){
        if(!ok[2][A.r[2]][B.r[2]] || !ok[3][A.r[3]][B.r[3]] || !ok[4][A.r[4]][B.r[4]])continue;
        i64 w=(i64)A.n*B.n,u=(i64)A.m*B.n+(i64)A.n*B.m,v=(i64)A.m*B.m,h=7*v+3*w;
        
        if(mod(v-4*w,7)) continue;
        int w7=inv(mod(w,7),7), s7=mod(u*w7,7);
        int tt=mod(((w+5*v)/7)*w7,7);
        int disc=mod(2*s7*s7-tt,7);
        if(disc==3||disc==5||disc==6) continue;
        ++valid;
        I e=7*(I)u*u-((I)w+5*(I)v)*h;
        if(e==0)continue;
        I K=7*(112*(I)u*u*v*v-e*((I)h*h-21*(I)u*u));
        if(K<=0||!sq64[K&63]||!sq63[K%63]||!sq65[K%65])continue;
        i64 z=(i64)std::sqrt((long double)K);
        while((I)z*z>K)--z;
        while((I)(z+1)*(z+1)<=K)++z;
        if((I)z*z!=K)continue;
        ++squares;
        auto a=red(28*u*v+z,7*e),b=red(28*u*v-z,7*e);
        if(!smooth(a.second) || !smooth(b.second) || a.second%7 || b.second%7) continue;
        std::array<std::pair<i64,i64>,4> C{red(A.m,A.n),red(B.m,B.n),a,b};
        std::sort(C.begin(),C.end());
        if(candidates.insert(C).second){
            for(auto [m,n]:C)std::cout<<m<<"/"<<n<<" ";
            std::cout<<std::endl;
        }
      }
    }
    std::cout<<"N="<<N<<", filtered abscissae "<<count<<", compatible pairs "<<valid
      <<", square discriminants "<<squares<<", all-smooth hits "<<candidates.size()<<"\n";
}
