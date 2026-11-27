#include <algorithm>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
using Mask = unsigned;
int main() {
  string line;
  long long graphs=0, prime=0, roots=0, pinCases=0, oddCases=0, neededBonus=0, nonmax=0;
  long long histogram[24]={};
  while (cin >> line) {
    int n=line[0]-63;
    if(n<3||n>18||line.size()!=1+size_t((n*(n-1)/2+5)/6)) return 2;
    ++graphs;
    const Mask count=1u<<n, all=count-1;
    vector<Mask> g(n);
    for(int j=1,t=0;j<n;++j)for(int i=0;i<j;++i,++t)
      if((line[1+t/6]-63)&(1<<(5-t%6))){g[i]|=1u<<j;g[j]|=1u<<i;}
    auto reach=[&](Mask m){Mask v=m&-m, old=0;while(v!=old){old=v;for(Mask x=old;x;x&=x-1)v|=g[countr_zero(x)]&m;}return v;};
    if(reach(all)!=all) continue;
    bool module=false;
    for(int a=0;a<n&&!module;++a)for(int b=0;b<a&&!module;++b) {
      Mask m=(1u<<a)|(1u<<b),seen=1u<<a;
      while(m!=all && (m&~seen)){int c=countr_zero(m&~seen);seen|=1u<<c;m|=g[c]^g[a];}
      if(m!=all)module=true;
    }
    if(module)continue;
    vector<Mask> neighbors(count);
    vector<int> ind(count),sz(count),bip(count),best(count),w(count);
    vector<Mask> independent;
    ind[0]=1; independent.push_back(0);
    for(Mask m=1;m<count;++m){Mask bit=m&-m,rest=m^bit;int i=countr_zero(bit);
      neighbors[m]=neighbors[rest]|g[i];ind[m]=ind[rest]&&!(g[i]&rest);sz[m]=sz[rest]+1;if(ind[m])independent.push_back(m);}
    for(auto a:independent)for(auto b:independent)bip[a|b]=1;
    if(bip[all])continue;
    ++prime;
    for(Mask m=0;m<count;++m){if(bip[m]) best[m]=sz[m];
      if(m&&((m|neighbors[m])==all)){Mask vis=m&-m;while(true){auto next=vis|(neighbors[vis]&m);if(vis==next)break;vis=next;}
        if(vis==m)w[all^m]=sz[all^m];}}
    for(int i=0;i<n;++i)for(Mask m=0;m<count;++m)if(!(m&(1u<<i))){Mask v=m|(1u<<i);best[m]=max(best[m],best[v]);w[m]=max(w[m],w[v]-1);}
    for(int i=0;i<n;++i)for(Mask m=0;m<count;++m)if(m&(1u<<i))w[m]=max(w[m],w[m^(1u<<i)]);
    if (n-best[0]!=2) continue;
    vector<Mask> partners(n);
    bool anyEdge=false, anyGood=false;
    for(int a=0;a<n;a++)for(int b=0;b<a;b++)if(bip[all^(1u<<a)^(1u<<b)]){
      partners[a]|=1u<<b;partners[b]|=1u<<a;
      bool edge=g[a]&(1u<<b);
      anyEdge|=edge;
      anyGood|=edge || (sz[g[a]]!=4 && sz[g[b]]!=4 &&
        (abs(sz[g[a]]-sz[g[b]])+sz[g[a]&g[b]]>2 || sz[g[a]|g[b]]<=5));
    }
    if(anyGood)continue;
    ++histogram[0];
    struct Rule {int a,b;bool soloA,soloB,both;};vector<Rule> rules;
    for(int a=0;a<n;a++)for(int b=0;b<a;b++)if(partners[a]&(1u<<b)){
      Mask R=all^((1u<<a)|(1u<<b));bool soloA=sz[g[a]]==4,soloB=sz[g[b]]==4,both=true;
      int bound=max({2,sz[g[a]]-2,sz[g[b]]-2});
      for(Mask C=R;;C=(C-1)&R){
        if(ind[C] && ind[R^C]){
          for(Mask col:{C,R^C}){
            if(sz[g[a]&col]!=2)soloA=false;
            if(sz[g[b]&col]!=2)soloB=false;
            for(Mask other:{C,R^C})if(sz[(g[a]&col)|(g[b]&other)]<=bound)both=false;
          }
        }
        if(!C)break;
      }
      rules.push_back({a,b,soloA,soloB,both});
    }
    bool possible=false;
    for(Mask k:independent){
      bool ok=true;
      for(auto [a,b,one,two,both]:rules){
        bool av=k&(1u<<a),bv=k&(1u<<b);
        if(!(av?(bv?both:one):(bv&&two))){ok=false;break;}
      }
      if(ok){possible=true;break;}
    }
    if(possible){
      if(!histogram[1]++)cout<<"First graph with consistent cover "<<line<<"\n";
    }else ++histogram[2];
  }
  cout<<"inputs "<<graphs<<" old_residual "<<histogram[0]<<" inconsistent_cover "<<histogram[2]<<" compatible_cover "<<histogram[1]<<"\n";
}
