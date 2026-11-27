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
    ++histogram[n-best[0]];
    for(int r=0;r<n;++r){
      Mask root=1u<<r;
      bool dominated=false;for(Mask x=g[r];x;x&=x-1)if((g[r]|g[countr_zero(x)])==all)dominated=true;
      if(dominated)continue;
      ++roots;
      Mask odd=0,fr=root,seen=root;bool level=false;
      while(fr){if(level)odd|=fr;fr=neighbors[fr]&~seen;seen|=fr;level=!level;}
      // Bipartite orders with the root isolated have a separate subset table.
      vector<int> iso(count);
      for(Mask z=0;z<count;++z)if(bip[z] && (z&root) && !(z&g[r]))iso[z]=sz[z]+1;
      for(int i=0;i<n;++i)for(Mask m=0;m<count;++m)if(!(m&(1u<<i)))iso[m]=max(iso[m],iso[m|(1u<<i)]);
      for(Mask A:independent)for(bool p:{false,true}){
        Mask P=p?odd:(all^odd),D=A&P,U=A|P;if(!(D&root))U&=~root;
        int need=1+sz[A]+sz[P]-w[U];
        ++pinCases;
        if(best[D]<need){cout<<"FAILED pinned "<<line<<" "<<r<<" "<<p<<" "<<A<<" "<<need<<" "<<best[D]<<endl;return 1;}
        if(p&&(A&root)){
          ++oddCases;Mask K=D|root;int ordinary=best[K],paid=max(ordinary,iso[K]);
          if(ordinary<need)++neededBonus;
          if(ordinary<best[0])++nonmax;
          if(paid<need){cout<<"FAILED odd "<<line<<" "<<r<<" "<<A<<" "<<need<<" "<<paid<<endl;return 1;}
        }
      }
    }
  }
  cout<<"inputs "<<graphs<<" connected_nonbipartite_prime "<<prime<<" qualifying_roots "<<roots<<" first_tests "<<pinCases<<" second_tests "<<oddCases<<" second_needing_credit "<<neededBonus<<" second_without_global_maximum "<<nonmax<<"\n";
  cout<<"transversal_histogram";for(int i=0;i<24;++i)if(histogram[i])cout<<" "<<i<<":"<<histogram[i];cout<<"\n";
}
