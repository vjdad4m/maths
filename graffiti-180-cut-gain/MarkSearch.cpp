#include <map>
#include <tuple>
#include <algorithm>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <string>
#include <utility>
#include <vector>
using Mask=unsigned;
using Graph=std::vector<Mask>;
int size(Mask s){return std::popcount(s);}
int first(Mask s){return std::countr_zero(s);}
Graph decode(const std::string& word){
    int n=word[0]-63;
    if(n<3||n>20||word.size()!=static_cast<std::size_t>(1+(n*(n-1)/2+5)/6))std::abort();
    Graph g(n);
    for(int j=1,k=0;j<n;j++)for(int i=0;i<j;i++,k++)
        if((word[1+k/6]-63)&(32>>(k%6))){g[i]|=1u<<j;g[j]|=1u<<i;}
    return g;
}
std::vector<int> layers(const Graph& g,int r){
    std::vector<int>d(g.size(),-1); Mask front=1u<<r,seen=0;
    for(int l=0;front;l++){Mask next=0;
        for(Mask t=front;t;t&=t-1){int i=first(t);d[i]=l;next|=g[i];}
        seen|=front;front=next&~seen;
    }
    if(size(seen)!=int(g.size()))std::abort();
    return d;
}
struct Scores{
    Mask all;
    std::vector<Mask> nb,inds;
    std::vector<unsigned char> ell;
    explicit Scores(const Graph& g):all((1u<<g.size())-1),nb(all+1),ell(all+1){
        std::vector<unsigned char> ind(all+1);ind[0]=1;inds.push_back(0);
        for(Mask s=1;s<=all;s++){
            int i=first(s);Mask tail=s&(s-1);nb[s]=nb[tail]|g[i];
            if(ind[tail]&&!(g[i]&tail)){ind[s]=1;inds.push_back(s);}
        }
        for(Mask s=1;s<=all;s++){
            Mask core=all^s;
            if((core|nb[core])==all && connected(core)){ell[s]=size(s);continue;}
            for(Mask t=s;t;t&=t-1)ell[s]=std::max(ell[s],ell[s^(t&-t)]);
        }
    }
    bool connected(Mask s)const{
        if(!s)return false;
        Mask f=s&-s,previous=0;
        while(f!=previous){previous=f;f|=nb[f]&s;}
        return f==s;
    }
};

bool bip(const Graph& g,Mask D){
    Mask A=0,B=0;
    while(D&~(A|B)){
        Mask newpart=(D&~(A|B)); A|=(newpart&-newpart);
        Mask frontier=newpart&-newpart; bool step=true;
        while(frontier){
            Mask nb=0;
            for(Mask t=frontier;t;t&=t-1)nb|=g[first(t)];
            nb&=D;
            if(nb&(step?A:B))return false;
            frontier=nb&~(A|B);
            (step?B:A)|=frontier;step=!step;
        }
    }
    return true;
}
int main(){
 long long graphs=0,pinnedGraphs=0,tests=0,saturated=0,unusual=0,over=0;std::string line;
 std::map<std::tuple<int,int,int,int>,long long> types;
 while(std::cin>>line){
  Graph g=decode(line);int n=g.size();Mask all=(1u<<n)-1,pin=all;int b=0;++graphs;
  for(Mask B=all;B;--B)if(size(B)>=b&&bip(g,B)){
    if(size(B)>b){b=size(B);pin=B;}else pin&=B;
  }
  if(b==n)continue;
  bool edge=false;for(Mask W=pin;W;W&=W-1)edge |= bool(g[first(W)]&pin);
  if(!edge)continue;
  ++pinnedGraphs;
  Scores sc(g);
  for(int r=0;r<n;r++){
    auto d=layers(g,r);Mask even=0;for(int i=0;i<n;i++)if(!(d[i]&1))even|=1u<<i;
    for(Mask W=pin;W;W&=W-1){
      int w=first(W);Mask near=0,wb=1u<<w;
      for(Mask X=g[w]&pin;X;X&=X-1)if(d[first(X)]==d[w]+1)near|=X&-X;
      if(!near)continue;
      for(Mask P:{even,all^even})for(Mask A:sc.inds){
        Mask U=(P|A)&~wb;if(!(A&P&(1u<<r)))U&=~(1u<<r);
        int k=1+size(A)+size(P)-b-sc.ell[U];
        bool aw=A&wb,pw=P&wb;
        for(int role=0;role<=(r==w);++role){
          int cap=role?(aw&&pw):(aw||pw);tests+=size(near);
          if(k<cap)continue;
          if(k>cap)over+=size(near);
          saturated+=size(near);
          for(Mask X=near;X;X&=X-1){
            int x=first(X);bool ax=A&(1u<<x);
            types[{role,aw,pw,ax}]++;
            if(aw||pw||!ax){
              ++unusual;
              if(unusual<=40)std::cout<<"EXCEPTION "<<line<<" n "<<n<<" r "<<r<<" w "<<w<<" x "<<x<<" P "<<P<<" A "<<A<<" role "<<role<<" k "<<k<<" cap "<<cap<<" rank "<<b<<std::endl;
            }
          }
        }
      }
    }
  }
 }
 std::cout<<"graphs "<<graphs<<" with pinned edge "<<pinnedGraphs<<" rooted marked port tests "<<tests<<" saturating or exceeding "<<saturated<<" exceptions "<<unusual<<" exceeding "<<over<<"\n";
 for(auto [key,count]:types){auto [r,a,p,t]=key;std::cout<<"role "<<r<<" seam A "<<a<<" seam P "<<p<<" tip A "<<t<<" count "<<count<<"\n";}
}
