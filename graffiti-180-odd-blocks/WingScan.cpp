#include <set>
#include <algorithm>
#include <array>
#include <bit>
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
struct Rank{
    const Graph& g;
    Mask all;
    std::vector<unsigned char> memo;
    std::vector<Mask> critical;
    int b=0;
    bool forest=true;
    int alpha(Mask s){
        if(!s)return 0;
        if(memo[s])return memo[s];
        int i=first(s);Mask t=s&(s-1);
        int take=1+alpha(t&~g[i]);
        return memo[s]=(t&g[i])?std::max(take,alpha(t)):take;
    }
    template<class F>bool maximal(Mask cand,Mask exc,Mask chosen,F& test){
        if(!cand)return !exc&&test(chosen);
        int pivot=first(cand|exc); Mask choices=cand&((1u<<pivot)|g[pivot]);
        while(choices){int i=first(choices);Mask bit=1u<<i;choices^=bit;cand^=bit;
            if(maximal(cand&~g[i],exc&~g[i],chosen|bit,test))return true;
            exc|=bit;
        }
        return false;
    }
    explicit Rank(const Graph& graph):g(graph),all((1u<<g.size())-1),memo(all+1),critical(g.size()){
        auto count=[&](Mask s){b=std::max(b,size(s)+alpha(all^s));return false;};
        maximal(all,0,0,count);
        int n=g.size();std::array<int,20> parent{};for(int i=0;i<n;i++)parent[i]=i;
        auto root=[&](int i){while(i!=parent[i])i=parent[i];return i;};
        for(int i=0;i<n;i++)for(Mask t=g[i]&~((2u<<i)-1);t;t&=t-1){
            int j=first(t); Mask pair=(1u<<i)|(1u<<j);
            auto better=[&](Mask s){return size(s)+alpha(all^s)>b;};
            if(maximal(all&~(g[i]|g[j]|pair),0,pair,better)){
                critical[i]|=1u<<j; critical[j]|=1u<<i;
            }else{
                int a=root(i),c=root(j);
                if(a==c){forest=false;return;}parent[a]=c;
            }
        }
    }
};
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
std::string code(const Graph& g,const std::vector<int>& perm){
    int n=g.size();std::string out(1,char(63+n));int bits=0,k=0;
    for(int j=1;j<n;j++)for(int i=0;i<j;i++){
        bits=2*bits+int((g[perm[i]]>>perm[j])&1);
        if(++k==6){out+=char(63+bits);bits=k=0;}
    }
    if(k)out+=char(63+(bits<<(6-k)));
    return out;
}
void ports(bool canonical){
    std::set<std::string> out;
    std::string line;
    while(std::cin>>line){
      Graph g=decode(line);unsigned n=g.size();Mask all=(1u<<n)-1,required=all; int best=0;
      for(Mask z=1;z<=all;z++)if(size(z)>=best&&bip(g,z)){
          if(size(z)>best){best=size(z);required=z;}else required&=z;
      }
      if(best==int(n))continue;
      for(Mask t=required;t;t&=t-1)for(Mask u=required&g[first(t)];u;u&=u-1){
          std::vector<int> p{first(t),first(u)};
          for(unsigned i=0;i<n;i++)if(int(i)!=p[0] && int(i)!=p[1])p.push_back(i);
          if(!canonical){std::cout<<code(g,p)<<"\n";continue;}
          std::string word;
          do{auto k=code(g,p);if(word.empty()||k<word)word=k;}while(std::next_permutation(p.begin()+2,p.end()));
          out.insert(word);
      }
    }
    for(auto &x:out)std::cout<<x<<"\n";
}
struct Census {
    long long pairs=0,drops=0,forest=0,roots=0,marks=0,tight=0;
    int slack=100;
    void pair(const Graph& L, const Graph& R){
        int n=L.size()+R.size()-1; if(n<4)return;
        Graph h(n);auto expand=[&](const Graph& b,int offset){
          auto v=[&](int i){return i?i+offset:0;};
          for(unsigned i=0;i<b.size();i++)for(Mask t=b[i];t;t&=t-1)h[v(i)]|=1u<<v(first(t));
        };
        expand(L,0);expand(R,L.size()-1);Graph g=h;int x=1,y=L.size();g[x]|=1u<<y;g[y]|=1u<<x;pairs++;
        Rank upper(g),lower(h);if(lower.b!=upper.b+1)return;drops++;
        if(!upper.forest)return;forest++;
        for(int r=0;r<n;r++){
            auto d=layers(g,r);if(d[x]!=d[y])continue;bool good=true;Mask even=0;
            for(int i=0;i<n;i++){
                if(!(d[i]%2))even|=1u<<i;
                Mask pred=0;
                for(Mask t=g[i];t;t&=t-1){
                    int j=first(t);if(d[j]+1==d[i])pred|=1u<<j;
                    if(d[j]==d[i]&&!(upper.critical[i]&(1u<<j)))good=false;
                }
                if(size(pred)>1 && (pred&~upper.critical[i]))good=false;
            }
            if(!good)continue;roots++;
            Scores hi(g),lo(h);Mask all=hi.all;
            for(auto a:hi.inds)for(auto P:{even,all^even}){
                marks++;Mask u=(a|P)&((a&P)|(all^(1u<<r)));
                int s=int(lo.ell[u])+lower.b-1-size(a)-size(P);
                slack=std::min(slack,s);if(s)continue;
                ++tight;std::vector<int> p;for(int v=0;v<n;v++)p.push_back(v);
                if(tight<=12)std::cout<<"TIGHT "<<code(g,p)<<" r "<<r<<" A "<<a<<" P "<<P<<" x y w "<<x<<" "<<y<<" 0\n";
            }
        }
    }
    void report(int count)const {
    std::cout<<"wings "<<count<<" constructed pairs "<<pairs<<" rank drops "<<drops<<" noncritical forest "<<forest<<" horizontal sparse roots "<<roots<<" marked profiles "<<marks<<" lower tight "<<tight;
    if(marks)std::cout<<" smallest lower slack "<<slack;
    std::cout<<"\n";
}
};
void search(bool pendant){
    Graph edge{2,1};Census c;std::string line;
    if(pendant){
        int count=1;
        while(std::cin>>line){c.pair(edge,decode(line));count++;}
        c.report(count);
    }else{
        std::vector<Graph> wings{edge};
        while(std::cin>>line)wings.push_back(decode(line));
        for(unsigned l=0;l<wings.size();l++)for(unsigned k=l;k<wings.size();k++)c.pair(wings[l],wings[k]);
        c.report(wings.size());
    }
}
int main(int argc,char **argv){
    std::string mode=argc>1?argv[1]:"";
    if(mode=="--ports"||mode=="--raw-ports")ports(mode=="--ports");
    else search(mode=="--pendant");
}
