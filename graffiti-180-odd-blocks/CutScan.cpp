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

struct Counts{long long graphs=0,roots=0,profiles=0,firsts=0,witnesses=0;};
void check(const std::string& word,Counts& c){
    Graph g=decode(word);int n=g.size();c.graphs++;
    bool triangle=false;
    for(int i=0;i<n&&!triangle;i++)for(Mask t=g[i];t;t&=t-1)if(g[i]&g[first(t)]){triangle=true;break;}
    if(!triangle)return;
    Rank rank(g);if(!rank.forest)return;
    Mask all=rank.all;
    struct Root{int r;Mask even;std::vector<std::pair<int,int>> chords;};
    std::vector<Root> roots;
    for(int r=0;r<n;r++){
        auto d=layers(g,r);Root row{r,0,{}};bool sparse=true;
        for(int i=0;i<n&&sparse;i++){
            if(!(d[i]&1))row.even|=1u<<i;
            Mask prev=0;
            for(Mask t=g[i];t;t&=t-1){int j=first(t);
                if(d[j]+1==d[i])prev|=1u<<j;
                if(d[j]!=d[i])continue;
                if(!(rank.critical[i]&(1u<<j))){sparse=false;break;}
                if(i<j&&(g[i]&g[j]))row.chords.emplace_back(i,j);
            }
            if(size(prev)>1&&(prev&~rank.critical[i]))sparse=false;
        }
        if(sparse&&!row.chords.empty())roots.push_back(std::move(row));
    }
    if(roots.empty())return;
    Scores hi(g);
    for(auto& row:roots){c.roots++;
        for(auto [i,j]:row.chords){
            Graph h=g;h[i]^=1u<<j;h[j]^=1u<<i;Scores lo(h);Mask tips=(1u<<i)|(1u<<j);
            for(int p=0;p<2;p++)for(Mask a:hi.inds){
                Mask parity=p?(all^row.even):row.even;
                Mask u=(a|parity)&((a&parity)|(all^(1u<<row.r)));
                int low=lo.ell[u];
                if(low+rank.b+1!=1+size(a)+size(parity))continue;
                c.profiles++;
                Mask common=h[i]&h[j];
                for(Mask t=common;t;t&=t-1){
                    int w=first(t);
                    if(lo.connected(all^(1u<<w)))continue;
                    c.witnesses++;
                    if(hi.ell[u&~tips]>low)c.firsts++;
                    if(c.witnesses<=10)std::cout<<"CUT "<<word<<" r "<<row.r<<" p "<<p<<" A "<<a<<" x y w "<<i<<" "<<j<<" "<<w<<" degree "<<size(h[i])<<" "<<size(h[j])<<" ell "<<low<<" rank "<<rank.b+1<<std::endl;
                }
            }
        }
    }
}
int main(){
    Counts c;std::string word;while(std::cin>>word)check(word,c);
    std::cout<<"upper graphs "<<c.graphs<<" roots with tested chords "<<c.roots<<" tight profiles "<<c.profiles
      <<" cut profiles "<<c.witnesses<<" cut profiles with first form "<<c.firsts<<"\n";
}
