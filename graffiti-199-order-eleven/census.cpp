#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string_view>
#include <utility>
#include <vector>

namespace {
using Mask = unsigned;
using Code = std::array<Mask, 5>;
constexpr int maxOrder = 12;
using Graph = std::array<Mask, maxOrder>;
constexpr std::array<std::array<int, 3>, 6> orders{{
    {{0,1,2}}, {{0,2,1}}, {{1,0,2}}, {{1,2,0}}, {{2,0,1}}, {{2,1,0}}
}};
constexpr Mask bit(int i) { return 1u << i; }
int count(Mask s) { return std::popcount(s); }
int first(Mask s) { return std::countr_zero(s); }

bool connected(const Graph& adj, Mask vertices) {
    if (!vertices) return false;
    Mask reached = vertices & -vertices;
    Mask frontier = reached;
    while (frontier) {
        int v = first(frontier);
        frontier ^= bit(v);
        Mask next = adj[v] & vertices & ~reached;
        reached |= next;
        frontier |= next;
    }
    return reached == vertices;
}

bool connectedAfterTwoDeletions(const Graph& adj, int n) {
    const Mask all = bit(n) - 1;
    for (int u=0; u<n; ++u)
        for (int v=u+1; v<n; ++v)
            if (!connected(adj, all ^ bit(u) ^ bit(v))) return false;
    // For n >= 4, connectivity after all two-vertex deletions implies
    // connectivity after smaller deletions as well.
    return true;
}

bool sixTree(const Graph& adj, int n) {
    for (Mask s = 0; s < bit(n); ++s) {
        if (count(s) != 6) continue;
        int twiceEdges = 0;
        for (Mask t = s; t; t &= t-1)
            twiceEdges += count(adj[first(t)] & s);
        if (twiceEdges == 10 && connected(adj, s)) return true;
    }
    return false;
}

bool claw(const Graph& adj, int n) {
    for (int v = 0; v < n; ++v) {
        for (Mask x = adj[v]; x; x &= x-1) {
            int a = first(x);
            for (Mask y = (x & (x-1)) & ~adj[a]; y; y &= y-1) {
                int b = first(y);
                if ((y & (y-1)) & ~adj[b]) return true;
            }
        }
    }
    return false;
}

bool independentFive(const Graph& adj, int n) {
    for (Mask s = 0; s < bit(n); ++s) {
        if (count(s) != 5) continue;
        bool independent = true;
        for (Mask t = s; t && independent; t &= t-1)
            independent = !(adj[first(t)] & s);
        if (independent) return true;
    }
    return false;
}

bool hamilton(const Graph& adj, int n) {
    std::array<Mask, 1 << maxOrder> dp{};
    for (int v = 0; v < n; ++v) dp[bit(v)] = bit(v);
    Mask all = bit(n)-1;
    for (Mask u = 1; u < all; ++u)
        for (Mask t = dp[u]; t; t &= t-1) {
            int end = first(t);
            for (Mask w = adj[end] & ~u; w; w &= w-1) {
                int next = first(w);
                dp[u | bit(next)] |= bit(next);
            }
        }
    return dp[all] != 0;
}

struct Shore {
    int n;
    Code internal{}, ports{};
    std::array<int,3> portDegrees{}, independentContacts{};
    std::array<Mask,6> gapMasks{};
    std::array<std::array<std::array<Mask,3>,8>,6> allowedB{};
    bool cubicPathTwins = false;
    bool supportedRoute = false;
};

std::vector<std::array<int,5>> permutations(int n) {
    std::vector<std::array<int,5>> result;
    std::array<int,5> p{0,1,2,3,4};
    do { result.push_back(p); } while (std::next_permutation(p.begin(), p.begin()+n));
    return result;
}

std::vector<std::pair<int,int>> pairs(int n) {
    std::vector<std::pair<int,int>> result;
    for (int i=0; i<n; ++i)
        for (int j=i+1; j<n; ++j)
            result.emplace_back(i,j);
    return result;
}

int localDegree(const Shore& c, int v) { return count(c.internal[v]) + count(c.ports[v]); }

Mask requiredGaps(const std::array<int,3>& p, Mask cutEdges) {
    auto hasEdge = [cutEdges](int a, int b) {
        return cutEdges & bit(a+b-1); // 01 -> 0, 02 -> 1, 12 -> 2.
    };
    return (hasEdge(p[0],p[1]) ? 0 : bit(1)) | (hasEdge(p[1],p[2]) ? 0 : bit(2));
}

void fillGapMasks(Shore& c) {
    Mask all = bit(c.n)-1;
    const int noPort = 3;
    std::array<std::array<std::array<bool,32>,4>,4> can{};
    for (int left = 0; left <= noPort; ++left) {
        std::array<Mask,32> endpoints{};
        for (int v = 0; v < c.n; ++v)
            if (left == noPort || (c.ports[v] & bit(left))) endpoints[bit(v)] = bit(v);
        for (Mask s = 1; s <= all; ++s) {
            for (Mask ends = endpoints[s]; ends; ends &= ends-1) {
                int v = first(ends);
                for (int right = 0; right <= noPort; ++right)
                    if (right == noPort || (c.ports[v] & bit(right))) can[left][right][s] = true;
                for (Mask next = c.internal[v] & ~s; next; next &= next-1) {
                    int w = first(next);
                    endpoints[s|bit(w)] |= bit(w);
                }
            }
        }
    }
    for (int p=0; p<3; ++p)
        for (int q=p+1; q<3; ++q)
            c.supportedRoute |= can[p][q][all];
    for (int k = 0; k < 6; ++k) {
        const auto& p = orders[k];
        const int left[4]{noPort,p[0],p[1],p[2]};
        const int right[4]{p[0],p[1],p[2],noPort};
        std::array<Mask,32> configurations{};
        configurations[0] = bit(0);
        for (int gap=0; gap<4; ++gap) {
            auto next = configurations;
            for (Mask s = 0; s <= all; ++s) if (configurations[s]) {
                Mask remain = all & ~s;
                for (Mask path = remain; path; path = (path-1)&remain) if (can[left[gap]][right[gap]][path]) {
                    next[s|path] |= configurations[s] << bit(gap);
                }
            }
            configurations = next;
        }
        c.gapMasks[k] = configurations[all];
        for (int edges=0; edges<8; ++edges)
            for (int extra=0; extra<=2; ++extra) {
                Mask required = requiredGaps(p, edges);
                for (Mask u = c.gapMasks[k]; u; u &= u-1) {
                    Mask ma = first(u);
                    for (Mask mb = 1; mb < 16; ++mb) if (!(ma & mb)) {
                        Mask unused = 15 & ~(ma | mb);
                        if (count(required & unused) <= extra && extra <= count(unused))
                            c.allowedB[k][edges][extra] |= bit(mb);
                    }
                }
            }
    }
}

// Enumerate one representative modulo permutations of a component.
// The cut remains labeled. Match equivalent components only when their
// internal edge masks are the same, and then use graph automorphisms.
std::vector<Shore> shoreCatalogue(int n) {
    std::vector<Shore> result;
    auto perm = permutations(n);
    auto edges = pairs(n);
    for (Mask internal=0; internal<bit(edges.size()); ++internal) {
        Shore base{};
        base.n = n;
        for (unsigned k=0; k<edges.size(); ++k) if (internal & bit(k)) {
            auto [u,v] = edges[k];
            base.internal[u] |= bit(v);
            base.internal[v] |= bit(u);
        }
        Graph check{};
        std::copy(base.internal.begin(),base.internal.end(),check.begin());
        if (!connected(check,bit(n)-1)) continue;
        std::vector<std::array<int,5>> automorphisms;
        bool canonical = true;
        for (const auto& p : perm) {
            Mask relabeled = 0;
            for (unsigned k=0; k<edges.size(); ++k) {
                auto [u,v] = edges[k];
                if (base.internal[p[u]] & bit(p[v])) relabeled |= bit(k);
            }
            if (relabeled < internal) { canonical = false; break; }
            if (relabeled == internal) automorphisms.push_back(p);
        }
        if (!canonical) continue;
        for (Mask attachment=0; attachment<bit(3*n); ++attachment) {
            Shore s = base;
            bool possible = true;
            for (int v=0; v<n; ++v) {
                s.ports[v] = (attachment >> (3*v)) & 7;
                if (localDegree(s,v) < 3) { possible = false; break; }
            }
            if (!possible) continue;
            for (unsigned k=0; k<edges.size() && possible; ++k) if (internal & bit(k)) {
                auto [u,v] = edges[k];
                if (localDegree(s,u)==3 && localDegree(s,v)==3) possible=false;
            }
            if (!possible) continue;
            for (Mask subset=1; subset<8 && possible; ++subset) {
                int contacts=0;
                for (int v=0; v<n; ++v) contacts += !!(s.ports[v] & subset);
                if (contacts < count(subset)) possible=false;
            }
            if (!possible) continue;
            for (const auto& p : automorphisms) {
                Mask relabeled = 0;
                for (int v=0; v<n; ++v) relabeled |= s.ports[p[v]] << (3*v);
                if (relabeled < attachment) { possible = false; break; }
            }
            if (!possible) continue;
            for (int q=0; q<3; ++q) {
                Mask touches=0;
                for (int v=0; v<n; ++v) if (s.ports[v]&bit(q)) touches |= bit(v);
                s.portDegrees[q]=count(touches);
                for (Mask t=touches; t; t=(t-1)&touches) {
                    bool independent=true;
                    for (Mask u=t; u && independent; u&=u-1)
                        independent=!(s.internal[first(u)]&t);
                    if (independent) s.independentContacts[q]=std::max(s.independentContacts[q],count(t));
                }
            }
            if (n==3 && count(internal)==2) {
                int middle=0;
                while (count(s.internal[middle]) != 2) ++middle;
                int u=(middle+1)%3, v=(middle+2)%3;
                s.cubicPathTwins = s.ports[u]==s.ports[v] && count(s.ports[u])==2 &&
                    count(s.ports[middle])>=2 && (s.ports[middle] & (7 ^ s.ports[u]));
            }
            fillGapMasks(s);
            result.push_back(s);
        }
    }
    return result;
}

Graph graph(const Shore& a, const Shore& b, int extra, Mask edges) {
    Graph adj{};
    auto add = [&adj](int u, int v) { adj[u]|=bit(v); adj[v]|=bit(u); };
    for (int i=0; i<3; ++i)
        for (int j=i+1; j<3; ++j)
            if (edges & bit(i+j-1)) add(i,j);
    auto install = [&](const Shore& shore, int offset) {
        for (int i=0; i<shore.n; ++i) {
            for (int j=i+1; j<shore.n; ++j)
                if (shore.internal[i]&bit(j)) add(i+offset,j+offset);
            for (int p=0; p<3; ++p)
                if (shore.ports[i]&bit(p)) add(i+offset,p);
        }
    };
    install(a,3);
    install(b,3+a.n);
    for (int x=0; x<extra; ++x)
        for (int p=0; p<3; ++p) add(3+a.n+b.n+x,p);
    return adj;
}

bool routingDP(const Shore& a, const Shore& b, int extra, Mask edges) {
    for (int k=0; k<6; ++k)
        if (a.allowedB[k][edges][extra] & b.gapMasks[k]) return true;
    return false;
}

bool oneIntervalForEach(const Shore& a, const Shore& b, int extra, Mask edges) {
    const Mask singletonGaps = bit(1)|bit(2)|bit(4)|bit(8);
    for (int k=0; k<6; ++k) {
        Mask need = requiredGaps(orders[k],edges);
        for (Mask x=a.gapMasks[k] & singletonGaps; x; x&=x-1)
            for (Mask y=b.gapMasks[k] & singletonGaps; y; y&=y-1) {
                Mask ma=first(x), mb=first(y);
                if (ma&mb) continue;
                Mask unused=15&~(ma|mb);
                if (count(need&unused)<=extra && extra<=count(unused)) return true;
            }
    }
    return false;
}

void dump(const Graph& adj, int n) {
    for (int v=0; v<n; ++v)
        for (int w=v+1; w<n; ++w)
            if (adj[v]&bit(w)) std::cout << ' ' << v << '-' << w;
    std::cout << '\n';
}

void census(const std::vector<Shore>& left, const std::vector<Shore>& right, int extra) {
    int n=3+left.front().n+right.front().n+extra;
    std::uint64_t profiles=0, noStar=0, high=0, noPath=0, six=0, disconnected=0, counter=0, samples=0;
    bool witness=false, twinWitness=false;
    for (const Shore& a:left) for (const Shore& b:right) {
        ++profiles;
        bool star=false;
        for (int p=0;p<3;++p)
            star |= a.independentContacts[p]+b.independentContacts[p]+extra>=5;
        if (star) continue;
        ++noStar;
        for (Mask edges=0; edges<8; ++edges) {
            bool ok=true;
            for (int p=0;p<3;++p) {
                int degree=a.portDegrees[p]+b.portDegrees[p]+extra;
                for (int q=0;q<3;++q)
                    if (p!=q && (edges&bit(p+q-1))) ++degree;
                if (degree<4) ok=false;
            }
            if (!ok) continue;
            ++high;
            bool route = routingDP(a,b,extra,edges);
            if ((high^(high>>16))%89003==0) {
                ++samples;
                if (route!=hamilton(graph(a,b,extra,edges),n))
                    throw std::runtime_error("gap DP disagrees with the independent subset DP");
            }
            if (route) {
                if ((!witness || (!twinWitness && a.cubicPathTwins)) &&
                    !oneIntervalForEach(a,b,extra,edges)) {
                    auto adj=graph(a,b,extra,edges);
                    if (connectedAfterTwoDeletions(adj,n) && !sixTree(adj,n) &&
                        claw(adj,n) && independentFive(adj,n)) {
                        if (!witness || (!twinWitness && a.cubicPathTwins && !b.supportedRoute)) {
                            std::cout << "routing-limit witness " << a.n << '+' << b.n
                                      << '+' << extra << " twin=" << a.cubicPathTwins
                                      << " other-route=" << b.supportedRoute << ':';
                            dump(adj,n);
                            witness=true;
                            twinWitness |= a.cubicPathTwins && !b.supportedRoute;
                        }
                    }
                }
                continue;
            }
            ++noPath;
            auto adj=graph(a,b,extra,edges);
            if (hamilton(adj,n)) throw std::runtime_error("negative gap DP disagrees with the independent subset DP");
            if (sixTree(adj,n)) { ++six; continue; }
            if (!connectedAfterTwoDeletions(adj,n)) { ++disconnected; continue; }
            ++counter;
            std::cout << "counterexample:";
            dump(adj,n);
            std::cout << "claw=" << claw(adj,n) << " independent-five=" << independentFive(adj,n) << '\n';
        }
    }
    std::cout << "shape " << left.front().n << '+' << right.front().n << '+' << extra
              << ": profiles=" << profiles << " star-free-pairs=" << noStar
              << " high-cut=" << high << " no-path=" << noPath << " induced-six-tree=" << six
              << " fails-three-connectivity=" << disconnected << " counterexamples=" << counter
              << " sampled-reference-checks=" << samples << std::endl;
}
} // namespace

int main(int argc, char** argv) {
    if (argc > 2 || (argc == 2 && std::string_view(argv[1]) != "--order-twelve")) {
        std::cerr << "Usage: census [--order-twelve]\n";
        return 2;
    }
    auto three=shoreCatalogue(3), four=shoreCatalogue(4), five=shoreCatalogue(5);
    std::cout << "catalogues: " << three.size() << ", " << four.size() << ", " << five.size() << std::endl;
    if (argc == 2) {
        census(three,four,2);
        census(four,four,1);
        census(three,five,1);
        census(four,five,0);
    } else {
        census(three,three,2);
        census(three,four,1);
        census(four,four,0);
        census(three,five,0);
    }
}
