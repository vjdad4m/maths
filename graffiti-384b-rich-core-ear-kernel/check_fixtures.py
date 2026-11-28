"""Independent diagnostic on three fixed rooted examples. The Lean proof does not call this script."""
from functools import lru_cache
from itertools import combinations

def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit

def graph6(code):
    n = ord(code[0]) - 63
    masks = [0] * n
    pos = 0
    for j in range(n):
        for i in range(j):
            if (ord(code[1 + pos // 6]) - 63) >> (5 - pos % 6) & 1:
                masks[i] |= 1 << j
                masks[j] |= 1 << i
            pos += 1
    return masks

def check(code, pairs, root):
    g = graph6(code)
    start = len(g)
    def add_vertex(neighbors):
        v = len(g)
        g.append(0)
        for u in neighbors:
            g[v] |= 1 << u
            g[u] |= 1 << v
    for pair in pairs:
        assert g[pair[0]] >> pair[1] & 1
        add_vertex(pair)
    add_vertex([root])
    scores = [sum((g[u]&g[v]).bit_count() for v in vertices(g[u]))//2 for u in range(len(g))]
    h = sum(1<<u for u,s in enumerate(scores) if s>=2)
    ears = [u for u,s in enumerate(scores) if s==1]
    @lru_cache(None)
    def match(s):
        if not s:return 0
        i = next(vertices(s))
        rem = s ^ (1<<i)
        return max([match(rem)]+[2+match(rem^(1<<j)) for j in vertices(g[i]&rem)])
    families = []
    for k in range(len(ears)+1):
        for F in combinations(ears,k):
            mask = sum(1<<v for v in F)
            if any(g[v]&mask for v in F): continue
            anchors = 0
            for v in F: anchors |= g[v]&h
            w = h&~anchors
            loss = 2*k-anchors.bit_count()
            families.append((F,loss,w.bit_count()-match(w)))
    cap = len(g)-(len(set(scores))+1)//2
    for k in range(len(g)+1):
        for D in combinations(range(len(g)),k):
            d = sum(1<<v for v in D)
            if all((d>>v)&1 or (g[v]&d).bit_count()>=2 for v in range(len(g))):break
        else:continue
        break
    all_inc = all(loss<=1 for _,loss,_ in families)
    all_match = all(gap<=1-loss for _,loss,gap in families) and all(
        match(h | (1<<v))==h.bit_count()+1 for v in ears)
    full = tuple(range(start,start+len(pairs)))
    print(code,'scores',scores,'gamma',k,'bound',cap,'D',D,'all incidence counts',all_inc,
          'all uncolored matching sizes',all_match,'selected family',
          next(x for x in families if x[0]==full))
    return k,cap,all_inc,all_match

if __name__=='__main__':
    assert check('EQzw',[(5,0),(5,4)],0)==(5,5,False,False)
    assert check('FEjvw',[(4,0),(5,3),(6,4)],0)==(6,6,True,False)
    assert check('D^{',[(2,0),(3,2)],0)==(4,4,True,True)
