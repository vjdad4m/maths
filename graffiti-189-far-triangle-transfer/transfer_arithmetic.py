from itertools import product

# Necessary numerical constraints under the hypothesis that no high
# double porter is produced.  These are profile checks, not graph searches.
for delta in (0, 1):  # star size d+delta
    survivors = []
    for d in range(6, 40):
        rows = []
        for q, l, i, m, b2, sig, rho in product(range(d+1), range(5), range(4), range(2), range(2), range(2), range(2)):
            if sig+rho+delta>1 or b2>rho: continue
            if q<1 or q>1+i+b2 or i>1+sig: continue
            if m>sig or l!=i+m: continue
            T = q+sig+delta
            cut = d-2
            dark = cut - 1 - l
            if dark<0 or dark>T+b2: continue
            rows.append((q,l,i,m,b2,sig,rho))
        if rows:
            survivors.append(d)
            print(delta,d,rows[0])
    assert max(survivors) == (10 if delta == 0 else 7)
