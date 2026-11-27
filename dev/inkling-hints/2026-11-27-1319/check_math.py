"""Small exact checks for the November 27 handoff. Not Lean verification."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, factorial
from functools import lru_cache

Q3 = F(172379525755689183991816396516567920780192827919620440221147749,
       6691837923759692633601708022649918108038775216019298375918637677488)
EPS = F(1, 1000)

def owners(n):
    return sorted(set(permutations([i for i, k in enumerate(n) for _ in range(k)])))

def hist(a, colors, p, c):
    return tuple(sum(i == u and j == v for i, j in zip(a, colors))
                 for u in range(p) for v in range(c))

def moves(a, i, j, k):
    for u in combinations([x for x, y in enumerate(a) if y == i], k):
        for v in combinations([x for x, y in enumerate(a) if y == j], k):
            b = list(a)
            for x in u: b[x] = j
            for x in v: b[x] = i
            yield tuple(b)

def check_fixed_pair():
    rows = edges = fibers = 0
    for n, colors, c in [((2,2,1),(0,1,1,2,0),3), ((3,2,1),(0,0,1,2,2,1),3),
                         ((0,2,2),(0,0,1,1),3), ((1,1,1),(0,1,2),3), ((0,0),(),2)]:
        p = len(n); A = owners(n); N = len(colors)
        hs = Counter(hist(a,colors,p,c) for a in A)
        for h, count in hs.items():
            num = 1; den = 1
            for j in range(c): num *= factorial(colors.count(j))
            for x in h: den *= factorial(x)
            assert count * den == num
            fibers += 1
        for i,j in combinations(range(p),2):
            for k in range(min(n[i],n[j])+1):
                table = {a: Counter(moves(a,i,j,k)) for a in A}
                quotient = {}
                for a, row in table.items():
                    assert len(row) == comb(n[i],k)*comb(n[j],k)
                    assert all(x == 1 for x in row.values())
                    x = hist(a,colors,p,c); hrow = Counter()
                    for b, mass in row.items():
                        assert table[b][a] == mass
                        hrow[hist(b,colors,p,c)] += mass
                        edges += 1
                    assert quotient.setdefault(x,hrow) == hrow
                    rows += 1
                for x,row in quotient.items():
                    for y,w in row.items():
                        assert hs[x]*w == hs[y]*quotient[y][x]
    print(f'fixed pair: {rows} rows, {edges} reversible edges, {fibers} factorial histogram fibers')

# Adjacent decks: swap four ordered noise pairs, leave all other pairs alone.
def swap(d, i, j):
    z = list(d); z[i], z[j] = z[j], z[i]; return tuple(z)

def check_coupling():
    count = 0
    for n in range(2,7):
        for d in permutations(range(n)):
            for a,b in combinations(range(n),2):
                e = swap(d,a,b)
                reparam = {(a,a):(a,b),(a,b):(a,a),(b,b):(b,a),(b,a):(b,b)}
                assert len(set(reparam.values())) == 4
                eq = 0
                for i,j in product(range(n),repeat=2):
                    k,l = reparam.get((i,j),(i,j))
                    u,v = swap(d,i,j),swap(e,k,l)
                    diff = sum(x!=y for x,y in zip(u,v))
                    assert diff in (0,2)
                    eq += (diff == 0); count += 1
                assert eq == 4
    print(f'coupling: {count} adjacent ordered-noise outcomes')

@lru_cache(None)
def eulerian(n):
    if n == 1: return (1,)
    old = eulerian(n-1)
    return tuple((d+1)*(old[d] if d < len(old) else 0) +
                 (n-d)*(old[d-1] if d else 0) for d in range(n))

def numerator(n, a, d):
    top = a+n-1-d
    return comb(top,n) if top >= n else 0

@lru_cache(None)
def gsr_classes(n,t):
    a = 2**t; den = a**n
    E = eulerian(n)
    nums = tuple(numerator(n,a,d) for d in range(n))
    assert sum(E) == factorial(n)
    assert sum(w*v for w,v in zip(E,nums)) == den
    return tuple(zip(E,nums)),den

def gsr_product_tv(t,u):
    a,da = gsr_classes(50,t); b,db = gsr_classes(49,u)
    M = factorial(50)*factorial(49); D = da*db
    return F(sum(e*f*abs(v*w*M-D) for e,v in a for f,w in b),2*M*D)

def check_cost():
    collision = lambda r,s: Q3 + F(1225,2**r) + F(1176,2**s)
    opt = min((r+s,r,s) for r in range(44) for s in range(44) if collision(r,s) < EPS)
    assert opt == (43,21,22) or opt == (43,22,21)
    assert collision(22,21) < EPS
    assert min(collision(r,42-r) for r in range(43)) >= EPS
    print('collision optimal total', opt[0], 'chosen feasible 22+21',float(collision(22,21)))
    for budget in range(28,35):
        # full finite frontier; exact arithmetic, no permutation enumeration
        val,r = min((Q3+gsr_product_tv(r,budget-r),r) for r in range(budget+1))
        print('exact descent budget',budget,'best split',r,budget-r,'upper',float(val))
        if val < EPS:
            print('first certified total (among checked budgets):',budget); break
    # independent check of descent formula on small label arrays
    for n in range(1,6):
        for a in range(1,5):
            cnt = Counter(tuple(sorted(range(n),key=lambda i:(l[i],i)))
                          for l in product(range(a),repeat=n))
            for d in permutations(range(n)):
                desc = sum(x>y for x,y in zip(d,d[1:]))
                assert cnt[d] == numerator(n,a,desc)
    print('small stable-sort descent formula checked')

if __name__ == '__main__':
    check_fixed_pair(); check_coupling(); check_cost()
