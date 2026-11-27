"""Small independent exact checks of the new mathematical hints.

These are regressions for the proposed statements, not Lean verification.
Run directly; they are not installed in the routine test suite.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial

F = Fraction
Q2 = F(12255318415559330995522631403472464258192877,
       4933350368865509640837610315994582805439728012)
Q3 = F(172379525755689183991816396516567920780192827919620440221147749,
       6691837923759692633601708022649918108038775216019298375918637677488)
EPS = F(1, 1000)


def check_budgets():
    assert Q2 > EPS
    for a, b in [(23, 23), (22, 22), (22, 21), (21, 22)]:
        assert Q3 + F(1225, 2**a) + F(1176, 2**b) < EPS
    # Any allocation with total cost better than 46 lies within this box.
    feasible = [(a + b, a, b) for a, b in product(range(47), repeat=2)
                if Q3 + F(1225, 2**a) + F(1176, 2**b) < EPS]
    assert min(x[0] for x in feasible) == 43
    assert {x for x in feasible if x[0] == 43} == {(43, 21, 22), (43, 22, 21)}
    assert 3 * F(3, 4)**30 < EPS
    print('Q2:', float(Q2), 'Q3:', float(Q3))
    for a, b in [(23, 23), (22, 22), (22, 21), (21, 22)]:
        print(f'Final {a}+{b} bound:', float(Q3 + F(1225, 2**a) + F(1176, 2**b)))


def push_counts(mu, choices):
    out = Counter()
    for deck, count in mu.items():
        for new in choices(deck):
            out[new] += count
    return out


def tv_uniform(counts, num_states):
    total = sum(counts.values())
    return (sum(abs(F(v, total) - F(1, num_states)) for v in counts.values())
            + F(num_states - len(counts), num_states)) / 2


def check_terminal_reset():
    cases = 0
    # Every start for N<=5; several starts for N=6.
    for n in range(2, 7):
        decks = list(permutations(range(n)))
        starts = decks if n <= 5 else [decks[0], decks[137], decks[-1]]
        for m in range(1, n):
            for k in range(min(m, n-m)+1):
                positions = list(product(combinations(range(m), k), combinations(range(m, n), k)))
                locals_ = list(product(permutations(range(m)), permutations(range(m, n))))
                hcount = len(locals_)
                def swaps(d):
                    for left, right in positions:
                        out = list(d)
                        for i, j in zip(left, right):
                            out[i], out[j] = out[j], out[i]
                        yield tuple(out)
                def reset(d):
                    for l, r in locals_:
                        yield tuple(d[i] for i in l + r)
                for start in starts:
                    plain = ideal = Counter({start: 1})
                    for t in range(1, 4):
                        plain = push_counts(plain, swaps)
                        terminal = push_counts(plain, reset)
                        ideal = push_counts(push_counts(ideal, swaps), reset)
                        # Normalize by the known difference in numbers of samples.
                        assert ideal == Counter({d: v * hcount**(t-1) for d, v in terminal.items()})
                        assert tv_uniform(plain, factorial(n)) >= tv_uniform(terminal, factorial(n))
                        cases += 1
    print('Terminal reset and TV lower-bound rows:', cases)


def check_conditional_hands():
    cases = 0
    for n in range(0, 7):
        decks = list(permutations(range(n)))
        for h in range(n+1):
            for t in range(n-h+1):
                joint = defaultdict(Counter)
                for d in decks:
                    joint[frozenset(d[:h])][frozenset(d[h:h+t])] += 1
                for s, conditional in joint.items():
                    assert len(conditional) == comb(n-h, t)
                    mass = sum(conditional.values())
                    for target, weight in conditional.items():
                        assert len(target) == t and not (s & target)
                        assert F(weight, mass) == F(1, comb(n-h, t))
                        cases += 1
    print('Conditional hand masses:', cases)


def check_fixed_pair():
    rows = 0
    hist_rows = 0
    for capacities, colors in [((2, 1, 1), (0, 0, 1, 1)),
                               ((2, 2, 1), (0, 0, 1, 1, 2)),
                               ((0, 3, 2), (0, 1, 1, 2, 2)),
                               ((2, 2, 2), (0, 0, 1, 1, 2, 2))]:
        n = sum(capacities)
        p = len(capacities)
        c = max(colors)+1
        states = set(permutations(tuple(i for i, m in enumerate(capacities) for _ in range(m))))
        def hist(a):
            return tuple(sum(a[x] == i and colors[x] == j for x in range(n))
                         for i in range(p) for j in range(c))
        fibers = Counter(map(hist, states))
        for x, count in fibers.items():
            numerator = 1
            for j in range(c):
                numerator *= factorial(colors.count(j))
            denominator = 1
            for value in x:
                denominator *= factorial(value)
            assert count * denominator == numerator
        for i, j in combinations(range(p), 2):
            for k in range(min(capacities[i], capacities[j])+1):
                macro = {}
                microscopic = {}
                for a in states:
                    options = Counter()
                    for u, v in product(combinations([x for x in range(n) if a[x] == i], k),
                                        combinations([x for x in range(n) if a[x] == j], k)):
                        b = list(a)
                        for x in u:
                            b[x] = j
                        for x in v:
                            b[x] = i
                        options[tuple(b)] += 1
                    degree = comb(capacities[i], k)*comb(capacities[j], k)
                    assert len(options) == degree and all(v == 1 for v in options.values())
                    microscopic[a] = options
                    q = Counter()
                    for b, w in options.items():
                        q[hist(b)] += w
                    x = hist(a)
                    if x in macro:
                        assert macro[x] == q
                    else:
                        macro[x] = q
                    rows += 1
                for a, options in microscopic.items():
                    for b, w in options.items():
                        assert microscopic[b][a] == w
                for x, q in macro.items():
                    for y, w in q.items():
                        assert fibers[x]*w == fibers[y]*macro[y][x]
                    hist_rows += 1
    print('Fixed-pair allocation rows:', rows, 'histogram rows:', hist_rows)


if __name__ == '__main__':
    check_budgets()
    check_terminal_reset()
    check_conditional_hands()
    check_fixed_pair()
