import itertools

def balanced(sums, n, h):
    from collections import Counter
    c = Counter(s % n for s in sums)
    return all(c[t] == c[(t+h) % n] for t in range(n))

def brute(n):
    h = n // 2
    out = []
    for A in itertools.combinations(range(n), 4):
        sums = [A[i]+A[j] for i in range(4) for j in range(i+1,4)]
        if balanced(sums, n, h):
            out.append(A)
    return out

def matches_ansatz(A, n):
    h = n // 2
    S = set(A)
    for x in A:
        if (x + h) % n in S:
            rest = [u for u in A if u != x and u != (x+h) % n]
            if len(rest) == 2 and (rest[0] + rest[1]) % n == (2*x) % n:
                return True
    return False

for m in range(2, 6):
    n = 2**m
    sols = brute(n)
    formula = n*(n-3)//4
    all_match = all(matches_ansatz(A, n) for A in sols)
    # also check converse: every ansatz config is balanced (sample exhaustively)
    conv = True
    h = n//2
    for x in range(n):
        for y in range(n):
            z = (2*x - y) % n
            A = {x, (x+h)%n, y, z}
            if len(A) == 4:
                sums = [a+b for a,b in itertools.combinations(sorted(A),2)]
                if not balanced(sums, n, h):
                    conv = False
    print(f"n={n}: #balanced={len(sols)} formula={formula} match={len(sols)==formula} ansatz_complete={all_match} ansatz_sound={conv}")
