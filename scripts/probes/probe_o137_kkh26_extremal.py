# O137: the KKH26 monomial-pair stack (X^3, X^2) is EXTREMAL at RS[F5,(1,2,4,3),2], delta=1/4:
# bad gamma set = {1,2,3,4} = census-law prediction = proven worst case (4).
# Care: (X^2, X) fires zero bad gammas (direction row X is a codeword).
from itertools import combinations
p, n = 5, 4
xs = [1, 2, 4, 3]
cws = [tuple((a + b*x) % p for x in xs) for a in range(p) for b in range(p)]
subsets3 = [S for r in (3, 4) for S in combinations(range(n), r)]
def ext(w, S):
    return any(all(c[i] == w[i] for i in S) for c in cws)
def badset(u0, u1):
    out = []
    for g in range(p):
        line = tuple((a + g*b) % p for a, b in zip(u0, u1))
        if any(ext(line, S) and not (ext(u0, S) and ext(u1, S)) for S in subsets3):
            out.append(g)
    return out
b3 = badset(tuple(pow(x,3,p) for x in xs), tuple(pow(x,2,p) for x in xs))
b2 = badset(tuple(pow(x,2,p) for x in xs), tuple(x % p for x in xs))
assert b3 == [1,2,3,4], b3
assert b2 == [], b2
print("(X^3,X^2) bad =", b3, "= census prediction; EXTREMAL (max=4).  (X^2,X) bad =", b2)
