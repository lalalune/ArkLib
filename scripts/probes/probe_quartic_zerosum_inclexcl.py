import itertools
# count pattern sets abstractly via index arithmetic mod n, n even, A(i)=i+n/2 mod n.
def counts(n):
    A=lambda i:(i+n//2)%n
    P1=set();P2=set();P3=set()
    for a,b,c,d in itertools.product(range(n),repeat=4):
        if b==A(a) and d==A(c): P1.add((a,b,c,d))
        if c==A(a) and d==A(b): P2.add((a,b,c,d))
        if d==A(a) and c==A(b): P3.add((a,b,c,d))
    U=P1|P2|P3
    print(f"n={n}: |P1|={len(P1)} |P2|={len(P2)} |P3|={len(P3)} "
          f"|P1&P2|={len(P1&P2)} |P1&P3|={len(P1&P3)} |P2&P3|={len(P2&P3)} "
          f"|P1&P2&P3|={len(P1&P2&P3)} |U|={len(U)} 3n(n-1)={3*n*(n-1)}")
for k in range(1,6):
    counts(2**k)
