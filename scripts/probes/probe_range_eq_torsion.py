# Probe: in finite cyclic group of order N = m*n,
# range(x -> x^m) == {y : y^n == 1}  (the n-torsion subgroup = mu_n)
# AND that set has cardinality exactly n.
# Model F_p^* as Z/(p-1) additively (cyclic of order N=p-1); x^m <-> m*x mod N.

def test(N, m):
    assert N % m == 0
    n = N // m
    rng = set((m * x) % N for x in range(N))
    tors = set(y for y in range(N) if (n * y) % N == 0)
    return rng == tors, len(rng), len(tors), n

primes = [17, 97, 257, 193, 769, 1153, 12289, 40961, 65537, 786433]
fails = 0
tot = 0
for p in primes:
    N = p - 1
    a = 0
    while (2 ** a) <= N:
        n = 2 ** a
        if N % n == 0:
            m = N // n
            ok, lr, lt, nn = test(N, m)
            tot += 1
            if not (ok and lr == nn and lt == nn):
                fails += 1
                print("FAIL p=%d N=%d n=%d m=%d range==tors=%s |rng|=%d |tors|=%d" % (p, N, n, m, ok, lr, lt))
        a += 1
print("range==n-torsion AND |range|=n: %d/%d pass, %d fails" % (tot - fails, tot, fails))

ok, lr, lt, nn = test(65536, 65536 // 16)
print("prize p=65537 n=16 m=4096: range==tors=%s |range|=%d (expect 16)" % (ok, lr))
