import itertools, math
def distinct_subset_sums(N, j):
    h=N//2; vals=set()
    for I in itertools.combinations(range(N), j):
        v=[0]*h
        for i in I: v[i%h]+= (1 if i<h else -1)
        vals.add(tuple(v))
    return len(vals)
def closed_m2(N,j):
    return sum(math.comb(N//2,s)*(2**s) for s in range(0,min(j,N-j)+1) if (s%2)==(j%2))
print("VERIFY closed m=2 formula  #bad = Σ_{s≡j(2),s≤min(j,N-j)} C(N/2,s)2^s:")
ok=True
for N in [4,8,16]:
    for j in range(1,N):
        a=distinct_subset_sums(N,j); b=closed_m2(N,j)
        if a!=b: ok=False; print(f"  MISMATCH N={N} j={j}: brute={a} closed={b}")
print("  all match!" if ok else "  MISMATCHES above")
# m=4 recursion test: #bad(m=4) = #distinct \hat(4) over A with \hat(1)=\hat(2)=\hat(3)=0
def fhat(A,jj,n,h):
    v=[0]*h
    for a in A: v[(jj*a)%n % h]+= (1 if (jj*a)%n<h else -1)
    return tuple(v)
def count_flat(n,k,m):
    h=n//2; w=k+m; vals=set(); Z=tuple([0]*h)
    for A in itertools.combinations(range(n),w):
        if all(fhat(A,j,n,h)==Z for j in range(1,m)): vals.add(fhat(A,m,n,h))
    return len(vals)
print("\n#bad(m) for n=16 (full), n=32 (small w):")
for (n,k,m) in [(16,8,2),(16,8,4),(16,4,2),(16,4,4),(16,2,2),(16,2,4),(16,2,6)]:
    print(f"  n={n} k={k} m={m} (w={k+m}): #bad={count_flat(n,k,m)}", flush=True)
