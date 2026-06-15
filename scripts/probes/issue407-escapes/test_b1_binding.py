import random
random.seed(2)

def is_prime(p):
    if p<2: return False
    return all(p%d for d in range(2,int(p**0.5)+1))

def find_primes(n,count,start):
    out=[]; p=start
    while len(out)<count:
        p+=1
        if is_prime(p) and (p-1)%n==0: out.append(p)
    return out

def subgroup(p,n):
    def is_pr(g):
        x=1;seen=set()
        for _ in range(p-1):
            x=x*g%p; seen.add(x)
        return len(seen)==p-1
    g=2
    while not is_pr(g): g+=1
    h=pow(g,(p-1)//n,p)
    return [pow(h,j,p) for j in range(n)]

# Reproduce the in-tree _IsolatedCountKelley worst case: (a,b)=(10,4), k=4, antipodal descent.
# Exhaustively search codeword coeffs over a small prime to find max isolated count.
def max_iso_exhaustive(p,n,a,b,k,S):
    # h = x^a + gamma x^b - c, c deg<k. We want max |{x in mu: h(x)=0, x on no coset}|.
    # Exhaustive over gamma and c coeffs is p^(k+1); only feasible tiny p. Instead:
    # The agreement set for FIXED (a,b,gamma) is determined: for each x, x^a+gamma x^b is a target value t(x);
    # a deg<k codeword agrees at x iff c(x)=t(x). Max agreement set = largest subset T of mu interpolable by deg<k poly.
    # T interpolable by deg<k <=> the (|T|) x k Vandermonde system has the target in column space <=>
    # all (k+1)-subsets of T have vanishing divided difference... Equivalent: build for each gamma the function t(x),
    # find max subset on which t restricted is a deg<k poly. This = (#agreement) <= via the root bound deg(x^a+gamma x^b - c).
    # Simplify: enumerate over gamma; the MAX agreement c is the deg<k poly best-fitting; agreement set size =
    # n - (min # points to delete to make t a deg<k poly). For exact: a subset T is agreement set iff
    # divided differences of order k vanish on T. We compute max such T greedily/exactly for small n.
    best=0; best_g=None
    for gamma in range(1,p):
        t=[ (pow(x,a,p)+gamma*pow(x,b,p))%p for x in S ]
        # find largest subset of indices where t is interpolated by deg<k poly.
        # t over subset T (points S[i]) is deg<k iff for all (k+1)-tuples the k-th divided difference =0.
        # Easiest exact for small n: a deg<k poly is determined by any k points; check how many of the other points it hits.
        # Take all C(n,k) choices of k anchor points, fit unique poly, count agreement. Expensive but n<=16 ok-ish.
        # Cheaper: the agreement set is root set of (x^a+gamma x^b - c). For the MAX, choose c interpolating k of the points.
        from itertools import combinations
        idxs=list(range(n))
        # to bound cost, sample anchor sets
        anchors = list(combinations(idxs,k))
        if len(anchors)>4000:
            anchors=random.sample(anchors,4000)
        for anc in anchors:
            # fit deg<k poly through (S[i], t[i]) for i in anc, evaluate at all, count matches
            xs=[S[i] for i in anc]; ys=[t[i] for i in anc]
            # Lagrange over F_p
            def evalpoly(z):
                res=0
                for i in range(k):
                    num=1;den=1
                    for j in range(k):
                        if i==j:continue
                        num=num*((z-xs[j])%p)%p
                        den=den*((xs[i]-xs[j])%p)%p
                    res=(res+ys[i]*num*pow(den,p-2,p))%p
                return res
            cnt=sum(1 for i in idxs if evalpoly(S[i])==t[i])
            if cnt>best: best=cnt; best_g=gamma
    return best,best_g

# The "isolated" count after stripping cosets is what matters. But for the BINDING question we want
# total far-incidence-relevant agreement. Let's instead test comment-125 directly:
# At the delta*-crossing, compare:
#  (A) max agreement of a HIGH/imprimitive monomial direction (the e2 / Kambire locus)  -- the "off-BGK" claim
#  (B) max agreement of LOW-exponent x^k direction                                       -- the "secretly BGK" claim
# If (B) >= (A) at the crossing => the binding family is low-exponent => secretly BGK.

def max_agreement_monomial(p,n,b,k,S):
    # direction x^b alone (gamma=0): agreement with deg<k codeword.
    # = n - (n - max root set of x^b - c). By FarThresholdMaximality, <= (b mod n) if k<=(b mod n).
    # max agreement = largest subset interpolable. For pure monomial: c(x)=x^b restricted; deg<k iff (b mod n)<k trivially.
    # If (b mod n)>=k, max agreement = (b mod n)?? Actually root bound says <= b mod n. Achievable when x^b agrees with
    # the unique deg<k interp on a (b mod n)-subset. Let's just measure via anchor-fit with gamma=0.
    bb=b%n
    t=[pow(x,bb,p) for x in S]
    from itertools import combinations
    best=0
    idxs=list(range(n))
    anchors=list(combinations(idxs,k))
    if len(anchors)>3000: anchors=random.sample(anchors,3000)
    for anc in anchors:
        xs=[S[i] for i in anc]; ys=[t[i] for i in anc]
        def ev(z):
            res=0
            for i in range(k):
                num=1;den=1
                for j in range(k):
                    if i==j:continue
                    num=num*((z-xs[j])%p)%p; den=den*((xs[i]-xs[j])%p)%p
                res=(res+ys[i]*num*pow(den,p-2,p))%p
            return res
        cnt=sum(1 for i in idxs if ev(S[i])==t[i])
        best=max(best,cnt)
    return best

n=16; k=4
primes=find_primes(n,3,200)
print(f"== n={n} k={k}, mu_n smooth subgroup ==")
for p in primes:
    S=subgroup(p,n)
    # low exponents (far set near capacity): b in [k, n) ; high/imprimitive: b=n/2+1=9 etc
    low = [max_agreement_monomial(p,n,b,k,S) for b in range(k,n)]
    print(f" p={p}: monomial max-agreement by exponent b=k..n-1: {list(zip(range(k,n),low))}")
