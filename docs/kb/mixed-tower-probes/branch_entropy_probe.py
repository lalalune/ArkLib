import itertools, random, math
# n=16 domain mu_16 in F_97; k=3 (29791 codewords); deep lists at agreement a = k+t
p=97; n=16
g=None
for c in range(2,p):
    if pow(c,16,p)==1 and pow(c,8,p)!=1: g=c; break
D=[pow(g,i,p) for i in range(16)]
# all deg<3 polys
codewords=[]
for a0 in range(p):
    for a1 in range(p):
        for a2 in range(p):
            codewords.append(tuple((a0+a1*x+a2*x*x)%p for x in D))
print("codewords:",len(codewords))
def branch_tree(S):
    # S = error support (frozenset of domain points); descend by squaring, branches split by even/odd fold ALIVENESS
    # alive pattern: at each level, for current 'support multiset' we just track SUPPORT of folds (values matter for aliveness; use generic values -> both folds alive unless fiber kills)
    # SIMPLE proxy: count total nodes of the support-descent tree: supports halve via squaring; splits = levels where |S| stays > |S^2| pairs...
    # measurable proxy: sequence of |S^(2^j)| sizes
    sizes=[]
    cur=set(S)
    while cur and len(sizes)<5:
        sizes.append(len(cur))
        cur={ (x*x)%p for x in cur }
    return tuple(sizes)
random.seed(2)
results=[]
for t in [2,3,4]:
    a=3+t; w=n-a
    maxlist=0; trees=None
    for trial in range(60):
        # received word: random codeword + random weight-w error (planted), plus pure random words
        if trial%2==0:
            cw=random.choice(codewords)
            S=random.sample(range(16),w)
            r=list(cw)
            for i in S: r[i]=(r[i]+random.randrange(1,p))%p
        else:
            r=[random.randrange(p) for _ in range(16)]
        # list at agreement >= a
        lst=[cw for cw in codewords if sum(1 for i in range(16) if cw[i]==r[i])>=a]
        if len(lst)>maxlist:
            maxlist=len(lst)
            trees=[branch_tree(frozenset(D[i] for i in range(16) if cw[i]!=r[i])) for cw in lst[:8]]
    print(f"t={t} (a={a}, w={w}): max list={maxlist}; sample support-descent size-sequences: {trees[:4] if trees else None}")
