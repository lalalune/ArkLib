import itertools
def s_exists(n, s):
    """Does a valid e2=0 config with exactly s singles exist? Uses the exact balance criterion."""
    h=n//2
    # singles: choose s distinct classes (0..h-1) and a sign (position = class or class+h)
    for classes in itertools.combinations(range(h), s):
        for signs in itertools.product([0,1], repeat=s):
            Q=[classes[t]+signs[t]*h for t in range(s)]  # positions
            # half-half sums
            r=[0]*n
            for i in range(s):
                for j in range(i+1,s):
                    r[(Q[i]+Q[j])%n]+=1
            ok=True
            need_pos=[]  # even positions needing a full pair (+1)
            for c in range(h):
                d=r[c]-r[c+h]
                cc, cch = c, c+h
                if c%2==1 and (c+h)%2==1:  # both odd? h even so c and c+h same parity
                    pass
                if (c%2)==1:  # odd fiber: no full-pair help
                    if d!=0: ok=False; break
                else:  # even fiber
                    if abs(d)>1: ok=False; break
                    if d==1: need_pos.append(c+h)   # add +1 at c+h
                    elif d==-1: need_pos.append(c)   # add +1 at c
            if not ok: continue
            # check full-pair indices available: position p (even) <- index i with 2i+h=p mod n, i not a single class, distinct
            used_classes=set(classes); idxs=set(); good=True
            for p in need_pos:
                # 2i+h ≡ p mod n  => i ≡ (p-h)*inv2 ... since gcd(2,n)=2 and p-h even, i=((p-h)//2) mod h has 2 solutions; pick available
                base=((p-h)%n)
                if base%2!=0: good=False; break
                cand=[(base//2)%h, ((base//2)+h//1)%h]  # two candidate indices mod h? actually i in 0..h-1
                placed=False
                for i in range(h):
                    if (2*i+h)%n==p and i not in used_classes and i not in idxs:
                        idxs.add(i); placed=True; break
                if not placed: good=False; break
            if good:
                return True, Q, sorted(idxs)
    return False, None, None
for n in [8,16,32,64]:
    mu=n.bit_length()-1
    smax=0; ex=None
    for s in range(1, mu+2):
        e,Q,F=s_exists(n,s)
        if e: smax=s; ex=(Q,F)
        else:
            # don't break: higher s might still exist even if this s pattern missed (but monotone-ish); check next anyway
            pass
    print(f"n={n} (mu={mu}): s_max = {smax}   (mu-1={mu-1})   example singles+fullpairs={ex}", flush=True)
