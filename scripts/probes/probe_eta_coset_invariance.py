import numpy as np
# Claim: eta_{c b} = eta_b for any c in G=mu_n (multiplicative coset invariance).
# Because eta_b = sum_{x in G} psi(b x); c*G = G for c in G (subgroup), so reindex x->c^{-1}x... wait:
# eta_{cb} = sum_{x in G} psi(c b x) = sum_{x in G} psi(b (c x)); cx ranges over G as x does (c in G).
# So eta_{cb} = sum_{y in G} psi(b y) = eta_b. Holds for ANY field, c in G. Verify.
for (p,n) in [(257,16),(257,8),(193,8),(97,16),(73,9),(41,5)]:
    if (p-1)%n: continue
    G=sorted({x for x in range(1,p) if pow(x,n,p)==1})
    w=np.exp(2j*np.pi/p)
    eta=np.array([sum(w**((b*x)%p) for x in G) for b in range(p)])
    ok=True
    for b in range(p):
        for c in G:
            if abs(eta[(c*b)%p]-eta[b])>1e-9: ok=False
    print(f"p={p} n={n}: eta_{{cb}}=eta_b for all c in G, all b: {ok}")
