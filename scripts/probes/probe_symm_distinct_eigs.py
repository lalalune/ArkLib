import numpy as np
# On symmetric G, eta is real AND even in b. Distinct non-principal eigenvalues come in b<->-b pairs.
# NEW structural question: does the b<->-b pairing + realness give a constraint on the
# distinct-eigenvalue SUM or the max beyond what's known? Check: sum over a transversal of pairs.
# Also: is there a clean count of DISTINCT eta values (multiplicity structure)?
for (p,n) in [(257,16),(257,8),(193,8),(97,16)]:
    if (p-1)%n: continue
    G=sorted({x for x in range(1,p) if pow(x,n,p)==1})
    w=np.exp(2j*np.pi/p)
    eta=np.array([sum(w**((b*x)%p) for x in G).real for b in range(p)])  # real part (eta is real)
    nz=eta[1:]  # non-principal
    # distinct values + multiplicities
    vals,counts=np.unique(np.round(nz,6),return_counts=True)
    # how many distinct, and is every multiplicity even (b<->-b) except possibly self-paired b=-b?
    selfpaired=[b for b in range(1,p) if (b%p)==((-b)%p)]  # b=-b mod p only b=0 for odd p; none nonzero
    print(f"p={p} n={n}: {len(vals)} distinct non-principal eigenvalues among {len(nz)} freqs; "
          f"mult parity all-even={all(c%2==0 for c in counts)}; self-paired nz freqs={selfpaired}")
    print(f"    max non-principal |eta| = {np.max(np.abs(nz)):.4f}  (sqrt(n log(p/n))={np.sqrt(n*np.log(p/n)):.4f}, sqrt n={np.sqrt(n):.4f})")
