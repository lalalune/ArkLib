"""
Attack the decay law A_r/Wick ~ exp(-r^2/2n) by DERIVING it. Test exact mechanisms:
(M1) Is the CHAR-0 A_r/Wick exactly a product/closed form? Compare to:
     - prod_{j=1}^{r-1}(1-j/n)  [falling factorial]
     - n!/(n-r)!/n^r = prod(1-j/n) [same]
     - the 'distinct-residue' fraction
(M2) The step ratio E_{r+1}/E_r vs (2r+1)n: char-0 exact closed form?
(M3) Does A_r = (2r-1)!! * (n)_r (falling factorial n(n-1)...(n-r+1))? Test EXACTLY with char-0 closed forms.
(M4) The Wick excess: Wick - E_r^char0 = ? (the SOS deficit). Closed form?
"""
def E0(r,n):  # char-0 exact closed forms (in-tree)
    return {2:3*n**2-3*n,3:15*n**3-45*n**2+40*n,4:105*n**4-630*n**3+1435*n**2-1155*n,
            5:945*n**5-9450*n**4+39375*n**3-77175*n**2+57456*n,
            6:10395*n**6-155925*n**5+1022175*n**4-3534300*n**3+6246471*n**2-4370520*n,
            7:135135*n**7-2837835*n**6+26801775*n**5-141891750*n**4+433726293*n**3-708996288*n**2+471556800*n}[r]
def dfac(k):
    r=1
    for i in range(1,2*k,2): r*=i
    return r
def falling(n,r):  # n(n-1)...(n-r+1)
    p=1
    for j in range(r): p*=(n-j)
    return p
print("(M3) Is E_r^char0 = (2r-1)!! * n^r * prod_{j=1}^{r-1}(1-j/n)? i.e. = (2r-1)!! * n * (n-1)...(n-r+1) * n^{?}")
print("   Test E_r^char0 vs (2r-1)!! * n^{r-?} * falling(n,r) forms:")
for n in (16,32,64):
    print(f" n={n}:")
    for r in range(2,8):
        e0=E0(r,n); wick=dfac(r)*n**r
        # candidate A: (2r-1)!! * falling(n,r) * n^? -- match leading
        cand_ff = dfac(r)*falling(n,r)  # (2r-1)!!*(n)_r
        print(f"   r={r}: E_0={e0}  Wick={wick}  E_0/Wick={e0/wick:.5f}  (2r-1)!!*(n)_r/Wick={cand_ff/wick:.5f}  ratio={e0/cand_ff:.5f}")
