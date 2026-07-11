# Independent recompute of rho(r)=S_r/((p-1)E_r(C)) for mu_{2^k}, beta=4  (#444)
# rho exact (Fraction); E_r(F_p) mod-p conv; E_r(C) cyclotomic antipodal reduction.

## n=8  p=4073  (beta_eff~3.67)  generator g=3
   base: E1(F_p)=8 (==n? True) E1(C)=8 (==n? True) S1=32520 (==pn-n^2? True)
   rho(1)=0.998281  Parseval (p-n)/(p-1)=0.998281  EXACT MATCH=True
   brute-check E_3(F_p): conv=5120 brute=5120 MATCH=True
   r=1: S_r=32520  E_r(C)=8  E_r(C)/Wick=1.0000  rho=0.998281  (<=1: True)  [0.0s]
   r=2: S_r=680168  E_r(C)=168  E_r(C)/Wick=0.8750  rho=0.994258  (<=1: True)  [0.0s]
   r=3: S_r=20591616  E_r(C)=5120  E_r(C)/Wick=0.6667  rho=0.987672  (<=1: True)  [0.0s]
   r=4: S_r=757581544  E_r(C)=190120  E_r(C)/Wick=0.4421  rho=0.978574  (<=1: True)  [0.0s]
   r=5: S_r=31261837760  E_r(C)=7939008  E_r(C)/Wick=0.2564  rho=0.967031  (<=1: True)  [0.0s]
   r=6: S_r=1388248276736  E_r(C)=357713664  E_r(C)/Wick=0.1313  rho=0.953068  (<=1: True)  [0.0s]
   r=7: S_r=64817727542608  E_r(C)=16993726464  E_r(C)/Wick=0.0600  rho=0.936693  (<=1: True)  [0.0s]
   r=8: S_r=3137372223692264  E_r(C)=839358285480  E_r(C)/Wick=0.0247  rho=0.917933  (<=1: True)  [0.0s]
   r=9: S_r=155993286681686208  E_r(C)=42714450658880  E_r(C)/Wick=0.0092  rho=0.896857  (<=1: True)  [0.0s]
   r=10: S_r=7917614056945342528  E_r(C)=2225741588095168  E_r(C)/Wick=0.0032  rho=0.873598  (<=1: True)  [0.0s]
   r=11: S_r=408413726827749773024  (E_r(C) beyond cap; rho skipped)  [0.0s]
   r=12: S_r=21340912469919622534912  (E_r(C) beyond cap; rho skipped)  [0.0s]
   >> rho strictly-decreasing(exact)=True   antitone(<=)=True  all<=1=True  rho range=[0.8736,0.9983]

## n=16  p=65537  (beta_eff~4.00)  generator g=3
   base: E1(F_p)=16 (==n? True) E1(C)=16 (==n? True) S1=1048336 (==pn-n^2? True)
   rho(1)=0.999771  Parseval (p-n)/(p-1)=0.999771  EXACT MATCH=True
   brute-check E_2(F_p): conv=720 brute=720 MATCH=True
   r=1: S_r=1048336  E_r(C)=16  E_r(C)/Wick=1.0000  rho=0.999771  (<=1: True)  [0.0s]
   r=2: S_r=47121104  E_r(C)=720  E_r(C)/Wick=0.9375  rho=0.998626  (<=1: True)  [0.0s]
   r=3: S_r=3296773504  E_r(C)=50560  E_r(C)/Wick=0.8229  rho=0.994952  (<=1: True)  [0.0s]
   r=4: S_r=300724716624  E_r(C)=4649680  E_r(C)/Wick=0.6757  rho=0.986884  (<=1: True)  [0.0s]
   r=5: S_r=32780203335056  E_r(C)=514031616  E_r(C)/Wick=0.5188  rho=0.973065  (<=1: True)  [0.0s]
   r=6: S_r=4056432601097984  E_r(C)=64941883776  E_r(C)/Wick=0.3724  rho=0.953102  (<=1: True)  [0.2s]
   r=7: S_r=551428599459919120  E_r(C)=9071319628800  E_r(C)/Wick=0.2501  rho=0.927553  (<=1: True)  [0.5s]
   r=8: S_r=80539878778988799824  E_r(C)=1369263687414480  E_r(C)/Wick=0.1573  rho=0.897520  (<=1: True)  [1.4s]
   r=9: S_r=12442475496551716699264  E_r(C)=219705672931613440  E_r(C)/Wick=0.0928  rho=0.864143  (<=1: True)  [3.8s]
   r=10: S_r=2009757242996325152134864  E_r(C)=37024402443528248320  E_r(C)/Wick=0.0514  rho=0.828277  (<=1: True)  [9.6s]
   r=11: S_r=336380368483866901588346384  (E_r(C) beyond cap; rho skipped)  [1.2s]
   >> rho strictly-decreasing(exact)=True   antitone(<=)=True  all<=1=True  rho range=[0.8283,0.9998]

## n=32  p=1048609  (beta_eff~4.00)  generator g=29
   base: E1(F_p)=32 (==n? True) E1(C)=32 (==n? True) S1=33554464 (==pn-n^2? True)
   rho(1)=0.999970  Parseval (p-n)/(p-1)=0.999970  EXACT MATCH=True
   brute-check E_2(F_p): conv=2976 brute=2976 MATCH=True
   r=1: S_r=33554464  E_r(C)=32  E_r(C)/Wick=1.0000  rho=0.999970  (<=1: True)  [0.0s]
   r=2: S_r=3119611808  E_r(C)=2976  E_r(C)/Wick=0.9688  rho=0.999665  (<=1: True)  [0.0s]
   r=3: S_r=467360870656  E_r(C)=446720  E_r(C)/Wick=0.9089  rho=0.997709  (<=1: True)  [0.0s]
   r=4: S_r=94884116244384  E_r(C)=90889120  E_r(C)/Wick=0.8255  rho=0.995562  (<=1: True)  [0.2s]
   r=5: S_r=23989959256676864  E_r(C)=23012946432  E_r(C)/Wick=0.7258  rho=0.994132  (<=1: True)  [1.6s]
   r=6: S_r=7171547374526455040  (E_r(C) beyond cap; rho skipped)  [5.4s]
   >> rho strictly-decreasing(exact)=True   antitone(<=)=True  all<=1=True  rho range=[0.9941,1.0000]

=== VERDICT: base-case+brute+monotone+<=1 all exact-confirmed = True ===
Corroborates _OpenCoreRhoMonotone.lean in the COMPUTED regime only; the open core is
rho(r+1)<=rho(r) for ALL r<=log p (the char-p excess = BGK/Paley wall), still open.
