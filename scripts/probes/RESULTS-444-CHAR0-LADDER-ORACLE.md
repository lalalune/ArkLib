# Independent semantic cross-validation of the char-0 energy ladder (#444)
# E_r(n) closed forms vs. the TRUE roots-of-unity additive energy.
# n=2 oracle: C(2r,r) (Vandermonde). n=4 oracle: cyclotomic antipodal convolution.

Found 16 published ladder rungs: r in [7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23]
NOTE: ladder gaps (no _AvL2_E{r}ClosedForm.lean) at r = [15]

  r= 7 n=2: claimed=3432  oracle=3432  OK 
  r= 7 n=4: claimed=11778624  oracle=11778624  OK 

  r= 8 n=2: claimed=12870  oracle=12870  OK 
  r= 8 n=4: claimed=165636900  oracle=165636900  OK 

  r= 9 n=2: claimed=48620  oracle=48620  OK 
  r= 9 n=4: claimed=2363904400  oracle=2363904400  OK 

  r=10 n=2: claimed=184756  oracle=184756  OK 
  r=10 n=4: claimed=34134779536  oracle=34134779536  OK 

  r=11 n=2: claimed=705432  oracle=705432  OK 
  r=11 n=4: claimed=497634306624  oracle=497634306624  OK 

  r=12 n=2: claimed=2704156  oracle=2704156  OK 
  r=12 n=4: claimed=7312459672336  oracle=7312459672336  OK 

  r=13 n=2: claimed=10400600  oracle=10400600  OK 
  r=13 n=4: claimed=108172480360000  oracle=108172480360000  OK 

  r=14 n=2: claimed=40116600  oracle=40116600  OK 
  r=14 n=4: claimed=1609341595560000  oracle=1609341595560000  OK 

  r=16 n=2: claimed=601080390  oracle=601080390  OK 
  r=16 n=4: claimed=361297635242552100  oracle=361297635242552100  OK 

  r=17 n=2: claimed=2333606220  oracle=2333606220  OK 
  r=17 n=4: claimed=5445717990022688400  oracle=5445717990022688400  OK 

  r=18 n=2: claimed=9075135300  oracle=9075135300  OK 
  r=18 n=4: claimed=82358080713306090000  oracle=82358080713306090000  OK 

  r=19 n=2: claimed=35345263800  oracle=35345263800  OK 
  r=19 n=4: claimed=1249287673091590440000  oracle=1249287673091590440000  OK 

  r=20 n=2: claimed=137846528820  oracle=137846528820  OK 
  r=20 n=4: claimed=19001665507723090592400  oracle=19001665507723090592400  OK 

  r=21 n=2: claimed=538257874440  oracle=538257874440  OK 
  r=21 n=4: claimed=289721539396666805313600  oracle=289721539396666805313600  OK 

  r=22 n=2: claimed=2104098963720  oracle=2104098963720  OK 
  r=22 n=4: claimed=4427232449127577876238400  oracle=4427232449127577876238400  OK 

  r=23 n=2: claimed=8233430727600  oracle=8233430727600  OK 
  r=23 n=4: claimed=67789381546187865401760000  oracle=67789381546187865401760000  OK 

=== VERDICT: every published char-0 ladder anchor matches the independent additive-energy oracle = True ===
This certifies the ladder polynomials ARE the roots-of-unity char-0 additive energy
(the semantic claim `decide` cannot reach), at the verified anchors n=2,4. It says
NOTHING about the open char-p transfer (the BGK/Paley wall), which remains open.
