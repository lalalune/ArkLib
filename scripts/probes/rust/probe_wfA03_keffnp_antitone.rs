// wf-A03 DECISIVE: reconcile B3 (step-ratio antitone FALSE char-p) with S1's actual need
// (K_eff^NP(r) GEOMETRIC-MEAN antitone, NONPRINCIPAL energy, anchored at r=1).
//
// TWO DIFFERENT objects on the SAME nonprincipal energy E^NP_r = (1/p) sum_{b!=0} eta_b^{2r}:
//   (1) STEP-RATIO  S(r) = E^NP_{r+1} / ((2r+1)*n*E^NP_r)        <- B3 refutes ANTITONE of this
//   (2) GEOM-MEAN   K(r) = ( E^NP_r / ((2r-1)!! * n^r) )^{1/r}   <- S1 NEEDS antitone of THIS
// S1's brick charzero_limit_of_anchor_antitone needs: E^NP_r <= E^NP_1 * (2r-1)!! * n^{r-1},
//   i.e. K(r) <= K(1) = E^NP_1/n = 1 - n/p  (Parseval anchor).  K(r) antitone => this.
//
// CRUX: B3 measured step-ratio S on the FULL (DC-included) moment; S1 needs K on NONPRINCIPAL.
// We measure BOTH on the SAME nonprincipal energy, at the EXACT B3 prime p=1001153 and beta=4
// structured primes, to DEEP r ~ 1.6 ln q, and report:
//   - is S(r) antitone? (expect NO, reproducing B3)
//   - is K(r) antitone & K(r)<=K(1)? (the S1 question -- DECISIVE)
//   - log-convexity diagnostic of E^NP_r: a_r := log E^NP_r; is (a_r) convex? K antitone <=>
//     the sequence b_r := a_r - log((2r-1)!! n^r) satisfies b_r/r decreasing.
use std::f64::consts::PI; use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
fn find_prime(n:u64,lo:u64,tv:Option<u32>)->Option<u64>{let mut p=lo-(lo%n)+1;if p<lo{p+=n}let mut t=0u64;while t<200_000_000{if p>2&&isp(p){match tv{Some(v)=>if v2(p-1)==v{return Some(p)},None=>return Some(p)}}p+=n;t+=1}None}
// returns nonprincipal energy ladder E^NP_r for r=1..rmax (DC b=0 excluded; b ranges nonzero cosets)
fn eval(n:u64,p:u64,rmax:usize,nth:usize)->Vec<f64>{
    let g=proot(p);let h=mpow(g,(p-1)/n,p);let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();let mu=Arc::new(mu);
    let m=(p-1)/n;let gn=mpow(g,n,p);let chunk=(m+nth as u64-1)/nth as u64;let mut hs=vec![];
    for t in 0..nth as u64{let lo=t*chunk;let hi=((t+1)*chunk).min(m);if lo>=hi{continue}let mu=Arc::clone(&mu);
        hs.push(thread::spawn(move||{let mut s=vec![0.0f64;rmax+1];let mut b=mpow(gn,lo,p);let pp=p as u128;let inv=2.0*PI/p as f64;let nf=n as f64;
            for _ in lo..hi{let mut re=0.0;for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64;re+=(inv*(tt as f64)).cos();}
                // each coset rep b stands for n actual residues (the coset b*mu_n); weight nf
                let e2=re*re;let mut pw=1.0;for r in 1..=rmax{pw*=e2;s[r]+=nf*pw;}b=((b as u128*gn as u128)%pp)as u64;}
            s}));}
    let mut ts=vec![0.0f64;rmax+1];for h in hs{let s=h.join().unwrap();for r in 1..=rmax{ts[r]+=s[r]}}
    for r in 1..=rmax{ts[r]/=p as f64} ts // NONPRINCIPAL: b=0 (DC, eta_0=n) never included
}
fn report(label:&str,n:u64,p:u64,rmax:usize,nth:usize){
    let enp=eval(n,p,rmax,nth);let ln_n=(n as f64).ln();let lp=(p as f64).ln();
    let rdeep=((1.6*lp).round() as usize).min(rmax);
    println!("[{}] n={} p={} v2={} beta={:.3} lnq={:.1} rdeep~1.6lnq={}",label,n,p,v2(p-1),lp/ln_n,lp,rdeep);
    // K(r) geometric-mean constant
    let mut k=vec![0.0f64;rmax+1];
    for r in 1..=rmax{ if enp[r]>0.0{let lc0=ldfact(r)+r as f64*ln_n; k[r]=((enp[r].ln()-lc0)/r as f64).exp();}}
    // S(r) step-ratio  E_{r+1}/((2r+1) n E_r)
    let mut s=vec![0.0f64;rmax+1];
    for r in 1..rmax{ if enp[r]>0.0{ s[r]= enp[r+1]/(((2*r+1)as f64)*(n as f64)*enp[r]); }}
    // K antitone & K<=K(1)
    let mut k_anti=true; let mut k_anti_break=0; let mut k_cap=true; let mut k_cap_break=0;
    let k1=k[1];
    for r in 1..rdeep{ if k[r+1]>k[r]+1e-12 {if k_anti{k_anti_break=r;} k_anti=false;}}
    for r in 1..=rdeep{ if k[r]>k1+1e-12 {if k_cap{k_cap_break=r;} k_cap=false;}}
    // S antitone (the B3 object)
    let mut s_anti=true; let mut s_anti_break=0;
    for r in 1..rdeep-1{ if s[r+1]>s[r]+1e-12 {if s_anti{s_anti_break=r;} s_anti=false;}}
    print!("   K^NP(r):");
    for r in 1..=rmax{ if r<=8||r==rdeep||r%5==0||r==rmax {print!(" K{}={:.4}",r,k[r]);}} println!();
    print!("   S^NP(r):");
    for r in 1..=rmax-1{ if r<=8||r==rdeep||r%5==0||r==rmax-1 {print!(" S{}={:.4}",r,s[r]);}} println!();
    println!("   => K(1)=1-n/p={:.6} | K-ANTITONE(to rdeep)={} {} | K<=K(1) CAP={} {} | S-ANTITONE(B3 obj)={} {}",
        k1, k_anti, if k_anti{"".into()}else{format!("(1st break r={})",k_anti_break)},
        k_cap, if k_cap{"".into()}else{format!("(1st break r={})",k_cap_break)},
        s_anti, if s_anti{"".into()}else{format!("(1st break r={})",s_anti_break)});
    // worst K over r vs K(1) (the S1-relevant sup)
    let mut supk=0.0f64; let mut supr=0; for r in 1..=rdeep{if k[r]>supk{supk=k[r];supr=r;}}
    println!("   => sup_r K^NP(r) (r<=rdeep) = {:.4} @r={}  (S1 needs sup<=K(1)={:.4}; gap={:+.2e})",
        supk,supr,k1,supk-k1);
    println!();
}
fn main(){
    let a:Vec<String>=std::env::args().collect();let nth:usize=if a.len()>1{a[1].parse().unwrap()}else{8};
    println!("=== wf-A03: K_eff^NP geom-mean antitone (S1 need) vs step-ratio antitone (B3 refutes) -- SAME nonprincipal energy ===");
    println!("-- THE B3 PRIME (where step-ratio antitone provably FAILS at prize scale) --");
    report("B3-PRIME",32,1001153,40,nth);
    report("B3-sub1",32,4129,28,nth);
    report("B3-sub2",128,15233,28,nth);
    println!("-- beta~4 structured (v2=mu tightest) + generic, prize-scale extrapolation --");
    for (n,rmax) in vec![(16usize,42),(32,42),(64,40),(128,38),(256,36)] {
        let n=n as u64; let mu=(n as f64).log2() as u32; let lo=((n as f64).powf(4.0)) as u64;
        if let Some(p)=find_prime(n,lo,Some(mu)){report("STRUCT-b4",n,p,rmax,nth);}
        if let Some(p)=find_prime(n,lo,None){report("GENERIC-b4",n,p,rmax,nth);}
    }
    // Fermat classic
    report("FERMAT16",16,65537,42,nth);
}
