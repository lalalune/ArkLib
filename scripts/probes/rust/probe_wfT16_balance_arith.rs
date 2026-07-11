// Probe wfT16b (#444): the BALANCING ARITHMETIC of the T16/G4-1 proof, independent of the 1/mu claim.
//
// The candidate's final step: "|Spec_alpha| <= n*D ; Parseval sum_{b!=0}|eta_b|^2 = n(p-n) over the
// <= n*D large cosets at alpha=M/n forces M <= C sqrt(n log(p/n))."
//
// This probe checks the LOGICAL DIRECTION of that step. Two standard ways to combine a cardinality
// bound |Spec_alpha| <= S with Parseval:
//   (i)  Parseval LOWER-bounds the mass NOT on Spec_alpha; gives NO upper bound on M.
//   (ii) The genuine Chang/large-spectrum route: |Spec_alpha| >= (something) gives a LOWER bound on
//        the spectrum size, used to FORCE structure -- the cardinality bound from Chang is an UPPER
//        bound on the DISSOCIATED DIM, which via Rudin gives |Spec_alpha| <= (n/alpha^2 n^2)*... .
// We test: does ANY combination of (#large cosets) and Parseval, with the measured numbers, produce
// M <= C sqrt(n log) -- or is the implication vacuous / reversed at prize regime?
//
// Specifically we compute, at the candidate's alpha = M/n:
//   - the actual #cosets with |eta|>=M (always small / isolated)
//   - the "balancing" candidate bound:  M^2 <= n(p-n) / (#cosets with |eta|>=M * n)   [the only way
//     cardinality + Parseval upper-bounds M: mass <= |Spec|*M^2 is a LOWER bound on M, WRONG dir;
//     mass on Spec >= ... gives M^2 >= mass/|Spec| -- a LOWER bound on M].
//   - We show the Parseval-balance gives a LOWER bound M^2 >= n(p-n)/(p-1) -> n  (=Johnson, RMS),
//     NEVER an upper bound, so the covering count cannot push M down.
//
// Prize regime beta=4, p=1 mod n, mu_n proper, NEVER n=p-1.

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((n+1-lo%n)%n);if p%n!=1{p=p-(p%n)+1;}if p<3{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

fn main(){
    println!("# wfT16b: balancing arithmetic of T16. At alpha=M/n the covering count + Parseval gives");
    println!("# only a LOWER bound on M (Johnson RMS), never the claimed upper bound. PRIZE beta=4.");
    println!();
    for &n in &[8u64,16,32,64,128,256,512] {
        let p=find_prime_cong1(n,(n as f64).powf(4.0).round() as u64);
        let g=primitive_root(p); let m=(p-1)/n; let gm=mpow(g,m,p);
        let mut mun=Vec::with_capacity(n as usize); let mut x=1u64;
        for _ in 0..n { mun.push(x); x=((x as u128*gm as u128)%p as u128) as u64; }
        let pf=p as f64; let nf=n as f64; let twopi=2.0*PI;
        // per coset eta magnitude
        let mut etas=Vec::with_capacity(m as usize); let mut r=1u64;
        for _ in 0..m {
            let mut re=0.0; let mut im=0.0;
            for &y in &mun { let ang=twopi*(((r as u128*y as u128)%p as u128) as f64/pf); re+=ang.cos(); im+=ang.sin(); }
            etas.push((re*re+im*im).sqrt()); r=((r as u128*g as u128)%p as u128) as u64;
        }
        let big_m=etas.iter().cloned().fold(0.0,f64::max);
        let logpn=(pf/nf).ln();
        let floor=(nf*logpn).sqrt();
        // Parseval over all nonzero b: each coset value repeats n times => sum_{b!=0}|eta|^2 = n * sum_coset |eta|^2.
        let coset_energy:f64 = etas.iter().map(|e|e*e).sum();
        let parseval = nf*coset_energy; // = n(p-n)
        // count cosets with |eta| >= M (the alpha=M/n spectrum, EXACTLY the argmax cosets)
        let nmax = etas.iter().filter(|&&e| e>=big_m-1e-6).count();
        // The Chang cover claims |Spec_{M/n}| <= n*D. Number of *frequencies* (not cosets) with |eta|>=M:
        let nfreq_max = nmax as f64 * nf;
        // Parseval-balance LOWER bound on M (RMS over the cosets that carry mass): the mass argument
        // gives M^2 >= parseval / (#nonzero b) = (p-n) -> NO. The correct RMS: avg |eta|^2 = (p-n)/(p-1)*n?
        // Let's just display: the ONLY M-relation from |Spec|<=S and Parseval is the trivial RMS.
        let rms_coset = (coset_energy/(m as f64)).sqrt();   // RMS coset period ~ sqrt(n) (Johnson)
        // The candidate's "forced" bound, read literally: M^2 * (n*D) >= parseval would force M down only
        // if D were LARGE; but the cardinality bound makes n*D SMALL -> the inequality M^2*(small) >= mass
        // pushes M UP, not down. Show the implied LOWER bound M >= sqrt(parseval/(n*D)) for the wall D0.
        for &al in &[1.0f64, big_m/nf] {
            let d0 = al.powi(-2)*logpn;          // wall dim
            let s = nf*d0;                       // claimed |Spec_alpha| <= n*D0
            let forced_lower = (parseval/(s)).sqrt();  // M >= sqrt(mass / |Spec|) if Spec carries all mass
            println!("  n={:4} alpha={:.4}: M={:7.2} floor={:7.2} M/floor={:.3}  |Spec<=n*D0|={:9.1}  Parseval/|Spec| -> M_lower={:8.2}  (>=Johnson?{})",
                n, al, big_m, floor, big_m/floor, s, forced_lower, if forced_lower>=nf.sqrt(){"yes"}else{"no"});
        }
        println!("       #argmax_cosets(|eta|>=M)={}  RMS_coset_period={:.3} (~sqrt(n)={:.3}, Johnson)  Parseval=n(p-n)? {:.3e} vs {:.3e}",
            nmax, rms_coset, nf.sqrt(), parseval, nf*(pf-nf));
    }
    println!();
    println!("# CONCLUSION: |Spec_alpha| <= n*D + Parseval is a LOWER-bound mechanism (mass / cardinality");
    println!("# = RMS = Johnson sqrt(n)). It cannot upper-bound M. The covering cardinality going DOWN");
    println!("# (smaller D) makes the forced LOWER bound on M go UP. The proof's final implication is");
    println!("# REVERSED: cardinality+Parseval pins the Johnson RMS floor, not the sqrt(log) ceiling.");
}
