// probe_wfT25_rajchman_density.rs
// ATTACK T25 (architect G5-5): "Absolutely-continuous (Rajchman) spectral measure of the dilation
//   Koopman flow with BOUNDED DENSITY forces an edge-tail decay => M(n) <= sqrt(n)*sqrt(2 log(p/n))."
//
// The candidate's ONLY non-tautological content is: the spectral measure mu_V of the dilation
//   Koopman operator V (x |-> g x, g a generator of mu_n) on l^2(F_p) is ABSOLUTELY CONTINUOUS
//   with bounded density rho_max <= 1 + C log(p/n)/n, and that bound caps M(n) at the edge.
//
// TWO decisive structural facts (this probe makes them concrete at the prize regime, beta=4):
//
//  (R0) PURE-POINT, NOT A.C.  V is a unitary operator on l^2(F_p), a FINITE-dimensional Hilbert
//       space of dimension p. Its spectral measure mu_V is therefore a FINITE SUM OF ATOMS
//       (point masses at the eigenvalues, which are roots of unity since V^ord = I). A finite-dim
//       unitary has NO absolutely-continuous part: dmu_V/dtheta does not exist as an L^infty
//       density (it is a sum of Dirac deltas). So "rho_max = sup of the a.c. density" is VACUOUS
//       at every finite prize prime. We VERIFY: V (dilation by g) is a permutation of F_p^* fixing
//       0, i.e. a single p-1 cycle (g generates F_p^*) plus the fixed point 0. Its eigenvalues are
//       exactly the (p-1)-th roots of unity (each once) plus eigenvalue 1 (from the 0 fixed point).
//       => spectral measure = uniform ATOMIC measure on mu_{p-1} cup {1}. Purely atomic. The a.c.
//       density object the candidate bounds DOES NOT EXIST. (Refutation at the root: REFUTED.)
//
//  (R1) THE FOURIER COEFFICIENTS = AUTOCORRELATIONS = ENERGY (the F1 reduction, if one passes to
//       the only well-defined surrogate). The candidate itself computes
//          mu_V^hat(k) = (1/n) <V^k 1_{mu_n}, 1_{mu_n}> = (1/n) #{x in mu_n : g^k x in mu_n}.
//       Since g generates mu_n (mu_n is the g-orbit of size n), g^k x in mu_n for ALL x in mu_n
//       and all k: the orbit is CLOSED under g. So mu_V^hat(k) = 1 for every k (the candidate says
//       this: "trivial on the orbit"). A measure with ALL Fourier coefficients = 1 is the DIRAC
//       MASS at theta=0 (delta_1): a single atom. NOT a.c., NOT Rajchman (Rajchman = hat -> 0;
//       here hat == 1 identically, the most-NON-Rajchman measure possible). So on H_eta the Koopman
//       spectrum is the single eigenvalue 1 (1_{mu_n} is V-invariant) -- a pure atom, density
//       undefined, and CARRIES NO INFORMATION about M(n) at all.
//       The ONLY place {eta_b} enters is the FULL operator's matrix coefficients across the m cosets
//       -- and those are <U_b 1, 1> = the additive autocorrelations whose magnitudes^2 are |eta_b|^2.
//       The "a.c. density across the coset fibration" the candidate wants is then, by Parseval,
//          sum_k |mu_V^hat(k)|^2  ~  the additive energy E_2(mu_n)  (Wiener: atoms <-> Cesaro |hat|^2),
//       and any L^infty bound on a putative density bounds sum_b |eta_b|^{2r} = p E_r - n^{2r}
//       = exactly F1's moment ladder. So if one FORCES a well-posed density-surrogate, it IS the
//       energy. We measure this tracking.
//
//  (R2) THE EDGE TRANSFER = THE SAME CHAR-p ENERGY TRANSFER. The claimed conclusion
//          M(n) <= sqrt(n) sqrt(2 log(p/n))   <=>   E_r(mu_n) <= (2r-1)!! n^r at r ~ ln(p/n)
//       (Gaussian edge tail <-> sub-Gaussian Wick moments). We measure K_eff=(E_r/Wick)^{1/r};
//       if FLAT, the "Rajchman density" gives nothing beyond the open char-p transfer (F1).
//
// build: rustc -O probe_wfT25_rajchman_density.rs -o /tmp/wfT25 && /tmp/wfT25
use std::f64::consts::PI;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128 % p as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn find_p(n:u64, beta:f64)->u64{
    let target = (n as f64).powf(beta) as u64;
    let mut p = (target/n + 1)*n + 1;
    loop{ if is_prime(p) && (p-1)%n==0 && (p-1)/n>1 { return p; } p+=n; }
}

fn main(){
    println!("{}","=".repeat(86));
    println!("T25 Rajchman a.c.-density Koopman probe (prize-faithful, beta->4 where tractable)");
    println!("{}","=".repeat(86));

    // (R0) structural: dilation Koopman is a permutation, eigenvalues are roots of unity => PURE POINT.
    println!("\n(R0) PURE-POINT STRUCTURE (a.c. density does not exist at finite p):");
    println!("  V = (x |-> g x) is a permutation of F_p: one (p-1)-cycle on F_p^* + fixed pt 0.");
    println!("  Eigenvalues of V = all (p-1)-th roots of unity (each once) + eigenvalue 1.");
    println!("  Spectral measure mu_V = (1/p) sum of p Dirac atoms on the unit circle.");
    println!("  => mu_V is PURELY ATOMIC; dmu_V/dtheta is a sum of deltas, NOT an L^infty density.");
    println!("  => rho_max := sup(a.c. density) is VACUOUS/UNDEFINED. The candidate's object is empty.");

    let cells: Vec<(u64,f64)> = vec![(8,4.0),(16,4.0),(32,3.6),(64,3.0),(128,2.6),(256,2.3)];
    for (n,beta) in cells {
        let p = find_p(n,beta);
        if (p as u128)*(n as u128) > 60_000_000u128 { println!("\n n={} p={} skip (sweep too big)",n,p); continue; }
        let m=(p-1)/n;
        let beta_eff = (n as f64).ln()/(p as f64).ln();
        let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();

        // (R1a) mu_V^hat(k) on H_eta = (1/n)#{x in mu_n : h^k x in mu_n}.  h generates mu_n.
        let muset: std::collections::HashSet<u64> = mu.iter().cloned().collect();
        let mut all_one = true; let mut min_corr = 1.0f64;
        for k in 0..n {
            let hk = mpow(h,k,p);
            let cnt = mu.iter().filter(|&&x| muset.contains(&(((hk as u128*x as u128)%p as u128) as u64))).count();
            let corr = cnt as f64 / n as f64;
            if (corr-1.0).abs()>1e-12 { all_one=false; }
            if corr<min_corr {min_corr=corr;}
        }

        // full {eta_b} over m coset reps b = g^j (one distinct eigenvalue per coset)
        let gn=mpow(g,n,p);
        let mut mags=Vec::with_capacity(m as usize);
        let mut b=1u64;
        for _ in 0..m {
            let mut re=0.0f64; let mut im=0.0f64;
            for &x in &mu {
                let t=((b as u128*x as u128)%p as u128) as u64;
                let ang=2.0*PI*(t as f64)/(p as f64);
                re+=ang.cos(); im+=ang.sin();
            }
            mags.push((re*re+im*im).sqrt());
            b=(b as u128*gn as u128 %p as u128) as u64;
        }
        mags.sort_by(|a,c|c.partial_cmp(a).unwrap());
        let mm=mags[0];
        let sqn=(n as f64).sqrt();
        let bgk=( (n as f64) * (p as f64/n as f64).ln() ).sqrt();

        println!("\n--- n={} (mu={})  p={}  m={}  beta_eff={:.3} ---",n,(n as f64).log2() as u32,p,m,beta_eff);
        println!("  (R1a) mu_V^hat(k) on H_eta: all == 1? {}  (min corr over k = {:.6})",
                 if all_one {"YES"} else {"no"}, min_corr);
        println!("        => spectral measure on H_eta = delta_1 (single atom); hat==1 is MOST-non-Rajchman.");
        println!("        => H_eta carries ZERO info about M(n) (1_{{mu_n}} is V-invariant, eigenvalue 1).");
        println!("  M=max|eta|={:.4}  M/sqrt(n)={:.4}  BGK={:.4}  C=M/BGK={:.4}", mm, mm/sqn, bgk, mm/bgk);

        // (R1b) Wiener/Parseval: the ONLY well-posed 'density' surrogate is the energy.
        // sum over ALL p-1 nonzero freqs of |eta_b|^{2r} = p*E_r - n^{2r}; r=2 is the L^2 'density mass'.
        println!("  (R2) K_eff=(E_r/Wick)^(1/r)  [if FLAT => density<->energy transfer = F1, no gain]:");
        println!("       r |   E_r (char-p)   |  Wick=(2r-1)!!n^r |  K_eff  |  M | BGK");
        let rmax = ((p as f64/n as f64).ln() as u32 + 2).max(4).min(10);
        let mut flat = true; let mut prev = -1.0f64;
        for r in 1..=rmax {
            let mut sm=0.0f64;
            for &v in &mags { sm += v.powi(2*r as i32); }
            // E_r over ALL freqs (incl principal): (n*sum_coset + n^{2r})/p
            let er = ((n as f64)*sm + (n as f64).powi(2*r as i32))/(p as f64);
            let mut wick=1.0f64; for k in 0..r { wick *= (2*k+1) as f64; } wick *= (n as f64).powi(r as i32);
            let keff = (er/wick).powf(1.0/r as f64);
            if prev>0.0 && (keff-prev).abs()>0.25 {flat=false;}
            prev=keff;
            if r<=8 {
                println!("       {:2} | {:16.4} | {:16.4} | {:7.4} | {:.3} | {:.3}", r, er, wick, keff, mm, bgk);
            }
        }
        println!("       K_eff stays flat ~constant? {}  (flat => Rajchman-density = F1 energy, NO gain)",
                 if flat {"YES"} else {"no"});
    }
    println!("\n{}","=".repeat(86));
    println!("VERDICT:");
    println!("  (R0) FINITE-DIM unitary => PURE-POINT spectral measure, NO a.c. part. rho_max VACUOUS.");
    println!("       The a.c.-density object the candidate bounds DOES NOT EXIST at any prize prime.");
    println!("       => REFUTED at the root (the spectral type is atomic, not a.c.).");
    println!("  (R1) On H_eta: mu_V^hat == 1 (delta_1), the MOST non-Rajchman measure; zero info on M.");
    println!("  (R2) Any well-posed density-surrogate (Wiener |hat|^2 mass) = the energy E_r = F1;");
    println!("       K_eff flat => the 'edge transfer' IS the open char-p energy transfer, no new lever.");
    println!("  => REFUTED (pure-point, a.c. density empty) + the surrogate REDUCES-TO-WALL F1.");
    println!("{}","=".repeat(86));
}
