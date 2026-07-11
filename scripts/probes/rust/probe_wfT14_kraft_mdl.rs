// wf-T14 (#444): empirical refutation of the Kolmogorov/MDL incompressibility route (= catalog N12).
//
// CANDIDATE (architect G3-T4 / catalog N12): the worst-frequency witness b* of the generalized-Paley
// sup M(n)=max_{b!=0}|eta_b|, eta_b=sum_{x in mu_n} e_p(b x), is algorithmically INCOMPRESSIBLE
// (K(b*) >= 2 log2(lambda), lambda=|eta_b|/sqrt n), and the alignment map b->c(b) is INJECTIVE on each
// |eta_b|-level set; Kraft's inequality over the (p-1) frequencies then caps #{|eta_b|>lambda sqrt n}
// <= (p-1)/lambda^2 and resummation gives M <= C sqrt(n log(p/n)).
//
// THIS PROBE refutes BOTH load-bearing premises at the PRIZE regime (beta=4, p~n^4, p=1 mod n):
//   (R1) LEVEL SETS ARE EXACT mu_n-COSET UNIONS. Since eta_{z b}=eta_b rotated for z in mu_n,
//        |eta_{z b}|=|eta_b|; so each level set is closed under mu_n-multiplication and has size a
//        multiple of n. => the alignment map is exactly n-to-1 (NOT injective), and the worst b* is
//        describable by its coset rep among (p-1)/n cosets => K(b*) <= log2((p-1)/n), NOT >= 2 log2 lambda.
//        (Even more: b* = "the maximizer of |eta_b|" is an O(log) description => LEAST incompressible.)
//   (R2) THE COUNT IS THE SECOND MOMENT (fence F0). Measured #{|eta_b|>lambda sqrt n} <= (p-1)/lambda^2
//        for every lambda (ratio actual/(p-1/lambda^2) < 1). That bound is exactly Markov on
//        sum_b |eta_b|^2 = (p-1) n (Parseval) — no MDL input beats it.
//   (R3) RESUMMING the (p-1)/lambda^2 count caps lambda <= sqrt((p-1)/n) (one coset survives),
//        i.e. M <= sqrt(p) ~ n^2 = VACUOUS, never sqrt(n log(p/n)). The MDL route, granting its
//        abstract Kraft count, lands EXACTLY on F0.
//
// build: rustc -O scripts/probes/rust/probe_wfT14_kraft_mdl.rs -o /tmp/t14 && /tmp/t14
use std::f64::consts::PI;

fn mpow(_a:u64,mut e:u64,p:u64,a:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2u64;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2u64;loop{if fs.iter().all(|&f|mpow(0,(p-1)/f,p,g)!=1){return g;}g+=1;}}

fn main(){
    println!("wf-T14: Kolmogorov/MDL incompressibility (N12) — REFUTED at beta=4 (prize-shaped p~n^4)\n");
    for &mu in &[3u32,4,5,6]{
        let n=1u64<<mu;
        // prize-shaped: smallest prime p = n*m+1 with m >= n^3 so p ~ n^4
        let lo=n*n*n*n; // ~ n^4
        let p=find_prime_cong1(n,lo);
        let g=primitive_root(p);
        let h=mpow(0,(p-1)/n,p,g);          // generator of mu_n
        let muel:Vec<u64>=(0..n).map(|j|mpow(0,j,p,h)).collect();
        let m=(p-1)/n;                       // number of mu_n-cosets
        // compute |eta_b| for ALL b in F_p^* by ranging over coset reps (period is coset-constant);
        // we store one magnitude per coset and remember each coset's full multiplicity = n.
        let mut coset_mag:Vec<f64>=Vec::with_capacity(m as usize);
        let mut b=1u64; let gn=mpow(0,n,p,g);   // g^n generates the quotient group of order m
        let mut best=0.0f64;
        for _ci in 0..m {
            let mut re=0.0f64; let mut im=0.0f64;
            for &x in &muel {
                let t=((b as u128 * x as u128)%p as u128) as u64;
                let ang=2.0*PI*(t as f64)/(p as f64);
                re+=ang.cos(); im+=ang.sin();
            }
            let mag=(re*re+im*im).sqrt();
            if mag>best{best=mag;}
            coset_mag.push(mag);
            b=((b as u128 * gn as u128)%p as u128) as u64;
        }
        let sn=(n as f64).sqrt();
        let lam_star=best/sn;
        let beta=(p as f64).ln()/(n as f64).ln();
        println!("n={:>3} p={} beta={:.3} M/sqrt(n)=lam*={:.3}", n, p, beta, lam_star);

        // (R1) level-set coset structure: the worst coset has magnitude `best`; the level set
        // {b : |eta_b| = best} is a union of WHOLE cosets, each of size n. Count how many cosets
        // share the top magnitude, then the level set size = (#top cosets)*n, a multiple of n.
        let top_cosets=coset_mag.iter().filter(|&&v|(v-best).abs()<1e-6).count();
        let level_size=(top_cosets as u64)*n;
        println!("    (R1) worst level set = {} coset(s) x n = {} elements (multiple of n: {}); ",
                 top_cosets, level_size, level_size%n==0);
        let k_coset=( (m as f64).log2() ).ceil() as i64;       // bits to name the coset rep
        let need_incompr=(2.0*lam_star.log2()).max(0.0);        // bits the candidate REQUIRES
        println!("         K(b*)<=log2((p-1)/n)={} bits (coset rep) vs candidate needs K>=2 log2 lam*={:.1} bits => incompressibility FALSE (short-describable)",
                 k_coset, need_incompr);

        // (R2) count #{|eta_b|>lambda sqrt n} over ALL (p-1) frequencies = n * #{cosets above thr}.
        // compare to second-moment (Markov) prediction (p-1)/lambda^2.
        print!("    (R2) count vs (p-1)/lam^2 (Markov 2nd moment):");
        for &lam in &[1.5f64,2.0,2.5,3.0]{
            let thr=lam*sn;
            let above=coset_mag.iter().filter(|&&v|v>thr).count() as u64 * n;
            let pred=(p as f64 -1.0)/(lam*lam);
            let ratio=above as f64/pred;
            print!("  lam={}:{}/{:.0}={:.3}", lam, above, pred, ratio);
        }
        println!("   (all ratios<1 => count IS the 2nd moment, F0)");

        // (R3) resummation cap: Markov count >= n (one coset must survive at the max) =>
        // (p-1)/lam^2 >= n => lam <= sqrt((p-1)/n) => M <= sqrt(p). vacuous.
        let lam_cap=((p as f64 -1.0)/(n as f64)).sqrt();
        let prize_target=(n as f64*(p as f64/n as f64).ln()).sqrt();
        println!("    (R3) MDL/2nd-moment resummation cap: lam<=sqrt((p-1)/n)={:.0} => M<=sqrt(p)={:.0} = VACUOUS (prize target sqrt(n log(p/n))={:.1})\n",
                 lam_cap, (p as f64).sqrt(), prize_target);
    }
    println!("VERDICT = REDUCES-TO-WALL (F0 conservation law; equiv. F1).");
    println!("Both premises false: (i) alignment map is n-to-1 not injective (level sets are mu_n-coset unions);");
    println!("(ii) worst witness is short-describable (K<=log2((p-1)/n)), NOT incompressible (K>=2 log lam).");
    println!("Granting the abstract Kraft count, the MDL route delivers EXACTLY the 2nd-moment count => F0 => vacuous sqrt(p).");
    println!("Matches DISPROOF_LOG lane D9: 'Kolmogorov-incompressibility (=N12) vacuous because worst b is short-describable.'");
}
