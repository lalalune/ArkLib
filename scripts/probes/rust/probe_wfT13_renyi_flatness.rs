// Probe wfT13 (#444): the Renyi-alpha FLATNESS FACTOR of the dilation pushforward of mu_n,
// for alpha in (1, infinity], read through the spectrum. Tests T13's claim that the flatness
// at a SUPER-CRITICAL order alpha* = 2 + c/log m carries strictly more than 2nd-order info and
// is a genuinely different (milder) object than the deep-moment ladder.
//
// SETUP. f = (1/n) 1_{mu_n} on F_p, f_hat(b) = eta_b / n, eta_b = sum_{x in mu_n} e_p(b x).
// mu_n is negation-closed (n=2^mu even) => eta_b real.
//
// FLATNESS FACTOR read through the spectrum. The natural "Renyi-alpha flatness factor" of the
// pushforward measure (Ling-Luzzi-Yan 2025/986 style, transcribed to F_p Fourier) is the
// Renyi-alpha divergence of the spectral mass distribution from the uniform/principal one. The
// candidate pins the ENDPOINTS exactly: eps_2 = energy (alpha=2), eps_infinity = M/n (sup).
// Reading "eps_alpha through the spectrum" the order-alpha flatness is governed by the
// L^{2 alpha} norm of the spectrum (the Renyi-alpha collision moment of the convolution measure),
// i.e. by  S(t) := (1/p) sum_{b != 0} |eta_b|^{2 t}  at  t = alpha - 1  (so t=1 <-> alpha=2 is the
// energy E_1-type 2nd moment, t->inf <-> alpha=inf is the sup). We measure:
//   - the per-order normalized flatness  eps_alpha := ( S(alpha-1) )^{1/(2(alpha-1))} / n   (spectral L^p flatness)
//   - eps_infinity = M/n exactly
//   - the candidate interpolation eps_infinity <= eps_alpha^theta  and the best theta(alpha)
//   - the deep-moment M-bound at integer r:  Mbound_r = (q E_r)^{1/2r},  E_r = sum_b |eta_b|^{2r}
//   - whether eps_{alpha*} at alpha* = 2 + c/log m sits at the Gaussian floor (n/p)^{1/2} sqrt(alpha*)
//
// PRIZE REGIME: beta = 4, p ~ n^4, p = 1 mod n, thin mu_n. NEVER n = q-1.

use std::f64::consts::PI;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}let _=a; r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

// Returns (n, p, m=(p-1)/n, M, vec of |eta_b| over coset reps b != 0)
fn spectrum(n:u64,p:u64)->(u64,u64,u64,f64,Vec<f64>){
    let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let mut etas=Vec::with_capacity(m as usize);
    let mut b=1u64; let gn=mpow(g,n,p);
    let mut best=0.0f64;
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu {
            let t=((b as u128 * x as u128)%p as u128) as u64;
            let ang=2.0*PI*(t as f64)/(p as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        let mag=(re*re+im*im).sqrt();
        if mag>best{best=mag;}
        etas.push(mag);
        b=(b as u128 * gn as u128 % p as u128) as u64;
    }
    // b ranges over coset reps of mu_n; b=1 is the trivial coset rep but NOT b=0.
    // The principal frequency b=0 (eta_0 = n) is excluded (we want max over b != 0).
    // Each coset has n elements with the same |eta|; total nonzero freqs = n*m = p-1.
    (n,p,m,best,etas)
}

fn main(){
    println!("# wfT13: Renyi-alpha flatness factor of mu_n pushforward, alpha in (2, inf]");
    println!("# columns: n p beta M M/sqrt(n) | alpha* eps_alpha* GaussFloor ratio | r* Mbound_r* Mbound/M | theta_needed");
    let ns=[16u64,32,64,128,256];
    let beta=4.0f64;
    for &n in &ns {
        let lo=(n as f64).powf(beta).round() as u64;
        let p=find_prime_cong1(n, lo.max(n+2));
        let (_,_,m,big_m,etas)=spectrum(n,p);
        let nf=n as f64; let pf=p as f64; let mf=m as f64;
        let beta_eff=pf.ln()/nf.ln();
        // E_r = sum over ALL nonzero freqs |eta|^{2r}; we have one rep per coset (n freqs each, same |eta|)
        // so E_r = n * sum_{coset reps} |eta|^{2r}. (Excludes b=0.)
        let energy=|r:f64|->f64{ nf * etas.iter().map(|&e| e.powf(2.0*r)).sum::<f64>() };
        // spectral Renyi-alpha flatness eps_alpha = ( (1/p) E_{alpha-1} )^{1/(2(alpha-1))} / n
        let eps=|alpha:f64|->f64{
            let t=alpha-1.0;
            ((energy(t)/pf).powf(1.0/(2.0*t)))/nf
        };
        let eps_inf=big_m/nf;
        // super-critical order: alpha* = 2 + c/log m  (c=1)
        let c=1.0f64;
        let astar=2.0 + c/mf.ln();
        let eps_astar=eps(astar);
        // Gaussian floor the candidate hypothesizes: eps_{alpha*} <= (n/p)^{1/2} sqrt(alpha*)
        let gauss_floor=(nf/pf).sqrt()*astar.sqrt();
        // deep-moment best integer r-bound on M: min_r (q E_r)^{1/2r}
        let mut best_mb=f64::INFINITY; let mut best_r=1u64;
        for r in 1..=24u64 {
            let mb=(pf*energy(r as f64)).powf(1.0/(2.0*(r as f64)));
            if mb<best_mb{best_mb=mb; best_r=r;}
        }
        // theta needed so that eps_inf = eps_astar^theta  => theta = ln(eps_inf)/ln(eps_astar)
        let theta=eps_inf.ln()/eps_astar.ln();
        println!("{:4} {:>12} b={:.3} | M={:8.3} M/sqrtn={:6.4} | a*={:.4} eps_a*={:.5e} gfloor={:.5e} ratio={:7.3} | r*={} Mb={:8.3} Mb/M={:6.4} | theta={:6.4}",
            n,p,beta_eff,big_m,big_m/nf.sqrt(),astar,eps_astar,gauss_floor,eps_astar/gauss_floor,best_r,best_mb,best_mb/big_m,theta);
    }
    println!();
    println!("# KEY DIAGNOSTIC: is eps_{{alpha*}} at alpha*=2+c/log m at the Gaussian floor? (ratio ~ 1 would close)");
    println!("# and: does the spectral L^{{2(alpha*-1)}} flatness eps_{{alpha*}} = the deep-moment E_{{alpha*-1}} ladder verbatim?");
    println!("# (if eps_astar tracks the energy at order ~alpha*-1, T13's 'new functional' IS the moment ladder = F1/F7)");

    // Direct check: eps_alpha for alpha = 2 (exact energy) vs alpha slightly above 2.
    println!();
    println!("# eps_alpha sweep at n=64 (shows monotone interpolation 2->inf, and the alpha=2 energy endpoint):");
    let n=64u64; let p=find_prime_cong1(n,(n as f64).powf(4.0).round() as u64);
    let (_,_,m,big_m,etas)=spectrum(n,p);
    let nf=n as f64; let pf=p as f64; let mf=m as f64;
    let energy=|r:f64|->f64{ nf * etas.iter().map(|&e| e.powf(2.0*r)).sum::<f64>() };
    let eps=|alpha:f64|->f64{ let t=alpha-1.0; ((energy(t)/pf).powf(1.0/(2.0*t)))/nf };
    let eps_inf=big_m/nf;
    for &a in &[2.0001f64, 2.0+1.0/mf.ln(), 2.5, 3.0, 4.0, 6.0, 10.0, 30.0] {
        println!("  alpha={:8.4}  eps_alpha={:.6e}  eps_alpha/eps_inf={:8.4}", a, eps(a), eps(a)/eps_inf);
    }
    println!("  alpha=inf    eps_inf  ={:.6e}  (= M/n, M={:.3})", eps_inf, big_m);
}
