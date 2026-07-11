// mgfexcess — #444/#407: char-p WRAPAROUND EXCESS of the cosh-MGF over the char-0 Bessel reference.
//
// Object (DCSubtractedMoment.lean / CoshMGFIdentity.lean / BGKNearRamanujan.lean):
//   eta_b = sum_{x in mu_n} psi(b x),   psi additive char of F_p.   |eta_b| constant on cosets b*mu_n.
//   #cosets among nonzero b = m = (p-1)/n, each coset size n.   eta_0 = n.
//
//   MGF identity (exact):   sum_{b in F} cosh(|eta_b| y) = q * I0(2y)^{n/2}  in char-0,
//                       and = sum_r (q E_r / (2r)!) y^{2r}  exactly (char-p E_r the actual energy).
//
//   DC-subtracted prize object:  Psi(y) = sum_{b != 0} cosh(|eta_b| y)
//                                       = n * sum_{cosets j} cosh(|eta_j| y).
//
//   char-0 reference:  Psi_0(y) = q * I0(2y)^{n/2} - cosh(n y).
//   wraparound excess: D(y) = Psi_charp(y) - Psi_0(y).
//
// Saddle:  y*^2 = 2 log q / n   (q = p).   Budget: MGF <= q^2  <=>  Psi(y*) <= q^2 - cosh(n y*) ~ q^2.
//
// Reports, at the saddle y*, for each structured THIN prime p ~ n^beta (p == 1 mod n):
//   Psi_charp, Psi_0(Bessel), D=excess, D/q^2 (slack used), D/Psi_0 (excess vs char-0),
//   q^2 (budget), Psi_charp/q^2 (fraction of budget), and char-0 fraction Psi_0/q^2.
//
// Usage: mgfexcess <n> <num_primes> <beta_mult>   e.g.  mgfexcess 16 12 4
use rayon::prelude::*;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn v2(mut x:u64)->u32{let mut v=0;while x%2==0{x/=2;v+=1;}v}

// modified Bessel I0(z) via series; z moderate (2y*, y*=sqrt(2 ln p / n)). Use log-domain for I0^{n/2}.
fn bessel_i0(z:f64)->f64{
    // I0(z) = sum_{k>=0} (z/2)^{2k} / (k!)^2 ; converges fast for z up to ~30. For larger, use asymptotic.
    if z < 30.0 {
        let mut term = 1.0f64;
        let mut sum = 1.0f64;
        let half = z*0.5;
        let half2 = half*half;
        for k in 1..200 {
            term *= half2 / ((k as f64)*(k as f64));
            sum += term;
            if term < sum*1e-18 { break; }
        }
        sum
    } else {
        // asymptotic I0(z) ~ e^z / sqrt(2 pi z) * (1 + 1/(8z) + 9/(128 z^2) + ...)
        let corr = 1.0 + 1.0/(8.0*z) + 9.0/(128.0*z*z) + 225.0/(3072.0*z*z*z);
        z.exp() / (2.0*std::f64::consts::PI*z).sqrt() * corr
    }
}
// log I0(z) directly (stable for large z)
fn log_bessel_i0(z:f64)->f64{
    if z < 30.0 {
        bessel_i0(z).ln()
    } else {
        let corr = 1.0 + 1.0/(8.0*z) + 9.0/(128.0*z*z) + 225.0/(3072.0*z*z*z);
        z - 0.5*(2.0*std::f64::consts::PI*z).ln() + corr.ln()
    }
}

// compute the m distinct |eta_j|^2 coset values
fn coset_periods(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let m=(p-1)/n;
    let h=powmod(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i,p)).collect();
    let tau=2.0*std::f64::consts::PI/(p as f64);
    (0..m).into_par_iter().map(|j|{
        let b=powmod(g,j,p);
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu{
            let bx=mulmod(b,x,p) as f64;
            let a=tau*bx;
            re+=a.cos(); im+=a.sin();
        }
        re*re+im*im   // |eta_j|^2
    }).collect()
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64=args.get(1).and_then(|s|s.parse().ok()).unwrap_or(16);
    let num:usize=args.get(2).and_then(|s|s.parse().ok()).unwrap_or(12);
    let beta:u32=args.get(3).and_then(|s|s.parse().ok()).unwrap_or(4);
    let base=n.pow(beta);
    let mut p=base;
    p += (n + 1 - p%n)%n;
    let nf=n as f64;
    println!("# n={} beta-target={} base=n^{}={}", n, beta, beta, base);
    println!("# saddle y*^2 = 2 ln q / n.   budget = q^2.   D = excess = Psi_charp - Psi_0(Bessel).");
    println!("# logs are natural-log MAGNITUDES (divide by ln q to read as power of q).");
    println!("# {:>13} {:>3} {:>6} {:>8} {:>9} {:>9} {:>9} {:>9} {:>9} {:>8} {:>8}",
             "p","v2","beta","y*","lnPsi_cp","lnQI0nh","lnCoshN","lnQ2","Pcp/q2","D/q2pow","slk");
    let mut found=0;
    while found<num{
        if p%n==1 && isprime(p){
            let lq = (p as f64).ln();
            let beta_eff = lq/nf.ln();
            let ystar2 = 2.0*lq/nf;
            let ystar = ystar2.sqrt();
            let v = coset_periods(n,p);
            let m = v.len() as f64;
            // top period for L^2 vs sup diagnostic
            let m2max = v.iter().cloned().fold(0.0f64,f64::max);
            // char-p MGF (DC subtracted): Psi = n * sum_j cosh(|eta_j| y*)
            // work in log domain to avoid overflow at large p.
            // log( sum_j cosh(|eta_j| y*) ) = LSE_j log cosh(...).  cosh(x) ~ e^x/2 for large x.
            let logcosh = |x:f64| -> f64 {
                if x > 20.0 { x - std::f64::consts::LN_2 } else { x.cosh().ln() }
            };
            // log-sum-exp over cosets
            let logs:Vec<f64>=v.iter().map(|&x2|{
                let absx = x2.sqrt();
                logcosh(absx*ystar)
            }).collect();
            let lmax = logs.iter().cloned().fold(f64::NEG_INFINITY,f64::max);
            let lse:f64 = lmax + logs.iter().map(|&l|(l-lmax).exp()).sum::<f64>().ln();
            let log_psi_cp = nf.ln() + lse;  // log Psi_charp
            // char-0 reference: Psi_0 = q * I0(2y*)^{n/2} - cosh(n y*).
            // log(q I0(2y*)^{n/2}) = ln q + (n/2) log I0(2y*)
            let log_q_i0 = lq + (nf/2.0)*log_bessel_i0(2.0*ystar);
            // cosh(n y*) ~ e^{n y*}/2:  log = n y* - ln 2  (n y* is huge => dominates? check)
            let log_cosh_ny = if nf*ystar > 20.0 { nf*ystar - std::f64::consts::LN_2 } else { (nf*ystar).cosh().ln() };
            // Psi_0 = exp(log_q_i0) - exp(log_cosh_ny).  Both could be large; subtract in log-safe way.
            // typically log_q_i0 >> log_cosh_ny (q^{0.5} vs e^{n y*}=q^{sqrt(2 n / ... )}?) -- compute both.
            let log2q = 2.0*lq; // log q^2 (budget)
            // ratios in log domain then exponentiate the (negative) log-ratios
            let psi_cp_over_q2 = (log_psi_cp - log2q).exp();
            // Psi_0: handle subtraction
            let (psi0_over_q2, d_over_q2, d_over_psi0);
            if log_q_i0 > log_cosh_ny {
                // Psi_0 = exp(log_q_i0)*(1 - exp(log_cosh_ny - log_q_i0))
                let sub = (log_cosh_ny - log_q_i0).exp();
                let log_psi0 = log_q_i0 + (1.0 - sub).ln();
                psi0_over_q2 = (log_psi0 - log2q).exp();
                // D = Psi_cp - Psi_0
                // log|D|: if Psi_cp > Psi_0
                if log_psi_cp > log_psi0 {
                    let r = (log_psi0 - log_psi_cp).exp();
                    let log_d = log_psi_cp + (1.0 - r).ln();
                    d_over_q2 = (log_d - log2q).exp();
                    d_over_psi0 = (log_d - log_psi0).exp();
                } else {
                    let r = (log_psi_cp - log_psi0).exp();
                    let log_d = log_psi0 + (1.0 - r).ln();
                    d_over_q2 = -(log_d - log2q).exp();
                    d_over_psi0 = -(log_d - log_psi0).exp();
                }
            } else {
                // cosh(n y*) dominates I0 term => Psi_0 ~ negative? shouldn't happen; flag
                psi0_over_q2 = -1.0; d_over_q2 = -1.0; d_over_psi0 = -1.0;
            }
            let slack_ok = if psi_cp_over_q2 <= 1.0 {"YES"} else {"NO!"};
            // express each quantity as POWER OF q: ln(X)/ln(q)
            let pow_psi_cp = log_psi_cp/lq;
            let pow_qi0    = log_q_i0/lq;
            let pow_coshn  = log_cosh_ny/lq;
            // D/q2 expressed as a power of q (signed): use d_over_q2 which is signed ratio to q^2
            let d_pow = if d_over_q2.abs() > 0.0 {
                2.0 + d_over_q2.abs().ln()/lq  // log_q(|D|) = 2 + log_q(|D|/q^2)
            } else { f64::NEG_INFINITY };
            let d_pow_signed = if d_over_q2 < 0.0 { -d_pow } else { d_pow };
            println!("{:>15} {:>3} {:>6.3} {:>8.4} {:>9.4} {:>9.4} {:>9.4} {:>9.4} {:>9.3} {:>8.3} {:>8}",
                p, v2(p-1), beta_eff, ystar,
                pow_psi_cp, pow_qi0, pow_coshn, 2.0*1.0,
                psi_cp_over_q2, d_pow_signed, slack_ok);
            let _ = (m, m2max, psi0_over_q2, d_over_psi0);
            found+=1;
        }
        p+=n;
    }
}
