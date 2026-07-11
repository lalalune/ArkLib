// Lane K2 (#444): is the Gauss-period field  b -> log|eta_b|  LOG-CORRELATED (so the
// sharp FHK / Arguin-Belius-Bourgade CUE-max extreme-value theory  max ~ logN - (3/4)loglogN
// would apply and could give a sub-Gaussian SHARPER max) or WHITE NOISE (so the only
// available extreme-value prediction is the iid-Gaussian one = sqrt(2n log m) = the OPEN
// BGK target, with NO sharper upper handle)?
//
// Method (EXACT integer phase accumulation, NOT float-FFT): compute eta_b = sum_{x in mu_n} e_p(bx)
// over mu_n = order-n=2^mu subgroup, n|p-1, p PRIME, p ~ n^4 (beta=4 prize regime). Then measure
//   (1) the empirical distribution of normalized real/imag parts vs N(0,1) (Sato-Tate = Gaussian);
//   (2) Cov(log|eta_b|, log|eta_{b'}|) vs -log|b-b'| (archimedean lag) AND vs 2-adic v_2(b-b') lag;
//   (3) the empirical max vs the iid-Gaussian extreme value sqrt(2n log m) and vs the
//       log-correlated-field value (sqrt n)*(log m - (3/4) loglog m) which is what FHK would give
//       if log-correlated. Multi-prime to confirm genericity.
//
// VERDICT logic: log-corr <=> cov(d) ~ -c ln d with a clear negative slope; white-noise <=> cov~0.
// If WHITE NOISE: the FHK sharper max is INAPPLICABLE; the extreme-value prediction is the
// iid-Gaussian one which IS the open BGK object => REDUCES-TO-FENCE (F0/F11). Honest.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let a2c=a as u128;let mut a2=a2c;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}let _=&mut a;r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn v2(mut x:u64)->u32{if x==0{return 64}let mut k=0;while x&1==0{x>>=1;k+=1}k}

fn run(n:u64, pstart:u64){
    let p=fp(n,pstart);
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; // number of distinct cosets = number of distinct period values
    // compute eta_b for a block of frequencies b=1..bmax
    let bmax = std::cmp::min(20000u64, p-1) as usize;
    let mut re=vec![0.0f64;bmax+1];
    let mut im=vec![0.0f64;bmax+1];
    let mut lg=vec![0.0f64;bmax+1];
    let mut maxabs=0.0f64;
    for b in 1..=bmax {
        let mut r=0.0;let mut i=0.0;
        for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;let a=2.0*PI*(t as f64)/p as f64;r+=a.cos();i+=a.sin();}
        re[b]=r;im[b]=i; let ab=(r*r+i*i).sqrt(); if ab>maxabs{maxabs=ab;}
        lg[b]=0.5*(r*r+i*i).max(1e-12).ln();
    }
    // (1) Gaussianity of normalized real part: re/sqrt(n/2) should be ~ N(0,1) (var of Re over random b is n/2)
    let xs:Vec<f64>=(1..=bmax).map(|b|re[b]).collect();
    let mre=xs.iter().sum::<f64>()/xs.len() as f64;
    let vre=xs.iter().map(|v|(v-mre).powi(2)).sum::<f64>()/xs.len() as f64;
    let m4=xs.iter().map(|v|(v-mre).powi(4)).sum::<f64>()/xs.len() as f64;
    let kurt=m4/(vre*vre); // Gaussian -> 3
    // (2a) archimedean-lag covariance of log|eta|
    let mlg=lg[1..=bmax].iter().sum::<f64>()/bmax as f64;
    let vlg=lg[1..=bmax].iter().map(|v|(v-mlg).powi(2)).sum::<f64>()/bmax as f64;
    println!("n={} mu={} p={} m=(p-1)/n={} beta={:.2}", n, (n as f64).log2() as u32, p, m, (p as f64).ln()/(n as f64).ln());
    println!("  Var(Re eta)={:.3} (iid pred n/2={:.1});  excess kurtosis(Re)={:+.3} (Gaussian=0)", vre, n as f64/2.0, kurt-3.0);
    print!("  ARCHIMEDEAN-lag cov(log|eta|)/var:");
    for d in [1usize,2,3,4,8,16,32,64,128,256] {
        let mut c=0.0;let mut cnt=0; for b in 1..=(bmax-d){ c+=(lg[b]-mlg)*(lg[b+d]-mlg); cnt+=1; } c/=cnt as f64;
        print!(" d{}={:+.3}", d, c/vlg);
    }
    println!();
    // (2b) 2-adic-lag covariance: bin pairs (b,b') by v_2(b XOR b' ~ b-b') ; manifesto says mu_n's structure is 2-adic
    let mut sums=vec![0.0f64;40]; let mut cnts=vec![0u64;40];
    let sample = if bmax>3000 {3000} else {bmax};
    for b in 1..=sample { for bp in (b+1)..=sample {
        let k=v2((bp-b) as u64) as usize; if k<40 { sums[k]+=(lg[b]-mlg)*(lg[bp]-mlg); cnts[k]+=1; }
    }}
    print!("  2-ADIC v2(b-b') cov(log|eta|)/var:");
    for k in 0..8 { if cnts[k]>0 { print!(" v2={}:{:+.3}(n{})", k, sums[k]/cnts[k] as f64/vlg, cnts[k]); } }
    println!();
    // (3) extreme value comparison
    let sqn=(n as f64).sqrt();
    let iid_gauss = sqn*(2.0*(m as f64).ln()).sqrt();   // iid complex-Gaussian max over m cosets
    let lm=(m as f64).ln();
    let fhk = sqn*(lm - 0.75*lm.ln().max(1.0));          // log-correlated-field (FHK/ABB) sharper max
    println!("  MAX|eta| (block)={:.3}  | iid-Gauss sqrt(2n ln m)={:.3} (ratio {:.3}) | FHK logcorr={:.3} (ratio {:.3})",
        maxabs, iid_gauss, maxabs/iid_gauss, fhk, maxabs/fhk);
    println!();
}
fn main(){
    println!("=== Lane K2: log-correlated vs white-noise structure of the Gauss-period field ===");
    println!("(log-corr => FHK sharper max applies; white-noise => only iid-Gaussian EVT = open BGK)\n");
    for &n in &[16u64,32,64,128] {
        // multi-prime: two distinct primes p ~ n^4 to confirm genericity
        run(n, (n as f64).powf(4.0) as u64);
        run(n, (n as f64).powf(4.0) as u64 + 7*n);
    }
}
