// #444 A04 (S6 Weil-II): the TRUE p-scaling of spur_r(p), and the VACUITY of the toric envelope.
//
// FINDING TO PIN: spur_r(p) does NOT grow like the naive Weil weight p^{r-1}. The config
// variety V_r = {x in mu_n^{2r}: sum eps_i x_i = 0} is a 0-DIMENSIONAL etale scheme; its
// F_p-point count is BOUNDED INDEPENDENT of p (= a count of cyclotomic relations that hold
// mod p but not over C). So spur_r is a bounded count, spur/p^{r-1} -> 0. We measure:
//   - spur_r(p) vs p across a long band: is it bounded / decreasing (0-dim) or growing as p^{r-1}?
//   - the CROSS-CHECK: the S6 envelope C(2r,r)*p^{r-1} vs E_r^char0 = (2r-1)!! n^r. The envelope
//     is VACUOUS exactly when p^{r-1} > n^r, i.e. beta > r/(r-1). At beta=4, vacuous for ALL r>=2.
//
// So the toric envelope, even with the d-free Betti C(2r,r), CANNOT discharge the prize at depth
// r ~ ln q: the Weil ERROR weight p^{r-1} dwarfs the char-0 main term n^r. We report the exact
// crossover beta*(r) = r/(r-1) and confirm spur is in fact bounded (the route's failure is the
// NORMALIZATION, not an inflating spur).

use std::collections::HashMap;
fn mpow(a: u64, mut e: u64, p: u64) -> u64 { let mut r:u128=1; let mut a2=a as u128; let pp=p as u128;
    while e>0 { if e&1==1 { r=r*a2%pp; } a2=a2*a2%pp; e>>=1; } r as u64 }
fn is_prime(n: u64) -> bool { if n<2 {return false;}
    for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37] { if n%q==0 {return n==q;} }
    let mut d=n-1; let mut s=0u32; while d&1==0 {d>>=1; s+=1;}
    'a: for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37] { let mut x=mpow(a,d,n);
        if x==1||x==n-1 {continue;} for _ in 0..s-1 {x=((x as u128*x as u128)%n as u128)as u64; if x==n-1 {continue 'a;}} return false; } true }
fn find_prime_cong1(n: u64, lo: u64) -> u64 { let mut p=lo+((1+n-lo%n)%n); if p<=2 {p+=n;}
    loop { if p>2 && p%n==1 && is_prime(p) {return p;} p+=n; } }
fn primitive_root(p: u64) -> u64 { let mut m=p-1; let mut fs=vec![]; let mut d=2;
    while d*d<=m {if m%d==0 {fs.push(d); while m%d==0 {m/=d;}} d+=1;} if m>1 {fs.push(m);}
    let mut g=2u64; loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) {return g;} g+=1; } }
fn v2(mut x:u64)->u32 {let mut v=0; while x&1==0 {v+=1; x>>=1;} v}

fn er_charp(mu:&[u64], r:usize, p:u64)->u128 {
    let mut cur:HashMap<u64,u128>=HashMap::new();
    for &x in mu { *cur.entry(x%p).or_insert(0)+=1; }
    for _ in 1..r { let mut nxt:HashMap<u64,u128>=HashMap::new();
        for (&s,&c) in &cur { for &x in mu { let t=((s as u128+x as u128)%p as u128)as u64; *nxt.entry(t).or_insert(0)+=c; } } cur=nxt; }
    cur.values().map(|&c| c*c).sum() }
fn er_char0(n:usize, r:usize)->u128 {
    let half=n/2; let mut cur:HashMap<Vec<i32>,u128>=HashMap::new();
    for k in 0..n { let idx=k%half; let sgn=if k<half {1} else {-1}; let mut v=vec![0i32;half]; v[idx]=sgn; *cur.entry(v).or_insert(0)+=1; }
    for _ in 1..r { let mut nxt:HashMap<Vec<i32>,u128>=HashMap::new();
        for (vt,&c) in &cur { for k in 0..n { let idx=k%half; let sgn=if k<half {1} else {-1}; let mut w=vt.clone(); w[idx]+=sgn; *nxt.entry(w).or_insert(0)+=c; } } cur=nxt; }
    cur.values().map(|&c| c*c).sum() }
fn comb(n:usize,k:usize)->f64 { if k>n {return 0.0;} let k=k.min(n-k); let mut r=1.0; for i in 0..k {r=r*(n-i)as f64/(i+1)as f64;} r }
fn double_fact(r:usize)->f64 {let mut v=1.0; for j in 1..=r {v*=(2*j-1)as f64;} v}

fn main() {
    println!("================================================================================");
    println!("A04: TRUE p-scaling of spur_r(p) (is it bounded/0-dim, or p^(r-1)?)");
    println!("================================================================================");
    // For fixed (n,r) with r >= 4 (where spur>0 happens), measure spur across a LONG p-band
    // at fixed beta-window, BUT also at increasing beta, to see if spur grows or is bounded.
    for &(n, r) in &[(16usize,4usize),(16,5),(32,4)] {
        let nn=n as u64; let c0=er_char0(n,r);
        println!("\n[n={} r={}] char0=(2r-1)!!n^r? exact char0={}  ((2r-1)!!n^r={:.0})", n, r, c0, double_fact(r)*(n as f64).powi(r as i32));
        // sweep beta from 3.5 to 6.0: does spur (when >0) grow with p?
        let mut maxspur: i128 = 0;
        for &beta in &[3.5f64, 4.0, 4.5, 5.0, 5.5] {
            let lo=(nn as f64).powf(beta) as u64;
            let mut p=find_prime_cong1(nn, lo.max(200));
            // among next 40 primes in this beta neighborhood, find max spur and count nonzero
            let mut tries=0; let mut nz=0; let mut local_max:i128=0; let mut sample_p=p;
            while tries<60 {
                let h=mpow(primitive_root(p),(p-1)/nn,p);
                let mu:Vec<u64>=(0..n).map(|j| mpow(h,j as u64,p)).collect();
                let spur=er_charp(&mu,r,p) as i128 - c0 as i128;
                if spur>0 {nz+=1; if spur>local_max {local_max=spur; sample_p=p;}}
                p=find_prime_cong1(nn,p+1); tries+=1;
            }
            if local_max>maxspur {maxspur=local_max;}
            println!("   beta~{:.1}: nonzero spur {}/60, max spur={} (at p~{}), spur/p^(r-1)={:.3e}",
                     beta, nz, local_max, sample_p, if local_max>0 {(local_max as f64)/(sample_p as f64).powi((r as i32)-1)} else {0.0});
        }
        // p-FREE envelope check: spur <= C(2r,r) * n^(2r-1) ?
        let pfree=comb(2*r,r)*(n as f64).powi((2*r-1) as i32);
        println!("   => max spur over all beta = {}.  p-FREE envelope C(2r,r)*n^(2r-1)={:.3e} (margin {:.1e})",
                 maxspur, pfree, (maxspur as f64)/pfree);
    }

    println!("\n================================================================================");
    println!("THE VACUITY: toric envelope C(2r,r)*p^(r-1) vs char-0 main term (2r-1)!!n^r");
    println!("  envelope is USEFUL only when C(2r,r)*p^(r-1) <= (2r-1)!!*n^r, i.e. beta <= beta*(r).");
    println!("================================================================================");
    println!("  n      r   log2(char0)   log2(C(2r,r)p^(r-1)@beta=4)   beta*(r)=crossover   useful@beta=4?");
    let n_log2 = 30.0f64; let p_log2 = 120.0f64; // prize n=2^30, p=2^120
    for r in [2usize,4,10,40,83] {
        let log2_df = ((1..=r).map(|j| (2*j-1) as f64).map(f64::ln).sum::<f64>())/2f64.ln();
        let log2_cb = (lgamma(2.0*r as f64+1.0)-2.0*lgamma(r as f64+1.0))/2f64.ln();
        let char0_log2 = log2_df + r as f64 * n_log2;
        let env_log2 = log2_cb + (r as f64 -1.0)*p_log2;
        // beta*(r): C(2r,r) p^{r-1} = (2r-1)!! n^r => (r-1) beta log n + log C(2r,r) = r log n + log (2r-1)!!
        // beta* = [ r*n_log2 + log2_df - log2_cb ] / [ (r-1)*n_log2 ]
        let beta_star = (r as f64 * n_log2 + log2_df - log2_cb) / ((r as f64 -1.0)*n_log2);
        println!("  2^30   {:3} {:12.0}   {:24.0}   {:18.3}   {}",
                 r, char0_log2, env_log2, beta_star, env_log2 <= char0_log2);
    }
    println!("\nVERDICT: spur_r is a BOUNDED 0-dim count (spur/p^(r-1) -> 0), but the S6 toric envelope");
    println!("C(2r,r)*p^(r-1) is VACUOUS at beta=4 for all r>=2 (beta*(r) -> 1 as r grows). The Weil");
    println!("ERROR WEIGHT p^(r-1) dwarfs the char-0 main term n^r. Route works only at beta ~ 1 (saturated).");
}

fn lgamma(x:f64)->f64 {
    // Lanczos approximation
    let g=7.0; let c=[0.99999999999980993,676.5203681218851,-1259.1392167224028,
        771.32342877765313,-176.61502916214059,12.507343278686905,-0.13857109526572012,
        9.9843695780195716e-6,1.5056327351493116e-7];
    if x<0.5 { return (std::f64::consts::PI/(std::f64::consts::PI*x).sin()).ln()-lgamma(1.0-x); }
    let x=x-1.0; let mut a=c[0]; let t=x+g+0.5;
    for i in 1..9 { a+=c[i]/(x+i as f64); }
    0.5*(2.0*std::f64::consts::PI).ln()+(x+0.5)*t.ln()-t+a.ln()
}
