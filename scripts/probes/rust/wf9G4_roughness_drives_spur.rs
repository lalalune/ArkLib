// wf-G4: does the ROUGHNESS of m=(p-1)/n (its largest prime factor P^+(m)) drive
// the Gauss-period wall M(n) and the spurious mass spur_r(p) UP?
//
// THE G4 HYPOTHESIS (the lane's exact claim):
//   "structured (rough) primes are worst because (p-1)/n has a large prime factor enabling extra
//    coincidences." If true, M(n)/sqrt(n log m) is a clean INCREASING function of some smoothness
//    statistic of m -- e.g. P^+(m)/m, or log P^+(m). If that statistic is bounded for prize primes,
//    M is bounded. If M is UNCORRELATED with P^+(m), the G4 arithmetic-driver thesis is FALSE and the
//    wall is genuinely about the pseudorandom phase (BGK is a real wall, no clean arithmetic handle).
//
// We hold n FIXED and beta~4 FIXED (prize thinness), sweep ALL primes p == 1 (mod n) in a band, and
// for each measure:
//   M           = max_{b!=0} |sum_{x in mu_n} e_p(b x)|            (exact, FFT-free direct)
//   C           = M / sqrt(n * ln(p/n))                            (the prize-normalized constant)
//   Pplus       = largest prime factor of m=(p-1)/n                (ROUGHNESS)
//   logPp_logm  = ln P^+(m) / ln m                                 (smoothness index in [0,1])
//   v2          = v2(p-1)                                          (Fermat/quiet gate)
//   nsmall      = # divisors d>1 of m with d < n  (# small subgroups mu_n can interact with cheaply)
// Then we report Spearman-style: is C MONOTONE in logPp_logm? Print sorted-by-roughness so a
// GROWING witness sequence (if any) is visible. Reuses mn_wall's measure().
//
// build: rustc -O wf9G4_roughness_drives_spur.rs -o /tmp/g4rough

use std::f64::consts::PI;

fn mpow(_a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=_a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while (d as u128)*(d as u128)<=m as u128{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{v+=1;x>>=1;}v}
fn factorize(mut m:u64)->Vec<(u64,u32)>{let mut f=vec![];let mut d=2u64;while (d as u128)*(d as u128)<=m as u128{if m%d==0{let mut e=0;while m%d==0{m/=d;e+=1;}f.push((d,e));}d+=if d==2{1}else{2};}if m>1{f.push((m,1));}f}

fn measure(n:u64,p:u64)->f64{
    let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let mut best=0.0f64;
    let mut b=1u64; let gn=mpow(g,n,p);
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu {
            let t=( (b as u128 * x as u128) % p as u128) as u64;
            let ang=2.0*PI*(t as f64)/(p as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        let mag=(re*re+im*im).sqrt();
        if mag>best{best=mag;}
        b=(( b as u128 * gn as u128) % p as u128) as u64;
    }
    best
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = if args.len()>1 { args[1].parse().unwrap() } else { 32 };
    let beta:f64 = if args.len()>2 { args[2].parse().unwrap() } else { 4.0 };
    let nprimes:usize = if args.len()>3 { args[3].parse().unwrap() } else { 200 };
    let target = (n as f64).powf(beta) as u64;
    // sweep ALL primes p == 1 mod n in a band around n^beta, but cap m so measure() is feasible.
    // measure cost ~ m*n; cap m <= ~ 6e5.  m = (p-1)/n ~ n^{beta-1}.
    let mut rows:Vec<(f64,u64,f64,u32,u64,u32)> = vec![]; // (logPp_logm, p, C, v2, Pplus, nsmall)
    let mut p = {let mut lo=target.max(200003); lo += (1 + n - lo%n)%n; lo};
    let mut count=0;
    while count<nprimes {
        if p%n==1 && is_prime(p) {
            let m=(p-1)/n;
            if m>=2 && m <= 700_000 {
                let f=factorize(m);
                let pplus = f.iter().map(|x|x.0).max().unwrap();
                let logpp_logm = (pplus as f64).ln()/(m as f64).ln();
                let nsmall = {
                    // count divisors d of m with 1<d<n (cheap subgroup orders dividing m that are < n)
                    let mut c=0u32; let mut d=2u64;
                    while d< n { if m%d==0 { c+=1; } d+=1; }
                    c
                };
                let mm=measure(n,p);
                let c = mm/(((n as f64)*((p as f64/n as f64).ln())).sqrt());
                rows.push((logpp_logm, p, c, v2(p-1), pplus, nsmall));
                count+=1;
            }
        }
        p += n; // stay in residue class; cheaper than scanning all
        if p > target.saturating_mul(2) { break; }
    }
    eprintln!("# n={} beta~{} : {} primes (p==1 mod n, m=(p-1)/n<=700k)", n, beta, rows.len());
    // correlation: C vs logPp_logm  (Pearson)
    let k=rows.len() as f64;
    let mx:f64=rows.iter().map(|r|r.0).sum::<f64>()/k;
    let my:f64=rows.iter().map(|r|r.2).sum::<f64>()/k;
    let mut sxy=0.0;let mut sxx=0.0;let mut syy=0.0;
    for r in &rows {sxy+=(r.0-mx)*(r.2-my);sxx+=(r.0-mx)*(r.0-mx);syy+=(r.2-my)*(r.2-my);}
    let pearson = sxy/(sxx.sqrt()*syy.sqrt());
    // Spearman via ranks of (logPp_logm) and C
    let mut idx_x:Vec<usize>=(0..rows.len()).collect(); idx_x.sort_by(|&a,&b|rows[a].0.partial_cmp(&rows[b].0).unwrap());
    let mut idx_y:Vec<usize>=(0..rows.len()).collect(); idx_y.sort_by(|&a,&b|rows[a].2.partial_cmp(&rows[b].2).unwrap());
    let mut rx=vec![0.0;rows.len()]; let mut ry=vec![0.0;rows.len()];
    for (rk,&i) in idx_x.iter().enumerate(){rx[i]=rk as f64;}
    for (rk,&i) in idx_y.iter().enumerate(){ry[i]=rk as f64;}
    let mrx=(k-1.0)/2.0; let mry=mrx;
    let mut s2=0.0;let mut sx2=0.0;let mut sy2=0.0;
    for i in 0..rows.len(){s2+=(rx[i]-mrx)*(ry[i]-mry);sx2+=(rx[i]-mrx)*(rx[i]-mrx);sy2+=(ry[i]-mry)*(ry[i]-mry);}
    let spearman=s2/(sx2.sqrt()*sy2.sqrt());
    eprintln!("# Pearson(C, logPp/logm)  = {:.4}", pearson);
    eprintln!("# Spearman(C, logPp/logm) = {:.4}", spearman);
    eprintln!("#   (>0 and large => roughness DRIVES the wall = G4 thesis SUPPORTED;");
    eprintln!("#    ~0 => phase-blind, BGK is a genuine wall, no arithmetic handle)");
    // also Spearman of C vs nsmall (small-subgroup count)
    let mut idx_ns:Vec<usize>=(0..rows.len()).collect(); idx_ns.sort_by(|&a,&b|rows[a].5.cmp(&rows[b].5));
    let mut rns=vec![0.0;rows.len()]; for(rk,&i)in idx_ns.iter().enumerate(){rns[i]=rk as f64;}
    let mut s3=0.0;let mut sn2=0.0; for i in 0..rows.len(){s3+=(rns[i]-mrx)*(ry[i]-mry);sn2+=(rns[i]-mrx)*(rns[i]-mrx);}
    eprintln!("# Spearman(C, #small-subgroups<n) = {:.4}", s3/(sn2.sqrt()*sy2.sqrt()));
    // top-10 ROUGHEST and top-10 SMOOTHEST, show C
    rows.sort_by(|a,b|b.0.partial_cmp(&a.0).unwrap());
    eprintln!("# --- 10 ROUGHEST m (largest logPp/logm) ---");
    eprintln!("#   p            m         logPp/logm  Pplus       C       v2  nsmall");
    for r in rows.iter().take(10){ eprintln!("  {:>13} {:>11} {:8.4}  {:>11} {:7.4} {:3} {:5}", r.1, (r.1-1)/n, r.0, r.4, r.2, r.3, r.5); }
    eprintln!("# --- 10 SMOOTHEST m (smallest logPp/logm) ---");
    for r in rows.iter().rev().take(10){ eprintln!("  {:>13} {:>11} {:8.4}  {:>11} {:7.4} {:3} {:5}", r.1, (r.1-1)/n, r.0, r.4, r.2, r.3, r.5); }
    // the global worst C overall and its roughness
    let worst=rows.iter().cloned().fold((0.0,0,0.0,0,0,0),|acc,r| if r.2>acc.2 {r} else {acc});
    eprintln!("# WORST C overall = {:.4} at p={}, logPp/logm={:.4}, Pplus={}, v2={}", worst.2, worst.1, worst.0, worst.4, worst.3);
}
