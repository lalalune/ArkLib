// wf-S2 (#444): the EQUIDISTRIBUTION CONSTANT kappa at depth r, prize scale.
//
// The S2 reduction (_wfS2_equidist_to_M.lean) collapses the prize to ONE inequality:
//   M^{2r} <= (kappa/c) * E_r,   with E_r <= K^r (2r-1)!! n^r (proven char-0, transfer-pending),
// where
//   kappa := M^{2r} * N_r / T_r      (equidistribution constant; 1 = perfectly flat)
//   c     := N_r / q                 (support fraction; spread floor guarantees c >= ~1/3)
//   T_r   := sum_{b!=0} |eta_b|^{2r}  (nonprincipal 2r-moment)
//   N_r   := #{b!=0 : eta_b != 0}     (nonprincipal support size)
//   M^{2r}:= max_{b!=0} |eta_b|^{2r}.
//
// kappa is exactly  (max term)/(support-average) = PAPR_r restricted to the nonprincipal support.
// The reduction is prize-relevant IFF kappa is BOUNDED (ideally O(log) -> after the 1/2r root it
// is O(1)) and c is bounded below, uniformly in n at prize scale. This probe measures kappa(r),
// c, and the resulting M-bound  M <= ((kappa/c) E_r)^{1/2r}  vs the prize target sqrt(n ln(q/n)),
// at beta=4, comparing structured (max v2(p-1)) vs generic primes.
//
// usage: probe_wfS2_equidist_kappa [n1 n2 ...]   default 16 32 64 128
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(k:u64)->f64{ // (2k-1)!!
    let mut r=1.0f64; let mut i=1u64; while i<=2*k-1 {r*=i as f64; i+=2;} r
}
// per-coset w_b = |eta_b|^2 over the m transversal reps b = g^0..g^{m-1}; the principal coset
// (b in mu_n) has w = n^2 and is EXCLUDED from the nonprincipal stats.
fn percoset_w(n:u64,p:u64)->Vec<f64>{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let mut out=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu { let t=((b as u128*x as u128)%p as u128)as u64; let a=2.0*PI*(t as f64)/p as f64; re+=a.cos(); im+=a.sin(); }
        out.push(re*re+im*im);
        b=((b as u128*g as u128)%p as u128)as u64;
    }
    out
}
fn analyze(tag:&str,n:u64,p:u64){
    let w=percoset_w(n,p);
    let nn=n as f64; let q=p as f64; let m=w.len() as f64;
    let beta=q.ln()/nn.ln();
    // nonprincipal entries: exclude the principal coset (w=n^2). Each transversal rep stands for
    // n actual frequencies b in F^* (same |eta|), so N_r = n * (#nonprincipal transversal reps with w>0).
    let np:Vec<f64>=w.iter().cloned().filter(|&x|(x-nn*nn).abs()>0.5).collect();
    let support_reps=np.iter().filter(|&&x|x>1e-9).count() as f64;
    let nr = nn*support_reps;                 // N_r counts actual frequencies
    let c = nr/q;                             // support fraction
    println!("[{}] n={} p={} v2={} beta={:.2}  c=N/q={:.4}", tag,n,p,v2(p-1),beta,c);
    println!("    {:>3} {:>10} {:>12} {:>10} {:>10} {:>12} {:>10}", "r","kappa","M^(1/r)/sqrt(n)","(2r-1)!!^1/2r","Mbound","prize_tgt","Mb/tgt");
    for r in [1u64,2,3,4,5,8,12,16] {
        let p2r = (2*r) as i32;
        // moments over nonprincipal frequencies, scaled by n (each rep = n freqs)
        let tr: f64 = nn * np.iter().map(|&x| x.powi(r as i32)).sum::<f64>(); // T_r = sum |eta|^{2r}
        let mmax = np.iter().cloned().fold(0.0f64,f64::max);                  // max |eta|^2
        let m2r = mmax.powi(r as i32);                                        // M^{2r}
        if tr<=0.0 {continue;}
        let kappa = m2r * nr / tr;            // (max term)/(support avg)
        let m = mmax.sqrt();                  // M = max |eta_b|
        // empirical M^{1/r}... report M/sqrt(n) (depth-independent, = the thing prize bounds by sqrt(log))
        let m_over_sqrtn = m/nn.sqrt();
        // reduction bound: M <= ((kappa/c) E_r)^{1/2r}; use E_r = (2r-1)!! n^r (char-0 Wick, K=1 anchor)
        let er = dfact(r)*nn.powi(r as i32);
        let mbound = ((kappa/c)*er).powf(1.0/p2r as f64);
        let prize_tgt = (nn*(q/nn).ln()).sqrt();
        let dfr = dfact(r).powf(1.0/p2r as f64);
        println!("    {:>3} {:>10.3} {:>12.4} {:>12.4} {:>10.3} {:>12.3} {:>10.4}",
            r, kappa, m_over_sqrtn, dfr, mbound, prize_tgt, mbound/prize_tgt);
    }
    println!();
}
fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() } else { vec![16,32,64,128] };
    println!("# wf-S2 EQUIDISTRIBUTION CONSTANT kappa(r) at prize scale (beta=4).");
    println!("# reduction: M^2r <= (kappa/c) E_r. kappa=(max term)/(support avg); c=N/q.");
    println!("# prize-relevant iff kappa bounded (O(log)) & c bounded below; Mbound/prize_tgt -> O(1).");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let mut p = target.max(100003); p = p - (p%n) + 1; if p<=2 {p+=n;}
        let mut best_s=(0u64,0u32); let mut best_g=(0u64,99u32); let mut cnt=0;
        while cnt<300 { if p%n==1 && isp(p) { let vv=v2(p-1); if vv>best_s.1 {best_s=(p,vv);} if vv<best_g.1 {best_g=(p,vv);} cnt+=1; } p+=n; }
        analyze("STRUCT",n,best_s.0);
        analyze("GENERIC",n,best_g.0);
    }
}
