// wf-F1: PIN the beta-threshold for normalized-ladder antitonicity / r=1 cap.
// R(r) = M_2r/[(2r-1)!! n^r].  We saw R-cap holds at beta~4, breaks at beta~2.
// For fixed n, sweep beta (choose primes p ~ n^beta) and find smallest beta s.t. maxR<=R(1)+eps
// to depth r ~ 1.5 ln q.  The PRIZE has beta = log2(p)/log2(n) = (30+128)/30 ~ 5.27, n=2^30.
// If threshold beta* < 5.27 (and not growing fast in n), the prize regime is SAFE.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let _=&mut a;let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

fn maxR_over_R1(n:u64,p:u64)->(f64,f64,usize){ // returns (R(1), maxR, argmax_r)
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let mf=m as f64; let lnq=(p as f64).ln();
    let rmax=((2.0*lnq) as usize).max(6);
    let mut r1=0.0; let mut maxr=0.0; let mut arg=0;
    for r in 1..=rmax {
        let mut s=0.0; for &e in &eta { s+=e.powi(2*r as i32); }
        let rr=(s/mf)/(dfact(r)*(n as f64).powi(r as i32));
        if r==1 {r1=rr;}
        if rr>maxr {maxr=rr; arg=r;}
    }
    (r1,maxr,arg)
}

fn main(){
    for &n in &[16u64,32,64,128,256] {
        println!("--- n={} (sweep beta) ---", n);
        // beta from ~1.5 up to ~5.5
        for k in 0..16 {
            let beta = 1.5 + 0.27*(k as f64);
            let target = (n as f64).powf(beta) as u64;
            let p = fp(n, target.max(n*4));
            let actual_beta = (p as f64).ln()/(n as f64).ln();
            let (r1,maxr,arg) = maxR_over_R1(n,p);
            let ok = maxr <= r1 + 1e-9;
            println!("  beta~{:.2} (p={:>14}) R(1)={:.4} maxR={:.4}@r{:<2} capped={}", actual_beta, p, r1, maxr, arg, ok);
            if ok && actual_beta>1.6 { /* keep going to confirm stays capped */ }
        }
    }
    let pb = 2.0f64.powi(30); // n
    println!("\nPRIZE: n=2^30={:.3e}, m=2^128, p~n*m=2^158, beta=158/30={:.3}", pb, 158.0/30.0);
}
