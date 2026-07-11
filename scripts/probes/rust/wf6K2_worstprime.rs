// wf-K2: worst-case-over-primes K_eff(n) stratified by v2(p-1).  PARALLEL (std threads).
// For each n=2^mu, scan MANY primes p (n|p-1) near beta~4; per prime compute the
// nonprincipal moment route's K_eff at optimal depth, M_bound/prize, and the ACTUAL
// C = eta_max/prize (the true M(n)/prize we must bound). Take WORST over primes;
// stratify by v2(p-1). Question: does worst-case grow faster than generic? v2 envelope?
//
// E_r' = (1/p) sum_{b!=0} eta_b^{2r}, EXCLUDING principal coset (eta=n).
// char0 = (2r-1)!! n^r. K_eff = (E_r'/char0)^{1/r} at depth minimizing M_bound.
// M_bound = (p * E_r')^{1/2r}.  prize = sqrt(n * ln(p/n)).
use std::f64::consts::PI;
use std::sync::{Arc,Mutex};
use std::thread;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=0.0f64;for j in 1..=r{v+=((2*j-1)as f64).ln()}v} // ln (2r-1)!!

// (M_bound/prize, K_eff@bestdepth, C_actual=eta_max/prize)
fn eval_prime(n:u64,p:u64,rmax:usize)->(f64,f64,f64){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let eta0=n as f64;
    // we only need sums S2[r]=sum_{b!=0} eta^{2r} and etamax. Stream the cosets.
    let mut s2=vec![0.0f64; rmax+1];
    let mut etamax=0.0f64;
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0;
        for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64; re+=(2.0*PI*(t as f64)/p as f64).cos();}
        if (re-eta0).abs()>0.5 {
            let ar=re.abs(); if ar>etamax {etamax=ar;}
            let e2=re*re; let mut pw=1.0;
            for r in 1..=rmax { pw*=e2; s2[r]+=pw; }
        }
        b=((b as u128*gn as u128)%p as u128)as u64;
    }
    let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
    let mut best_mb=f64::INFINITY; let mut best_keff=0.0;
    for r in 1..=rmax {
        let er = s2[r]/(p as f64);
        let lnc0 = dfact(r)+ (r as f64)*(n as f64).ln();
        let keff = ((er.ln()-lnc0)/r as f64).exp();
        let mb = (p as f64 * er).powf(1.0/(2.0*r as f64));
        if mb<best_mb { best_mb=mb; best_keff=keff; }
    }
    (best_mb/prize, best_keff, etamax/prize)
}

fn scan(n:u64, beta_lo:f64, beta_hi:f64, count:usize, rmax:usize, nthreads:usize){
    let lo=(n as f64).powf(beta_lo) as u64;
    let hi=(n as f64).powf(beta_hi) as u64;
    // collect candidate primes first (cheap), then eval in parallel
    let mut primes=vec![];
    let mut p = lo - (lo% n) + 1; if p<lo {p+=n;}
    while p<=hi && primes.len()<count*4 { if isp(p){primes.push(p);} p+=n; }
    // subsample evenly to `count`
    let step = (primes.len().max(1)+count-1)/count.max(1);
    let cand: Vec<u64> = primes.iter().step_by(step.max(1)).cloned().take(count).collect();
    let cand=Arc::new(cand);
    let idx=Arc::new(Mutex::new(0usize));
    // results: (mb,keff,cact,p,v2)
    let res=Arc::new(Mutex::new(Vec::<(f64,f64,f64,u64,u32)>::new()));
    let mut handles=vec![];
    for _ in 0..nthreads {
        let cand=cand.clone(); let idx=idx.clone(); let res=res.clone();
        handles.push(thread::spawn(move||{
            loop{
                let i={let mut g=idx.lock().unwrap(); let i=*g; *g+=1; i};
                if i>=cand.len(){break}
                let p=cand[i];
                let (mb,keff,cact)=eval_prime(n,p,rmax);
                res.lock().unwrap().push((mb,keff,cact,p,v2(p-1)));
            }
        }));
    }
    for h in handles {h.join().unwrap();}
    let r=res.lock().unwrap();
    use std::collections::HashMap;
    let mut worst_mb=(0.0f64,0u64,0.0f64,0u32);
    let mut worst_c=(0.0f64,0u64,0u32);
    let mut by_v2: HashMap<u32,(f64,f64,u64)> = HashMap::new();
    for &(mb,keff,cact,p,vv) in r.iter(){
        if mb>worst_mb.0 {worst_mb=(mb,p,keff,vv);}
        if cact>worst_c.0 {worst_c=(cact,p,vv);}
        let e=by_v2.entry(vv).or_insert((0.0,0.0,0));
        if mb>e.0 {*e=(mb,cact,p);}
    }
    println!("=== n={} ({} primes, beta [{:.1},{:.1}]) ===",n,r.len(),beta_lo,beta_hi);
    println!("  WORST M_bound/prize = {:.4} @p={} (K_eff={:.3} v2={})",worst_mb.0,worst_mb.1,worst_mb.2,worst_mb.3);
    println!("  WORST C_actual/prize= {:.4} @p={} (v2={})",worst_c.0,worst_c.1,worst_c.2);
    let mut vs:Vec<u32>=by_v2.keys().cloned().collect(); vs.sort();
    for vv in vs {let (mb,c,p)=by_v2[&vv]; println!("    v2={:2}: M_bound/prize={:.4} C_act={:.4} (p={})",vv,mb,c,p);}
}

fn main(){
    let nt=8;
    scan(16,  3.0, 4.8, 500, 16, nt);
    scan(32,  3.0, 4.4, 500, 20, nt);
    scan(64,  3.0, 4.0, 400, 22, nt);
    scan(128, 2.9, 3.7, 300, 24, nt);
    scan(256, 2.7, 3.4, 250, 26, nt);
    scan(512, 2.6, 3.1, 200, 28, nt);
    scan(1024,2.5, 2.95,160, 30, nt);
}
