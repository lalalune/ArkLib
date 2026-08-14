// spechist — #444 SHARPENED PRIZE: spectral histogram of Gauss periods |eta_b| near B=max.
// Goal: does the TOP-B SHARE of the saddle moment A_{r*}=sum_{b!=0}|eta_b|^{2r*} (r*=log q) -> 0?
// If the count of b with |eta_b|>=(1-eps)B is sub-poly, top-B share -> 0 => saddle moment is
// L2-DOMINATED (bulk), sup-B-blind => delta* computable at the saddle.
//
// For mu_n = unique multiplicative subgroup of order n in F_p (p≡1 mod n, p≈n^beta):
//   eta_b = sum_{x in mu_n} psi(b*x),  psi = additive char.  There are m=(p-1)/n distinct |eta_b|
//   values (one per coset of mu_n in F_p^*); b=0 (=> eta=n) excluded.
//
// Outputs per prime:
//   - B = max|eta_b|, B/sqrt(n), R = B/sqrt(2 n log m)  (Ramanujan ratio)
//   - histogram of |eta_b|/B in 10 bands
//   - NEAR-B counts: #{|eta_b| >= (1-eps)B} for eps=0.30,0.20,0.10,0.05,0.02,0.01
//   - saddle r* = round(log q) where q = p (field size); A_{r*}=sum|eta_b|^{2r*}
//   - TOP-1 share = B^{2r*}/A_{r*}, TOP-k cumulative shares
//   - L2 proxy: A_{r*} vs (#cosets)*<|eta_b|^{2r*}>_typical
// Usage: spechist <n> <num_primes> [start_offset_in_blocks]
use rayon::prelude::*;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn v2(mut x:u64)->u32{let mut v=0;while x%2==0{x/=2;v+=1;}v}

// Return all |eta_b| (length m) for b ranging over coset reps g^j, j=0..m-1.
fn all_abs(n:u64,p:u64)->(Vec<f64>,u64){
    let g=proot(p); let m=(p-1)/n;
    let h=powmod(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i,p)).collect();
    let tau=2.0*std::f64::consts::PI/(p as f64);
    let v:Vec<f64>=(0..m).into_par_iter().map(|j|{
        let b=powmod(g,j,p);
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu{
            let bx=mulmod(b,x,p) as f64;
            let a=tau*bx;
            re+=a.cos(); im+=a.sin();
        }
        (re*re+im*im).sqrt()
    }).collect();
    (v,m)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64=args.get(1).and_then(|s|s.parse().ok()).unwrap_or(64);
    let num:usize=args.get(2).and_then(|s|s.parse().ok()).unwrap_or(10);
    let off:i64=args.get(3).and_then(|s|s.parse().ok()).unwrap_or(0);
    let base=n.pow(4);
    let mut p=(base as i64 + off*(n as i64)) as u64;
    p += (n + 1 - p%n)%n;
    let nf=n as f64;
    println!("# n={}  base=n^4={}  (beta~4, thin regime)", n, base);
    println!("# m = #distinct |eta_b| cosets = (p-1)/n ; B=max|eta_b| ; sqrt(n)={:.3}", nf.sqrt());
    let mut found=0;
    // accumulate near-B count trend for sub-poly verdict
    let mut nearB_log: Vec<(u64,usize,usize,f64)> = vec![]; // (p, #>=0.9B, m, top1share)
    while found<num{
        if p%n==1 && isprime(p){
            let (abs,m)=all_abs(n,p);
            let mf=m as f64;
            let b_max=abs.iter().cloned().fold(0.0f64,f64::max);
            // sort descending copy for top-k
            let mut sorted=abs.clone();
            sorted.sort_by(|a,b|b.partial_cmp(a).unwrap());
            // L2 energy: sum |eta_b|^2  (should ~ p - n exact over b!=0)
            let l2:f64 = abs.iter().map(|x|x*x).sum();
            let logm=mf.ln();
            let r_ram = b_max/(2.0*nf*logm).sqrt();
            // histogram of ratio in 10 bands [0.0,0.1),...,[0.9,1.0]
            let mut hist=[0usize;10];
            for &x in &abs{
                let r=x/b_max;
                let mut idx=(r*10.0) as usize;
                if idx>9{idx=9;}
                hist[idx]+=1;
            }
            // near-B counts
            let eps_list=[0.30f64,0.20,0.10,0.05,0.02,0.01];
            let mut nearB=[0usize;6];
            for (k,&e) in eps_list.iter().enumerate(){
                let thr=(1.0-e)*b_max;
                nearB[k]=abs.iter().filter(|&&x|x>=thr).count();
            }
            // saddle r* = round(log q). q = p (field). Cap r* to keep pow finite; use f64.
            let logq=(p as f64).ln();
            let rstar=logq.round().max(2.0) as i64;
            // A_{2r*} = sum |eta_b|^{2 r*}. Use ln-domain to avoid overflow:
            //   compute via shares. exponent = 2*rstar.
            let expo=2.0*(rstar as f64);
            // top-1 share and cumulative top-k shares, computed stably:
            //   share_i = (|eta_i|/B)^expo  (since A = B^expo * sum (x/B)^expo)
            // denom_sum = sum_i (x_i/B)^expo
            let denom:f64 = abs.iter().map(|&x|(x/b_max).powf(expo)).sum();
            // top-k cumulative (sorted desc): how many top terms to reach 50%, 90%
            let mut cum=0.0f64; let mut k50=0usize; let mut k90=0usize; let mut k99=0usize;
            let mut top_shares=[0.0f64;5];
            for (i,&x) in sorted.iter().enumerate(){
                let s=(x/b_max).powf(expo)/denom;
                cum+=s;
                if i<5 {top_shares[i]=s;}
                if k50==0 && cum>=0.5 {k50=i+1;}
                if k90==0 && cum>=0.9 {k90=i+1;}
                if k99==0 && cum>=0.99 {k99=i+1;}
            }
            let top1=top_shares[0];
            // L2-domination check: if moment were L2-flat (all |eta|=sqrt(l2/m)),
            //   each share = 1/m. Effective participation ratio = 1/sum(share^2).
            let ipr:f64 = 1.0 / abs.iter().map(|&x|{let s=(x/b_max).powf(expo)/denom; s*s}).sum::<f64>();
            println!("# ---- p={} (v2={}, m={}, log q={:.2}, r*={}) ----",p,v2(p-1),m,logq,rstar);
            println!("#   B={:.4}  B/sqrt(n)={:.4}  R=B/sqrt(2n log m)={:.4}  L2=sum|eta|^2={:.1} (p-n={})",
                b_max, b_max/nf.sqrt(), r_ram, l2, p as i64 - n as i64);
            print!("#   hist |eta|/B bands [.0..1.0]: ");
            for h in hist {print!("{} ",h);}
            println!();
            print!("#   near-B #>=(1-eps)B: ");
            for (k,&e) in eps_list.iter().enumerate(){print!("eps{:.2}={} ",e,nearB[k]);}
            println!();
            println!("#   SADDLE r*={}: top1share={:.4e}  top5shares=[{:.3e},{:.3e},{:.3e},{:.3e},{:.3e}]",
                rstar, top1, top_shares[0],top_shares[1],top_shares[2],top_shares[3],top_shares[4]);
            println!("#   #terms for 50%/90%/99% of A_r* = {}/{}/{}  (of m={})  IPR(eff #freqs)={:.2}",
                k50,k90,k99,m,ipr);
            // === MGF object (the ACTUAL prize saddle): Psi(y)=sum cosh(|eta|y) at y*^2=2 log q/n ===
            // top-B share of MGF = cosh(B y*)/Psi(y*). This is the Poisson-AVERAGED moment,
            // NOT the single moment A_{r*}. Compute in ln-domain (cosh(z)~0.5 e^z for large z).
            let ystar = (2.0*logq/nf).sqrt();
            // Psi via log-sum-exp on exponents |eta|*ystar (using exp approx for cosh; add cosh exact)
            // exact cosh, but values can overflow: factor out e^{B*ystar}.
            let bz = b_max*ystar;
            // sum cosh(x*ystar) = e^{bz} * sum cosh(x ystar)/e^{bz}; cosh(x y)/e^{bz}=0.5(e^{(x-B)y}+e^{-(x+B)y})
            let mut psi_scaled=0.0f64;
            let mut topB_scaled=0.0f64;
            for (i,&x) in sorted.iter().enumerate(){
                let xy=x*ystar;
                let term = 0.5*((xy-bz).exp() + (-(xy+bz)).exp()); // cosh(xy)/e^{bz}
                psi_scaled+=term;
                if i==0 {topB_scaled=term;}
            }
            let mgf_top1_share = topB_scaled/psi_scaled; // = cosh(B y*)/Psi(y*)
            // Psi(y*) actual (scaled by e^{bz}): log Psi = bz + ln(psi_scaled)
            let log_psi = bz + psi_scaled.ln();
            // prize threshold: Psi(y*) <= q^2 i.e. log_psi <= 2 log q.  margin = 2logq - logPsi.
            let target = 2.0*logq;
            // MGF effective participation (Poisson-weighted IPR):
            let mgf_ipr = {
                let mut s2=0.0; for &x in &abs{let xy=x*ystar; let t=0.5*((xy-bz).exp()+(-(xy+bz)).exp())/psi_scaled; s2+=t*t;} 1.0/s2
            };
            // MGF: #terms (sorted desc) to reach 50%/90% of Psi
            let mut cumm=0.0f64; let mut mk50=0usize; let mut mk90=0usize;
            for (i,&x) in sorted.iter().enumerate(){
                let xy=x*ystar; let t=0.5*((xy-bz).exp()+(-(xy+bz)).exp())/psi_scaled;
                cumm+=t;
                if mk50==0 && cumm>=0.5 {mk50=i+1;}
                if mk90==0 && cumm>=0.9 {mk90=i+1;}
            }
            println!("#   MGF y*={:.4} (y*^2=2logq/n): top-B share=cosh(By*)/Psi={:.4e}  MGF-IPR={:.2}  #for50/90%={}/{}",
                ystar, mgf_top1_share, mgf_ipr, mk50, mk90);
            println!("#   PRIZE GATE: log Psi(y*)={:.3} vs target 2 log q={:.3}  margin={:.3} ({})",
                log_psi, target, target-log_psi, if log_psi<=target {"PASS"} else {"FAIL"});
            // === top-B share of the per-r moment A_r as a function of r (find where 0.4-3.8% lives) ===
            print!("#   top-B share of A_r vs r: ");
            for &rr in &[1i32,2,3,4,5,6,8,10,14,20]{
                let e2=2.0*(rr as f64);
                let den:f64 = abs.iter().map(|&x|(x/b_max).powf(e2)).sum();
                let sh = 1.0/den; // (B/B)^e2 / sum = 1/den
                print!("r{}={:.2}% ",rr,sh*100.0);
            }
            println!();
            nearB_log.push((p,nearB[2],m as usize,top1)); // nearB[2] = eps=0.10
            found+=1;
        }
        p+=n;
    }
    // summary trend
    println!("# === SUMMARY n={} : near-B(0.10) count, m, top1-share at saddle ===",n);
    for (p,nb,m,t1) in &nearB_log{
        println!("# p={:>13} near0.10B={:>4} m={:>9} frac={:.4} top1share={:.4e}",p,nb,m,*nb as f64/ *m as f64,t1);
    }
}
