// wf-O1: OSV short-Weil curve-blend re-attack for the CONSTANT-C target.
// Findings to verify numerically at prize regime (beta~4, n=p^{1/4}):
//
//  Q1. Our f=bX is a SINGLE additive character over mu_n (OSV n=1 monomial case).
//      OSV Lemma 3.6 / Shkredov gives  M(n) <= min{ p^{1/2}, C * n^{1/2} p^{1/6} (log p)^{1/6} }.
//      The PRIZE target is M(n) <= C * sqrt(n log(p/n)).  Compare the two as ratios to prize.
//      => Does the Shkredov bound (the only OSV-stack bound touching tau=p^{1/4}) give C-const? NO if it has the p^{1/6}.
//
//  Q2. The OSV CURVE (Lemma 2.1: #{F=0} <= 4 d^{4/3} p^{2/3} + 3p) is used only for BINOMIAL
//      additive energy Q_3(m,n;G) (6 vars). For the linear/monomial case there is no curve.
//      Measure the actual moment-r additive count A_r = #{2r-tuples in mu_n summing to 0 mod p}
//      = q * E_r' + principal, vs the OSV per-coset curve-count bound, vs char-0 (2r-1)!! n^r.
//      Key: does the curve-count bound 4 d^{4/3} p^{2/3} BEAT char-0 at r=3 (the OSV 6-var level)?
//
//  Q3. The blended bound:  M_bound = (q * E_r')^{1/(2r)} at optimal r ~ ln q.  Does adding the
//      curve point-count CAP on E_r (per-coset) lower M_bound/prize below the moment-only plateau?
//
// All exact mod-p counts; re-run at increasing n to flag small-n artifacts.
use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}

// exact additive energy A_r = #{ (x_1..x_2r) in mu_n^{2r} : sum x_i = 0 mod p }
// via meet-in-the-middle on r-fold sumset distributions
fn additive_count(mu:&[u64],r:usize,p:u64)->u128{
    let mut d:HashMap<u64,u128>=HashMap::new(); d.insert(0,1);
    for _ in 0..r { let mut nd:HashMap<u64,u128>=HashMap::new();
        for(&s,&c)in &d{for &x in mu{let t=((s as u128+x as u128)%p as u128)as u64;*nd.entry(t).or_insert(0)+=c;}} d=nd; }
    let mut t:u128=0; for(&s,&c)in &d{let ns=(p-s)%p; if let Some(&c2)=d.get(&ns){t+=c*c2;}} t
}

fn main(){
    println!("=== Q1: Shkredov/OSV monomial bound vs PRIZE (the only OSV bound touching tau=p^(1/4)) ===");
    println!("  n     p        beta   prize=sqrt(n ln(p/n))  Shk=n^.5 p^(1/6)(lnp)^(1/6)   Shk/prize   p^.5/prize");
    for &(n,lo) in &[(16u64,60000u64),(32,1000000),(64,16000000),(256,4_000_000_000u64),(1024,1_000_000_000_000u64)]{
        let p=fp(n,lo);
        let beta=(p as f64).ln()/(n as f64).ln();
        let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
        let shk=(n as f64).sqrt()*(p as f64).powf(1.0/6.0)*((p as f64).ln()).powf(1.0/6.0);
        let triv=(p as f64).sqrt();
        println!("  {:5} {:14} {:.3}  {:14.2}        {:18.2}   {:8.3}   {:8.3}", n,p,beta,prize,shk,shk/prize,triv/prize);
    }
    // project to prize scale n=2^30, beta=4 => p=2^120
    {
        let n=2f64.powi(30); let p=2f64.powi(120);
        let prize=(n*( (p/n).ln() )).sqrt();
        let shk=n.sqrt()*p.powf(1.0/6.0)*(p.ln()).powf(1.0/6.0);
        println!("  PRIZE n=2^30 p=2^120: prize={:.3e}  Shk={:.3e}  Shk/prize={:.3e}  (=> Shkredov USELESS at beta=4)", prize, shk, shk/prize);
    }

    println!("\n=== Q2: per-coset OSV curve-count bound vs actual additive count A_r vs char-0 ===");
    println!("   (A_r counts 2r-tuples summing to 0 mod p; char0=(2r-1)!! n^r ; curve bound = 4 (rn)^(4/3) p^(2/3)+3p heuristic) ===");
    for &(n,lo) in &[(16u64,60000u64),(32,1000000),(64,16000000)]{
        let p=fp(n,lo);
        let g=proot(p);let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        println!("  -- n={} p={} --", n,p);
        println!("    r    A_r(exact)      char0=(2r-1)!!n^r   A_r/char0   OSVcurve(4(rn)^4/3 p^2/3+3p)  curve/char0");
        for r in 1..=6usize {
            let ar=additive_count(&mu,r,p);
            let c0=(dfact(r)*(n as f64).powi(r as i32)) as f64;
            let dd=(r as f64*n as f64); // degree proxy of diagonal system
            let curve=4.0*dd.powf(4.0/3.0)*(p as f64).powf(2.0/3.0)+3.0*(p as f64);
            println!("    {:2}  {:15}  {:18.0}   {:8.4}   {:24.0}   {:8.2}", r, ar, c0, ar as f64/c0, curve, curve/c0);
        }
    }

    println!("\n=== Q3: blended M_bound: min(moment-r , curve-capped) , ratio to prize ===");
    println!("   curve cap on E_r' per coset: replace A_r by min(A_r_actual, char0) -- already <=char0 measured. ===");
    println!("   So the curve adds NOTHING beyond char0 when A_r<=char0 already holds. Report M_bound from actual A_r.");
    for &(n,lo,rmax) in &[(16u64,60000u64,16usize),(32,1000000,18),(64,16000000,20)]{
        let p=fp(n,lo);
        let g=proot(p);let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let prize=((n as f64)*((p as f64/n as f64).ln())).sqrt();
        let mut best=f64::INFINITY; let mut bestr=0;
        for r in 1..=rmax {
            let ar=additive_count(&mu,r,p) as f64; // = q*E_r (all cosets incl principal n^{2r})
            // subtract principal contribution n^{2r} (the b=0 coset's full weight appears once as the all-equal? no:
            // A_r = q*E_r where E_r=(1/q)sum_b eta_b^{2r}. principal eta_0=n contributes n^{2r}. nonprincipal sum:
            let er_nonpr = ar - (n as f64).powi(2*r as i32);
            // M_bound on max_{b!=0} = (sum_{b!=0} eta_b^{2r})^{1/2r} = er_nonpr^{1/2r}
            let mb = er_nonpr.max(1.0).powf(1.0/(2.0*r as f64));
            let ratio=mb/prize;
            if ratio<best{best=ratio;bestr=r;}
        }
        println!("  n={:3} p={}: best M_bound/prize = {:.4} at r={}", n,p,best,bestr);
    }
}
