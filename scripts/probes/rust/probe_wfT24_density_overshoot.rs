// probe_wfT24_density_overshoot.rs
// FOCUSED REFUTATION of T24's claimed affine Sarnak-Xue DENSITY bound
//      #{b!=0 : |eta_b| >= n^{1/2+s}} <= p^{1-2s+o(1)}   (claim)
// and its sharp log-refined form
//      #{b!=0 : |eta_b| >= t*sqrt(n)} <= m * e^{-(1-o(1)) t^2}   (claim, m=(p-1)/n).
//
// We test BOTH at prize-faithful beta=4 (p~n^4 exact) for the cleanest cells, with the FULL
// p-1 nonzero-frequency count (graph mult n per coset).  If the empirical count EXCEEDS the
// claimed bound by a growing margin, the density bound is FALSE -> the conjecture is REFUTED.
//
// The sharp-form test is the decisive one: a TRUE Sarnak-Xue/Gaussian density e^{-t^2} would
// force the largest t (= M/sqrt(n)) to satisfy m*e^{-t_max^2} >= 1, i.e. t_max <= sqrt(log m).
// We check whether t_max = M/sqrt(n) vs sqrt(log m): the claim PREDICTS M <= sqrt(n log m) ~ BGK.
// But the deeper question: is the COUNT at fixed t actually <= m e^{-t^2}, or is it LARGER
// (heavier-than-Gaussian tail in the bulk count = the BGK content the conservation law hides)?
//
// build: rustc -O probe_wfT24_density_overshoot.rs -o /tmp/wfT24o && /tmp/wfT24o
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128 % p as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn find_p(n:u64,beta:f64)->u64{let t=(n as f64).powf(beta) as u64;let mut p=(t/n+1)*n+1;loop{if is_prime(p)&&(p-1)%n==0&&(p-1)/n>1{return p;}p+=n;}}
fn main(){
    println!("{}","=".repeat(82));
    println!("T24 DENSITY-OVERSHOOT refutation: empirical #{{|eta|>=...}} vs claimed p^(1-2s) & m e^(-t^2)");
    println!("{}","=".repeat(82));
    for (n,beta) in [(8u64,4.0f64),(16,4.0),(32,4.0)] {
        let p=find_p(n,beta); let m=(p-1)/n;
        if (p as u128)*(n as u128)>120_000_000u128 {println!("\n n={} p={} skip",n,p);continue;}
        let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let gn=mpow(g,n,p);
        let mut mags=Vec::with_capacity(m as usize); let mut b=1u64;
        for _ in 0..m {
            let mut re=0.0; let mut im=0.0;
            for &x in &mu { let t=((b as u128*x as u128)%p as u128) as u64; let a=2.0*PI*(t as f64)/(p as f64); re+=a.cos(); im+=a.sin(); }
            mags.push(((re*re+im*im) as f64).sqrt());
            b=(b as u128*gn as u128 %p as u128) as u64;
        }
        mags.sort_by(|a,c|c.partial_cmp(a).unwrap());
        let mm=mags[0]; let sqn=(n as f64).sqrt();
        let tmax=mm/sqn; let sqlogm=(m as f64).ln().sqrt();
        println!("\n--- n={} p={} (beta={:.3}) m={} ---",n,p,(n as f64).ln()/(p as f64).ln(),m);
        println!("  M/sqrt(n)=t_max={:.4}  sqrt(log m)={:.4}  (claim predicts t_max<=sqrt(log m)): {}",
                 tmax, sqlogm, if tmax<=sqlogm {"holds"} else {"VIOLATED"});
        // (A) power-density claim  N(s) <= p^{1-2s}
        println!("  (A) POWER DENSITY  N(s)=#{{all p-1 freqs}}  vs  p^(1-2s):");
        println!("      s   | N(s)        | p^(1-2s)    | ratio N/p^(1-2s) | emp_exp | claim 1-2s | OVER?");
        let mut max_over=0.0f64;
        for k in 0..=12 {
            let s=0.025*k as f64;
            let thr=(n as f64).powf(0.5+s);
            let cnt=(mags.iter().filter(|&&v|v>=thr).count() as u64).saturating_mul(n);
            let claim=(p as f64).powf(1.0-2.0*s);
            let ratio=if claim>0.0 {cnt as f64/claim} else {f64::INFINITY};
            let emp=if cnt>0 {(cnt as f64).ln()/(p as f64).ln()} else {f64::NEG_INFINITY};
            let over = emp-(1.0-2.0*s);
            if cnt>0 && over>max_over {max_over=over;}
            println!("      {:.3} | {:11} | {:11.1} | {:15.3} | {:7.4} | {:9.4} | {}",
                     s,cnt,claim,ratio,emp,1.0-2.0*s, if over>0.0 {"YES"} else {"no"});
        }
        println!("      => MAX exponent overshoot (emp - (1-2s)) = {:.4}  [>0 => power-density claim FALSE]",max_over);
        // (B) sharp log-refined Gaussian density  N_t <= m e^{-t^2}
        println!("  (B) SHARP GAUSSIAN  N_t=#{{coset:|eta|>=t sqrt n}} vs m*e^(-t^2)  (per-coset count, m total):");
        println!("      t    | N_t(coset) | m*e^(-t^2)  | ratio | log-ratio per t^2");
        let mut max_logratio=f64::NEG_INFINITY;
        for k in 4..=((tmax*4.0) as i64) {
            let t=0.25*k as f64;
            if t>tmax+0.3 {break;}
            let nt=mags.iter().filter(|&&v|v>=t*sqn).count();
            let gauss=(m as f64)*(-(t*t)).exp();
            let ratio=if gauss>0.0 {nt as f64/gauss} else {f64::INFINITY};
            // effective tail constant c_eff in N_t ~ m e^{-c_eff t^2}: c_eff = -ln(N_t/m)/t^2
            let ceff = if nt>0 { -((nt as f64/m as f64).ln())/(t*t) } else {f64::INFINITY};
            if nt>0 && ratio>1.0 { let lr=ratio.ln(); if lr>max_logratio{max_logratio=lr;} }
            println!("      {:.2} | {:10} | {:11.3} | {:8.3} | c_eff={:.4} (claim c=1)",t,nt,gauss,ratio,ceff);
        }
        println!("      => if c_eff<1 in the bulk, tail is HEAVIER than Gaussian e^(-t^2) (the BGK excess)");
    }
    println!("\n{}","=".repeat(82));
    println!("READ: claim says N(s)<=p^(1-2s) and N_t<=m e^(-t^2).  If empirical exponent OVERSHOOTS");
    println!("1-2s and c_eff<1 in the bulk, the affine-density bound is provably FALSE at beta=4 ->");
    println!("REFUTED.  (And M/sqrt(n)=t_max GROWS with n, not bounded by a fixed Sarnak-Xue edge.)");
    println!("{}","=".repeat(82));
}
