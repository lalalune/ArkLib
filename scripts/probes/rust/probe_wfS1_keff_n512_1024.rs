// wf-S1 DECISIVE EXTENSION: K_eff^NP(n,r) at n=512,1024 (prize regime beta=4), good+hi-v2+rough primes,
// depth r up to ~1.4 ln q. Does the NONPRINCIPAL energy constant K_eff^NP=(E_np_r/[(2r-1)!! n^r])^{1/r}
// stay BOUNDED (transfer holds => prize via prize_of_transfer_slack) or finally GROW?
//
// E_np_r = (1/p) sum_{b!=0} eta_b^{2r},  eta_b = sum_{x in mu_n} e_p(bx)  (real; mu_n neg-closed).
// char0_r = (2r-1)!! n^r  (Lam-Leung Wick anchor).
//
// EXACT ANCHOR (provable, n-independent): K_eff^NP(1) = E_np_1/n = (n - n^2/p)/n = 1 - n/p -> 1^-.
//   So sup_r K_eff^NP is pinned <=1 iff the ladder is r-decreasing (observed n<=256). We test n=512,1024.
//
// n=512: FULL enumeration of all m=(p-1)/n cosets (~1.3e8 cosets x 512 = 6.9e10 cos ops) -- multithreaded.
// n=1024: MONTE-CARLO sampling of B random b in F_p^* (unbiased estimator of E_np_r) + n=512 MC cross-check
//   to validate the estimator vs the n=512 exact run.
//
// usage: probe <nthreads> <mode>   mode in {exact512, mc1024, mc512check, all}
use std::f64::consts::PI; use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3u64;while (d as u128)*(d as u128)<=n as u128{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn lpf(mut x:u64)->u64{let mut l=1u64;let mut d=2u64;while (d as u128)*(d as u128)<=x as u128{while x%d==0{l=d;x/=d}d+=1}if x>1{l=x}l}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while (d as u128)*(d as u128)<=m as u128{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2u64;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
// find smallest prime p = 1 mod n with p >= lo and (optionally) prescribed v2(p-1) or rough condition.
// cond: 0=any, 1=v2>=target, 2=rough (lpf((p-1)/n) > (p-1)/n/divp)
fn find(n:u64,lo:u64,cond:u32,tv:u32,divp:u64)->Option<u64>{
    let mut p=lo-(lo%n)+1; if p<lo{p+=n}
    let mut t=0u64;
    while t<200_000_000{
        if p>2&&p%n==1&&isp(p){
            match cond{0=>return Some(p),
                1=>if v2(p-1)>=tv{return Some(p)},
                2=>{let m=(p-1)/n; if lpf(m)>m/divp{return Some(p)}},
                _=>return Some(p)}
        }
        p+=n; t+=1;
    }
    None
}
// EXACT: full enumeration of all cosets, multithreaded. returns (E_np[1..=rmax], M=max|eta_b|)
fn eval_exact(n:u64,p:u64,rmax:usize,nth:usize)->(Vec<f64>,f64){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();let mu=Arc::new(mu);
    let m=(p-1)/n;let gn=mpow(g,n,p);let chunk=(m+nth as u64-1)/nth as u64;let mut hs=vec![];
    for t in 0..nth as u64{let lo=t*chunk;let hi=((t+1)*chunk).min(m);if lo>=hi{continue}let mu=Arc::clone(&mu);
        hs.push(thread::spawn(move||{let mut s=vec![0.0f64;rmax+1];let mut mm=0.0f64;let mut b=mpow(gn,lo,p);let pp=p as u128;let inv=2.0*PI/p as f64;
            for _ in lo..hi{let mut re=0.0;for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64;re+=(inv*(tt as f64)).cos();}
                let e2=re*re;let mut pw=1.0;for r in 1..=rmax{pw*=e2;s[r]+=pw;}let ar=re.abs();if ar>mm{mm=ar}b=((b as u128*gn as u128)%pp)as u64;}
            (s,mm)}));}
    let mut ts=vec![0.0f64;rmax+1];let mut mm=0.0f64;for h in hs{let(s,m2)=h.join().unwrap();for r in 1..=rmax{ts[r]+=s[r]}if m2>mm{mm=m2}}
    for r in 1..=rmax{ts[r]/=p as f64}(ts,mm)
}
// MONTE-CARLO: sample B random nonzero b, estimate E_np_r = (1/p) sum_{b!=0} eta_b^{2r}
//   = ((p-1)/p) * E_{b~Unif(F_p^*)}[ eta_b^{2r} ]. Unbiased; report estimate + (for sup-tracking) max|eta|.
// We use a multiplicative walk b *= gstep to get pseudo-random-but-coprime coverage, plus an LCG offset.
fn eval_mc(n:u64,p:u64,rmax:usize,nth:usize,b_per_thread:u64,seed0:u64)->(Vec<f64>,f64,u64){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();let mu=Arc::new(mu);
    let mut hs=vec![];
    for t in 0..nth as u64{let mu=Arc::clone(&mu);let seed=seed0.wrapping_add(t.wrapping_mul(0x9E3779B97F4A7C15));
        hs.push(thread::spawn(move||{
            let mut s=vec![0.0f64;rmax+1];let mut mm=0.0f64;let pp=p as u128;let inv=2.0*PI/p as f64;
            let mut st=seed|1;
            for _ in 0..b_per_thread{
                // xorshift64 -> b in [1,p-1]
                st^=st<<13; st^=st>>7; st^=st<<17;
                let b=1+(st%(p-1));
                let mut re=0.0;for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64;re+=(inv*(tt as f64)).cos();}
                let e2=re*re;let mut pw=1.0;for r in 1..=rmax{pw*=e2;s[r]+=pw;}let ar=re.abs();if ar>mm{mm=ar}
            }
            (s,mm)}));}
    let mut ts=vec![0.0f64;rmax+1];let mut mm=0.0f64;let total=b_per_thread*nth as u64;
    for hh in hs{let(s,m2)=hh.join().unwrap();for r in 1..=rmax{ts[r]+=s[r]}if m2>mm{mm=m2}}
    // E_np_r ~ ((p-1)/p) * (sum / total)  (mean over nonzero b, scaled by (p-1)/p)
    let scale=((p-1) as f64)/(p as f64)/(total as f64);
    for r in 1..=rmax{ts[r]*=scale}
    (ts,mm,total)
}
fn ladder(label:&str,n:u64,p:u64,enp:&[f64],m_eta:f64,rmax:usize,extra:&str){
    let ln_n=(n as f64).ln();let lp=(p as f64).ln();let prize=((n as f64)*(lp-ln_n)).sqrt();
    let rdeep=((1.4*lp).round() as usize).min(rmax);
    let mut supk=0.0f64;let mut supk_r=0;
    println!("[{}] n={} p={} v2={} lpf((p-1)/n)={} beta={:.3} lnq={:.1} rdeep~1.4lnq={} M/prize={:.4} {}",
        label,n,p,v2(p-1),lpf((p-1)/n),lp/ln_n,lp,rdeep,m_eta/prize,extra);
    print!("   K_eff^NP(r):");
    for r in 1..=rmax{ if enp[r]>0.0{let lc0=ldfact(r)+r as f64*ln_n;let k=((enp[r].ln()-lc0)/r as f64).exp();
        if k>supk{supk=k;supk_r=r;} if r<=6||r==rdeep||r%5==0||r==rmax{print!(" r{}={:.4}",r,k);} } }
    println!();
    println!("   => SUP K_eff^NP = {:.5} @r={}   (anchor K(1)=1-n/p={:.6})",supk,supk_r,1.0-(n as f64)/(p as f64));
}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let nth:usize=if a.len()>1{a[1].parse().unwrap()}else{8};
    let mode:&str=if a.len()>2{&a[2]}else{"all"};
    println!("=== wf-S1 DECISIVE: K_eff^NP at n=512,1024 (beta=4) — does the transfer constant stay BOUNDED (<=1)? ===");
    let rmax=40usize;

    if mode=="mc512check"||mode=="all"{
        // n=512 cross-check: MC estimate vs exact (run exact below). small B for speed.
        let lo=512u64*512*512*512; // n^4
        if let Some(p)=find(512,lo,0,0,0){
            println!("-- n=512 MC cross-check (validate estimator) --");
            let(enp,m,tot)=eval_mc(512,p,rmax,nth, 200_000, 0xABCDEF);
            ladder("MC512chk",512,p,&enp,m,rmax,&format!("[MC B={}]",tot));
        }
    }

    if mode=="exact512"||mode=="all"{
        println!("-- n=512, beta=4, EXACT full enumeration: good / hi-v2 / rough --");
        let lo=512u64*512*512*512;
        if let Some(p)=find(512,lo,0,0,0){let(e,m)=eval_exact(512,p,rmax,nth);ladder("EXACT512-good",512,p,&e,m,rmax,"");}
        if let Some(p)=find(512,lo,1,16,0){let(e,m)=eval_exact(512,p,rmax,nth);ladder("EXACT512-hiv2",512,p,&e,m,rmax,"");}
        if let Some(p)=find(512,lo,2,0,3){let(e,m)=eval_exact(512,p,rmax,nth);ladder("EXACT512-rough",512,p,&e,m,rmax,"");}
    }

    if mode=="mc1024"||mode=="all"{
        println!("-- n=1024, beta=4, MONTE-CARLO (B ~ 1.6M random b): good / hi-v2 / rough --");
        let lo=1024u64*1024*1024*1024; // n^4 ~ 1.1e12
        let bpt=200_000u64;
        if let Some(p)=find(1024,lo,0,0,0){let(e,m,t)=eval_mc(1024,p,rmax,nth,bpt,0x111);ladder("MC1024-good",1024,p,&e,m,rmax,&format!("[MC B={}]",t));}
        if let Some(p)=find(1024,lo,1,16,0){let(e,m,t)=eval_mc(1024,p,rmax,nth,bpt,0x222);ladder("MC1024-hiv2",1024,p,&e,m,rmax,&format!("[MC B={}]",t));}
        if let Some(p)=find(1024,lo,2,0,3){let(e,m,t)=eval_mc(1024,p,rmax,nth,bpt,0x333);ladder("MC1024-rough",1024,p,&e,m,rmax,&format!("[MC B={}]",t));}
    }
}
