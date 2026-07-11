// wf-A03 MECHANISM: WHY does K^NP(r) antitone hold while step-ratio fails?
// Claim: K(r) = (E_r/c_r)^{1/r} with c_r=(2r-1)!! n^r. K antitone <=> the sequence
//   t_r := log(E_r/c_r) is SUBADDITIVE-PER-INDEX: t_r/r decreasing <=> for all r,
//   t_{r+1}/(r+1) <= t_r/r. A SUFFICIENT condition: t_r is CONCAVE (t_{r+1}-t_r decreasing)
//   AND t_1 <= 0 ... no. Actually t_r/r decreasing <=> t is "star-shaped from 0 below":
//   need t convex? Let's just test: is t_r CONCAVE? is t_r/r decreasing? does a SINGLE
//   step-ratio bump (t locally convex) still leave t_r/r decreasing (geom-mean robust)?
//
// Also: the char-0 reference. char-0 E^(0)_r = (2r-1)!! n^r * g0(r) where g0(r) is the
//   Lam-Leung correction (g0(1)=1 exactly, g0 decreasing). For char-p: E^p_r = E^0_r + spur_r.
//   K^NP(r)^r = (E^0_r + spur_r)/c_r = g0(r) + spur_r/c_r. At beta=4 spur thins.
//   Question: is g0(r) + spur_r/c_r antitone-in-geom-mean even when spur injects a step bump?
use std::f64::consts::PI; use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
fn find_prime(n:u64,lo:u64,tv:Option<u32>)->Option<u64>{let mut p=lo-(lo%n)+1;if p<lo{p+=n}let mut t=0u64;while t<200_000_000{if p>2&&isp(p){match tv{Some(v)=>if v2(p-1)==v{return Some(p)},None=>return Some(p)}}p+=n;t+=1}None}
fn eval(n:u64,p:u64,rmax:usize,nth:usize)->Vec<f64>{
    let g=proot(p);let h=mpow(g,(p-1)/n,p);let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();let mu=Arc::new(mu);
    let m=(p-1)/n;let gn=mpow(g,n,p);let chunk=(m+nth as u64-1)/nth as u64;let mut hs=vec![];
    for t in 0..nth as u64{let lo=t*chunk;let hi=((t+1)*chunk).min(m);if lo>=hi{continue}let mu=Arc::clone(&mu);
        hs.push(thread::spawn(move||{let mut s=vec![0.0f64;rmax+1];let mut b=mpow(gn,lo,p);let pp=p as u128;let inv=2.0*PI/p as f64;let nf=n as f64;
            for _ in lo..hi{let mut re=0.0;for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64;re+=(inv*(tt as f64)).cos();}
                let e2=re*re;let mut pw=1.0;for r in 1..=rmax{pw*=e2;s[r]+=nf*pw;}b=((b as u128*gn as u128)%pp)as u64;}
            s}));}
    let mut ts=vec![0.0f64;rmax+1];for h in hs{let s=h.join().unwrap();for r in 1..=rmax{ts[r]+=s[r]}}
    for r in 1..=rmax{ts[r]/=p as f64} ts
}
fn report(label:&str,n:u64,p:u64,rmax:usize,nth:usize){
    let enp=eval(n,p,rmax,nth);let ln_n=(n as f64).ln();let lp=(p as f64).ln();
    let rdeep=((1.6*lp).round() as usize).min(rmax);
    // t_r = log(E_r) - log(c_r); g_r = exp(t_r) = E_r/c_r (the "g0(r)+spur/c_r" object); t_r/r = log K(r)
    let mut t=vec![0.0f64;rmax+1];
    for r in 1..=rmax{ if enp[r]>0.0{ t[r]= enp[r].ln() - (ldfact(r)+r as f64*ln_n); }}
    // diagnostics: is t concave? (t_{r+1}-t_r decreasing); is t_r/r decreasing? (K antitone)
    let mut d1=vec![0.0f64;rmax+1]; for r in 1..rmax{d1[r]=t[r+1]-t[r];}
    let mut concave=true; let mut cbreak=0;
    for r in 1..rdeep-1{ if d1[r+1]>d1[r]+1e-12{ if concave{cbreak=r;} concave=false;}}
    let mut star=true; let mut sbreak=0; // t_r/r decreasing
    for r in 1..rdeep{ if t[r+1]/(r as f64+1.0) > t[r]/(r as f64)+1e-13{ if star{sbreak=r;} star=false;}}
    println!("[{}] n={} p={} v2={} beta={:.3} rdeep={}",label,n,p,v2(p-1),lp/ln_n,rdeep);
    println!("   t_r=log(E_r/c_r): t_r CONCAVE(diff decr)={} {} | t_r/r DECREASING(=K antitone)={} {}",
        concave, if concave{"".into()}else{format!("(break r={})",cbreak)},
        star, if star{"".into()}else{format!("(break r={})",sbreak)});
    // the key: t_1 = log K(1) <= 0 at beta=4 generic (since K(1)=1-n/p<1). t_r <= t_1 * r ?? no.
    // The SUFFICIENT structural shape S1 needs: t_r <= t_1 + log((2r-1)!!/(2*1-1)!!) ... no, simpler:
    //   E_r <= E_1 * (2r-1)!! * n^{r-1}  <=> log E_r <= log E_1 + ldfact(r) + (r-1) log n
    //   <=> t_r + ldfact(r)+r logn <= t_1 + 0 + ldfact(r)+(r-1)logn + ... wait recompute:
    //   E_1 = c_1 * exp(t_1) = (1)*(n)*exp(t_1). target RHS = E_1*(2r-1)!!*n^{r-1}
    //     = n*exp(t_1)*(2r-1)!!*n^{r-1} = (2r-1)!!*n^r*exp(t_1) = c_r * exp(t_1).
    //   So target: E_r = c_r exp(t_r) <= c_r exp(t_1)  <=>  t_r <= t_1. THIS is exactly K(r)^r<=K(1)^r form? no:
    //   t_r<=t_1 means E_r/c_r <= E_1/c_1, i.e. the RATIO g_r=E_r/c_r decreasing, NOT K=g_r^{1/r}.
    //   That's STRONGER than K antitone. Check it:
    let mut g_decr=true; let mut gbreak=0;
    for r in 1..rdeep{ if t[r+1]>t[r]+1e-13{ if g_decr{gbreak=r;} g_decr=false;}}
    println!("   S1-EXACT needs E_r/c_r DECREASING (t_r<=t_1, stronger than K-antitone): {} {} | t_1={:.5} sup_r t_r@r<=rdeep={:.5}",
        g_decr, if g_decr{"".into()}else{format!("(break r={})",gbreak)}, t[1], {let mut s=f64::MIN;for r in 1..=rdeep{if t[r]>s{s=t[r];}} s});
    print!("   g_r=E_r/c_r:"); for r in 1..=8.min(rmax){print!(" g{}={:.4}",r,t[r].exp());} 
    if rdeep<=rmax{print!(" g{}={:.4}",rdeep,t[rdeep].exp());} println!();
    println!();
}
fn main(){
    let a:Vec<String>=std::env::args().collect();let nth:usize=if a.len()>1{a[1].parse().unwrap()}else{10};
    println!("=== wf-A03 MECHANISM: which monotonicity SHAPE holds? (E_r/c_r ratio-decr is what S1 brick literally needs) ===");
    report("B3-PRIME",32,1001153,40,nth);
    for (n,rmax) in vec![(16usize,42),(32,42),(64,40),(128,38),(256,36)] {
        let n=n as u64; let mu=(n as f64).log2() as u32; let lo=((n as f64).powf(4.0)) as u64;
        if let Some(p)=find_prime(n,lo,Some(mu)){report("STRUCT-b4",n,p,rmax,nth);}
        if let Some(p)=find_prime(n,lo,None){report("GENERIC-b4",n,p,rmax,nth);}
    }
}
