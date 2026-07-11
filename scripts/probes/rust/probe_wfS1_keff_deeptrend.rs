// wf-S1 DECISIVE: per-r trend of the NONPRINCIPAL energy constant K_eff^NP(n,r) = (E_np_r/char0_r)^{1/r}
// and the DC-INCLUDED full constant, at the worst structured primes incl Fermat, to depth r~1.6 ln q.
//
// E_np_r = (1/p) sum_{b!=0} eta_b^{2r}, eta_b=sum_{x in mu_n} e_p(bx) (real; mu_n neg-closed). b ranges
//   over NONZERO residues => b=0 DC term (eta_0=n) excluded => this IS the nonprincipal additive energy
//   A_r - n^{2r}/p (verified identity, wf6P2). char0_r = (2r-1)!! n^r (Lam-Leung Wick anchor).
// DC-INCLUDED full E_r = E_np_r + n^{2r}/p ; its constant ((E_np+n^{2r}/p)/char0)^{1/r} shows the trivial
//   b=0 blowup (n^{2r}/p = n^{2r-4} at beta=4) for contrast -- NOT the prize-relevant object.
// M = max_{b!=0}|eta_b| (the actual Gaussian-period sup that bounds the prize). prize=sqrt(n*ln(p/n)).
//
// VERDICT: print full K_eff^NP(r) ladder. BOUNDED & flat in n => TRANSFER-HOLDS-WITH-SLACK (report sup K).
// GROWS in n or r => TRANSFER-FALSE (report witness).
// usage: probe <nthreads>
use std::f64::consts::PI; use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
fn find_prime(n:u64,lo:u64,tv:Option<u32>)->Option<u64>{let mut p=lo-(lo%n)+1;if p<lo{p+=n}let mut t=0u64;while t<80_000_000{if p>2&&isp(p){match tv{Some(v)=>if v2(p-1)==v{return Some(p)},None=>return Some(p)}}p+=n;t+=1}None}
fn eval(n:u64,p:u64,rmax:usize,nth:usize)->(Vec<f64>,f64){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();let mu=Arc::new(mu);
    let m=(p-1)/n;let gn=mpow(g,n,p);let chunk=(m+nth as u64-1)/nth as u64;let mut hs=vec![];
    for t in 0..nth as u64{let lo=t*chunk;let hi=((t+1)*chunk).min(m);if lo>=hi{continue}let mu=Arc::clone(&mu);
        hs.push(thread::spawn(move||{let mut s=vec![0.0f64;rmax+1];let mut mm=0.0f64;let mut b=mpow(gn,lo,p);let pp=p as u128;let inv=2.0*PI/p as f64;let nf=n as f64;
            for _ in lo..hi{let mut re=0.0;for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64;re+=(inv*(tt as f64)).cos();}
                let e2=re*re;let mut pw=1.0;for r in 1..=rmax{pw*=e2;s[r]+=nf*pw;}let ar=re.abs();if ar>mm{mm=ar}b=((b as u128*gn as u128)%pp)as u64;}
            (s,mm)}));}
    let mut ts=vec![0.0f64;rmax+1];let mut mm=0.0f64;for h in hs{let(s,m2)=h.join().unwrap();for r in 1..=rmax{ts[r]+=s[r]}if m2>mm{mm=m2}}
    for r in 1..=rmax{ts[r]/=p as f64}(ts,mm)}
fn report(label:&str,n:u64,p:u64,rmax:usize,nth:usize){
    let(enp,mnp)=eval(n,p,rmax,nth);let ln_n=(n as f64).ln();let lp=(p as f64).ln();let prize=((n as f64)*(lp-ln_n)).sqrt();
    let rdeep=((1.6*lp).round() as usize).min(rmax);
    let mut supk=0.0f64;let mut supk_r=0;
    println!("[{}] n={} p={} v2={} beta={:.2} lnq={:.1} rdeep~1.6lnq={} M/prize={:.4}",label,n,p,v2(p-1),lp/ln_n,lp,rdeep,mnp/prize);
    print!("   K_eff^NP(r):");
    for r in 1..=rmax{ if enp[r]>0.0{let lc0=ldfact(r)+r as f64*ln_n;let k=((enp[r].ln()-lc0)/r as f64).exp();
        if k>supk{supk=k;supk_r=r;} if r<=6||r==rdeep||r%5==0||r==rmax{print!(" r{}={:.3}",r,k);} } }
    println!();
    // DC-included constant at rdeep for contrast (the trivial b=0 blowup)
    let dc=(n as f64).powf(2.0*rdeep as f64)/p as f64; let lc0d=ldfact(rdeep)+rdeep as f64*ln_n;
    let kfull=(((enp[rdeep]+dc).ln()-lc0d)/rdeep as f64).exp();
    println!("   => SUP K_eff^NP = {:.4} @r={}  |  DC-included K_full@rdeep={:.4} (trivial b=0 term)",supk,supk_r,kfull);
}
fn main(){
    let a:Vec<String>=std::env::args().collect();let nth:usize=if a.len()>1{a[1].parse().unwrap()}else{8};
    println!("=== wf-S1 deep K_eff^NP trend: does the NONPRINCIPAL energy constant stay BOUNDED? (worst structured + Fermat) ===");
    // Fermat n=16 (p=65537, the classic structured) ; structured v2=mu at each n; generic.
    println!("-- Fermat / classic structured small primes --");
    report("FERMAT16",16,65537,42,nth);
    report("FERMAT32",32,65537*0+65537, 0+42, nth); // 65537-1=65536=2^16, mu_32 subgroup exists; reuse Fermat
    println!();
    println!("-- prize-scale beta~4, structured (v2=mu, tightest) vs generic --");
    for (n,rmax) in vec![(16usize,42),(32,42),(64,40),(128,38),(256,38)] {
        let n=n as u64; let mu=(n as f64).log2() as u32; let lo=((n as f64).powf(4.0)) as u64;
        if let Some(p)=find_prime(n,lo,Some(mu)){report("STRUCT",n,p,rmax,nth);}
        if let Some(p)=find_prime(n,lo,None){report("GENERIC",n,p,rmax,nth);}
        println!();
    }
}
