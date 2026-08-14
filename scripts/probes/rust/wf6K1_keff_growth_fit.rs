// wf-K1 DECISIVE: extrapolate K_eff(n) and M_bound/prize at optimal depth to large n.
// E_r' = (1/p) sum_{b!=0} eta_b^{2r}, eta_b = sum_{x in mu_n} cos(2 pi b x / p), over all m=(p-1)/n cosets.
// K_eff(n) = max_r (E_r'/[(2r-1)!! n^r])^{1/r}  (PEAK, the absolute constant the prize needs bounded).
// M_bound/prize = min_r (q E_r')^{1/2r} / sqrt(n log(p/n)).
// Reports BOTH peak K_eff (interior) and min M/prize, for several primes per n, and varying beta.
// usage: wf6K1 <n> <nthreads> <rmax> [beta]   (beta default 4; primes: first few >= n^beta)
use std::f64::consts::PI;
use std::thread;
use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}if n%3==0{return n==3}let mut d=5;while d*d<=n{if n%d==0{return false}if n%(d+2)==0{return false}d+=6}true}
// k-th prime p == 1 mod n with p >= lo
fn primes(n:u64,lo:u64,k:usize)->Vec<u64>{
    let mut out=vec![]; let mut p=lo+((1+n-lo%n)%n); if p<=2{p+=n}
    loop{ if p>2 && p%n==1 && isp(p){out.push(p); if out.len()>=k{break;}} p+=n; }
    out
}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v} // ln (2r-1)!!
fn run(n:u64,p:u64,rmax:usize,nthreads:usize)->(f64,usize,f64,usize,f64){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mu=Arc::new(mu);
    let chunk=(m+nthreads as u64-1)/nthreads as u64;
    let mut handles=vec![];
    for t in 0..nthreads as u64 {
        let lo=t*chunk; let hi=((t+1)*chunk).min(m); if lo>=hi{continue;}
        let mu=Arc::clone(&mu);
        handles.push(thread::spawn(move||{
            let mut s=vec![0.0f64;rmax+1];
            let mut b=mpow(gn,lo,p); let pp=p as u128; let inv=2.0*PI/p as f64;
            for _ in lo..hi {
                let mut re=0.0;
                for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64; re+=(inv*(tt as f64)).cos();}
                let e2=re*re; let mut pw=1.0;
                for r in 1..=rmax{pw*=e2; s[r]+=pw;}
                b=((b as u128*gn as u128)%pp)as u64;
            }
            s
        }));
    }
    let mut tot=vec![0.0f64;rmax+1];
    for h in handles{let s=h.join().unwrap();for r in 1..=rmax{tot[r]+=s[r];}}
    let lp=(p as f64).ln(); let ln_n=(n as f64).ln();
    let prize=((n as f64)*(lp-ln_n)).sqrt();
    // peak K_eff (use log-space to avoid overflow): ln E_r = ln(tot[r]) - lp
    let mut peak_keff=0.0f64; let mut peak_r=0;
    let mut min_mr=f64::INFINITY; let mut argmin_r=0;
    for r in 1..=rmax {
        let ln_er = tot[r].ln() - lp;
        let ln_c0 = ldfact(r) + r as f64*ln_n;
        let keff = ((ln_er-ln_c0)/r as f64).exp();
        if keff>peak_keff{peak_keff=keff; peak_r=r;}
        // M_bound = (p * E_r)^{1/2r}; ln = (lp + ln_er)/(2r)
        let mbound = ((lp+ln_er)/(2.0*r as f64)).exp();
        let mr = mbound/prize;
        if mr<min_mr{min_mr=mr; argmin_r=r;}
    }
    (peak_keff,peak_r,min_mr,argmin_r,prize)
}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:u64=a[1].parse().unwrap();
    let nth:usize=if a.len()>2{a[2].parse().unwrap()}else{8};
    let rmax:usize=if a.len()>3{a[3].parse().unwrap()}else{40};
    let beta:f64=if a.len()>4{a[4].parse().unwrap()}else{4.0};
    let lo=((n as f64).powf(beta)) as u64;
    let ps=primes(n,lo,3);
    println!("### n={} beta={} rmax={} (3 primes) ###",n,beta,rmax);
    let mut pk=vec![]; let mut mr=vec![];
    for &p in &ps {
        let m=(p-1)/n;
        let (peak,pr,minmr,ar,prize)=run(n,p,rmax,nth);
        let realbeta=(p as f64).ln()/(n as f64).ln();
        println!("  p={} m={} beta_real={:.3} lnq={:.2} prize={:.3} | peak_K_eff={:.4}@r={} | min(M/prize)={:.4}@r={}",
            p,m,realbeta,(p as f64).ln(),prize,peak,pr,minmr,ar);
        pk.push(peak); mr.push(minmr);
    }
    let am=|v:&Vec<f64>| v.iter().sum::<f64>()/v.len() as f64;
    println!("  >>> n={} avg peak_K_eff={:.4}  avg min(M/prize)={:.4}",n,am(&pk),am(&mr));
}
