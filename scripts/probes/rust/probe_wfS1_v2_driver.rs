// wf-S1 the REAL inflation driver: sweep v2(p-1) at fixed n, beta~4, watch SUP_r K_eff^NP.
// FERMAT32 (n=32,p=65537,v2=16) gave K=2.28; structured v2=mu gave K=1.0. Hypothesis: HIGH v2(p-1)
// (2-power-smooth p-1, mu_n deep inside a 2^k cyclic group) drives the nonprincipal energy inflation.
// This is the genuine BGK structured-prime witness. Q: at prize scale p~n^4 with p-1 = n^30-style,
// can v2 even BE large?  v2(p-1) <= log2(p-1) ~ beta*mu. So at n=2^mu, beta=4, max v2 = ~4mu.
// We find primes p~n^4 with v2(p-1) = mu, mu+2, 2mu, 3mu, ~4mu and report K_eff^NP.
// usage: probe <n> <nthreads>
use std::f64::consts::PI; use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
// find prime p in [lo,hi] with exactly v2(p-1)=tv: p = 2^tv * odd + 1, odd ranges, scan.
fn find_prime_v2(tv:u32, lo:u64, hi:u64)->Option<u64>{
    let step=1u64<<tv; let mut k=(lo/step).max(1); // p=step*k+1, need k odd for exact v2
    if k%2==0{k+=1}
    loop{ let p=step*k+1; if p>hi{return None} if isp(p) && v2(p-1)==tv {return Some(p);} k+=2; }
}
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
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:u64=if a.len()>1{a[1].parse().unwrap()}else{32};
    let nth:usize=if a.len()>2{a[2].parse().unwrap()}else{8};
    let mu=(n as f64).log2() as u32; let ln_n=(n as f64).ln(); let rmax=30usize;
    let lo=((n as f64).powf(3.9)) as u64; let hi=((n as f64).powf(4.3)) as u64;
    println!("=== wf-S1 v2(p-1) driver, n={} (mu={}), p~n^4 in [{},{}], rmax={} ===",n,mu,lo,hi,rmax);
    println!("v2(p-1) sweep: does deeper 2-adic valuation of p-1 inflate the NONPRINCIPAL energy constant?");
    let maxv = (4*mu).min(50); // up to ~beta*mu
    let mut tv=mu;
    while tv<=maxv {
        if let Some(p)=find_prime_v2(tv,lo,hi){
            let(enp,mnp)=eval(n,p,rmax,nth);let lp=(p as f64).ln();let prize=((n as f64)*(lp-ln_n)).sqrt();
            let mut supk=0.0f64;let mut supr=0;for r in 1..=rmax{if enp[r]>0.0{let k=((enp[r].ln()-(ldfact(r)+r as f64*ln_n))/r as f64).exp();if k>supk{supk=k;supr=r}}}
            println!("  v2={:>2} p={} beta={:.3} | SUP K_eff^NP={:.4}@r={} | M/prize={:.4}",tv,p,lp/ln_n,supk,supr,mnp/prize);
        } else { println!("  v2={:>2}: no prime in window",tv); }
        tv += if tv<mu+4 {1} else {2};
    }
}
