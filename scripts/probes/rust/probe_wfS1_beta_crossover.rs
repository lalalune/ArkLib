// wf-S1 transfer THRESHOLD in beta: hold n fixed, sweep p~n^beta (worst structured v2=mu prime),
// watch SUP_r K_eff^NP cross from >1 (TRANSFER-FALSE: structured-prime energy inflation) down to <=1
// (TRANSFER-HOLDS-WITH-SLACK). Pins where the BGK wall actually sits vs the prize regime (beta=4).
// K_eff^NP(r) = ((1/p) sum_{b!=0} eta_b^{2r} / ((2r-1)!! n^r))^{1/r}, eta_b=sum_{x in mu_n} cos(2pi bx/p).
// usage: probe <n> <nthreads>
use std::f64::consts::PI; use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{x>>=1;v+=1}v}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
fn find_prime(n:u64,lo:u64,tv:u32)->Option<u64>{let mut p=lo-(lo%n)+1;if p<lo{p+=n}let mut t=0u64;while t<200_000_000{if p>2&&isp(p)&&v2(p-1)==tv{return Some(p)}p+=n;t+=1}None}
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
    println!("=== wf-S1 beta crossover, n={} (mu={}), worst structured v2={} prime, rmax={} ===",n,mu,mu,rmax);
    println!("beta sweep: SUP_r K_eff^NP > 1 => structured-prime energy INFLATION (transfer-false); <=1 => transfer-holds");
    for bx in [30,32,34,36,38,40,42,45,48,50] { // beta*10
        let beta=bx as f64/10.0; let lo=((n as f64).powf(beta)) as u64;
        if let Some(p)=find_prime(n,lo,mu){
            let(enp,mnp)=eval(n,p,rmax,nth);let lp=(p as f64).ln();let prize=((n as f64)*(lp-ln_n)).sqrt();
            let mut supk=0.0f64;let mut supr=0;for r in 1..=rmax{if enp[r]>0.0{let k=((enp[r].ln()-(ldfact(r)+r as f64*ln_n))/r as f64).exp();if k>supk{supk=k;supr=r}}}
            let verdict=if supk<=1.0001{"HOLDS"}else{"INFLATE"};
            println!("  beta={:.1} p={} (actual beta={:.3}) | SUP K_eff^NP={:.4}@r={} [{}] | M/prize={:.4}",beta,p,lp/ln_n,supk,supr,verdict,mnp/prize);
        } else { println!("  beta={:.1}: no prime found",beta); }
    }
}
