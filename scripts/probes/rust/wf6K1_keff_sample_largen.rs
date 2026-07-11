// wf-K1 large-n: Monte-Carlo coset sampling for K_eff(n) (unbiased moment estimate) at beta=4.
// For n=1024,2048,4096 the full m=(p-1)/n cosets are too many for exact O(p) enumeration,
// but E_r' = (1/p) sum_b eta_b^{2r} = (n/(p-1)) * mean over cosets of eta_b^{2r} (each coset rep
// appears once; eta_b real). Sample S random cosets b=gn^k (k uniform in [0,m)), compute exact
// eta_b = sum_{x in mu} cos(2 pi b x / p), accumulate moments. This is an UNBIASED estimate of
// E_r' (the average), hence of K_eff. (The TRUE max is undersampled by sampling, so we report the
// moment-bound proxy q^{1/2r}(E_r)^{1/2r} which is an UPPER bound on M and the relevant prize obj.)
// usage: wf6K1samp <n> <nthreads> <rmax> <samples> [beta]
use std::f64::consts::PI;
use std::thread; use std::sync::Arc;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}if n%3==0{return n==3}let mut d=5;while d*d<=n{if n%d==0{return false}if n%(d+2)==0{return false}d+=6}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn ldfact(r:usize)->f64{let mut v=0.0;for j in 1..=r{v+=((2*j-1)as f64).ln()}v}
// xorshift rng
fn run(n:u64,p:u64,rmax:usize,samples:u64,nth:usize){
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p); let mu=Arc::new(mu);
    let per=samples/nth as u64;
    let mut hs=vec![];
    for t in 0..nth as u64{
        let mu=Arc::clone(&mu);
        hs.push(thread::spawn(move||{
            let mut s=vec![0.0f64;rmax+1]; let mut mx=0.0f64;
            let mut st=0x9E3779B97F4A7C15u64 ^ (t.wrapping_mul(0xBF58476D1CE4E5B9));
            let pp=p as u128; let inv=2.0*PI/p as f64;
            for _ in 0..per {
                // random exponent k in [0,m)
                st^=st<<13; st^=st>>7; st^=st<<17;
                let k = st % m;
                let b = mpow(gn,k,p);
                let mut re=0.0; for &x in mu.iter(){let tt=((b as u128*x as u128)%pp)as u64; re+=(inv*(tt as f64)).cos();}
                if re.abs()>mx{mx=re.abs();}
                let e2=re*re; let mut pw=1.0; for r in 1..=rmax{pw*=e2; s[r]+=pw;}
            }
            (s,mx)
        }));
    }
    let mut tot=vec![0.0f64;rmax+1]; let mut gmx=0.0f64;
    for h in hs{let (s,mx)=h.join().unwrap(); for r in 1..=rmax{tot[r]+=s[r];} if mx>gmx{gmx=mx;}}
    let nsamp=(per*nth as u64) as f64;
    let lp=(p as f64).ln(); let ln_n=(n as f64).ln();
    let prize=((n as f64)*(lp-ln_n)).sqrt();
    // E_r' estimate = mean of eta^{2r} over cosets (sample mean); note sum_b eta^{2r}/p = (m/p)*mean ~= mean/n
    // E_r' = (1/p) sum_{b!=0} eta^{2r}; b ranges over m cosets each repeated n times in F_p^* => sum_{b!=0} = n*sum_cosets
    // so E_r' = (n/p)* sum_cosets eta^{2r} = (n*m/p)* mean = ((p-1)/p)*mean ~= mean.
    let mut peak=0.0f64; let mut pr=0; let mut minmr=f64::INFINITY; let mut ar=0;
    for r in 1..=rmax {
        let mean = tot[r]/nsamp;            // mean over sampled cosets of eta^{2r}
        // Match the exact-probe convention: E_r = (1/p) * sum over the m coset reps = (m/p)*mean.
        let er = (m as f64/p as f64)*mean;
        let ln_er = er.ln();
        let keff = ((ln_er - (ldfact(r)+r as f64*ln_n))/r as f64).exp();
        if keff>peak{peak=keff; pr=r;}
        let mbound=((lp+ln_er)/(2.0*r as f64)).exp();
        let mr=mbound/prize; if mr<minmr{minmr=mr; ar=r;}
    }
    println!("  n={} p={} m={} beta={:.3} samples={} | peak_K_eff={:.4}@r={} | mom_bound/prize={:.4}@r={} | sampled_max/prize={:.4}",
        n,p,m,(p as f64).ln()/ln_n,samples,peak,pr,minmr,ar,gmx/prize);
}
fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:u64=a[1].parse().unwrap();
    let nth:usize=if a.len()>2{a[2].parse().unwrap()}else{8};
    let rmax:usize=if a.len()>3{a[3].parse().unwrap()}else{50};
    let samples:u64=if a.len()>4{a[4].parse().unwrap()}else{20_000_000};
    let beta:f64=if a.len()>5{a[5].parse().unwrap()}else{4.0};
    let p=fp(n,(n as f64).powf(beta) as u64);
    run(n,p,rmax,samples,nth);
}
