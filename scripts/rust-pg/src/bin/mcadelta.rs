// mcadelta — TRUE MCA delta* via the in-tree mcaEvent (Errors.lean Def 4.3), NOT the far-line proxy.
//
// mcaEvent(C,delta,u0,u1,gamma): EX S, |S| >= (1-delta) n, AND
//   (EX codeword w in C, w = u0 + gamma*u1 on S)  AND  NOT pairJointAgreesOn(C,S,u0,u1)
// where pairJointAgreesOn = EX (v0,v1) in C^2, v0=u0 and v1=u1 on all of S.
//
// LEMMA (used here, proven in the comment of Errors.lean monotonicity): no-joint is monotone in S
// (larger S => harder to jointly explain), and line-explainability needs S subset of some agree(L,w).
// So the optimal S for a fixed witnessing codeword w is A := agree(L_gamma, w) itself.
//   => mcaEvent(gamma) <=> EX codeword w with |agree(L_gamma,w)| >= t  AND
//                          NOT EX (v0,v1) in C^2 with A subset agree(u0,v0) cap agree(u1,v1).
// t = ceil((1-delta) n).
//
// We compute, for each tested (u0,u1), the BAD-scalar count = #{gamma : mcaEvent holds}, and the
// max over a worst-case search family. Then delta* = largest delta whose worst-case bad count
// exceeds the prize budget (here we report the FULL bad-count profile vs t so the caller reads
// delta* = 1 - t*/n directly), AND we compare to the FAR-LINE proxy (drop the no-joint clause).
//
// Codewords agreeing with a word z on >= t points: enumerate via k-subset interpolation (a codeword
// agreeing on >= t >= k pts is the interpolant of some k of its agreement pts), exactly like listsize.rs.
//
// Usage: mcadelta <n> <k> [mult=4] [gammacap=0]   (gammacap>0 caps #gamma scanned for speed; 0=all p)
use rayon::prelude::*;
use std::collections::HashSet;
#[inline] fn mulmod(a:u64,b:u64,p:u64)->u64{((a as u128*b as u128)%p as u128)as u64}
#[inline] fn addmod(a:u64,b:u64,p:u64)->u64{let s=a+b;if s>=p{s-p}else{s}}
#[inline] fn submod(a:u64,b:u64,p:u64)->u64{if a>=b{a-b}else{p-b+a}}
fn powmod(mut b:u64,mut e:u64,p:u64)->u64{let mut r=1u64;b%=p;while e>0{if e&1==1{r=mulmod(r,b,p);}b=mulmod(b,b,p);e>>=1;}r}
#[inline] fn invmod(a:u64,p:u64)->u64{powmod(a,p-2,p)}
fn isprime(x:u64)->bool{if x<2{return false;}for &q in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{if x%q==0{return x==q;}}let mut d=x-1;let mut s=0;while d%2==0{d/=2;s+=1;}'a:for &a in &[2u64,3,5,7,11,13,17,19,23,29,31,37]{let mut y=powmod(a,d,x);if y==1||y==x-1{continue;}for _ in 0..s-1{y=mulmod(y,y,x);if y==x-1{continue 'a;}}return false;}true}
fn factor(mut x:u64)->Vec<u64>{let mut f=vec![];let mut d=2;while d*d<=x{if x%d==0{f.push(d);while x%d==0{x/=d;}}d+=1;}if x>1{f.push(x);}f}
fn proot(p:u64)->u64{let fs=factor(p-1);for g in 2..p{if fs.iter().all(|&q|powmod(g,(p-1)/q,p)!=1){return g;}}0}
fn big_prime(n:u64,mult:u32)->u64{let mut p=n.pow(mult);if p<1000{p=1000;}p+=(1+n-p%n)%n;loop{if p%n==1&&isprime(p){return p;}p+=n;}}

// interpolate deg<k poly through k points (xs[i],ys[i]); coeff vec len k
fn interp(idx:&[usize],mu:&[u64],z:&[u64],k:usize,p:u64)->Vec<u64>{
    let xs:Vec<u64>=idx.iter().map(|&i|mu[i]).collect();
    let ys:Vec<u64>=idx.iter().map(|&i|z[i]).collect();
    let mut coef=vec![0u64;k];
    for i in 0..k{let mut denom=1u64;for j in 0..k{if j!=i{denom=mulmod(denom,submod(xs[i],xs[j],p),p);}}
        let scale=mulmod(ys[i],invmod(denom,p),p);
        let mut np=vec![0u64;k];np[0]=1;let mut deg=0usize;
        for j in 0..k{if j!=i{let mut nn=vec![0u64;k];for t in 0..=deg{nn[t+1]=addmod(nn[t+1],np[t],p);nn[t]=addmod(nn[t],mulmod(np[t],submod(0,xs[j],p),p),p);}np=nn;deg+=1;}}
        for t in 0..k{coef[t]=addmod(coef[t],mulmod(scale,np[t],p),p);}}
    coef}
#[inline] fn eval(c:&[u64],x:u64,p:u64)->u64{let mut r=0u64;for &v in c.iter().rev(){r=addmod(mulmod(r,x,p),v,p);}r}
// agreement SET (bitmask over n points, n<=64) of codeword c with word z
#[inline] fn agree_mask(c:&[u64],mu:&[u64],z:&[u64],p:u64)->u64{
    let mut m=0u64;for i in 0..mu.len(){if eval(c,mu[i],p)==z[i]{m|=1<<i;}}m}
fn next_comb(c:&mut [usize],n:usize)->bool{let s=c.len();let mut i=s;while i>0{i-=1;if c[i]!=i+n-s{c[i]+=1;for j in i+1..s{c[j]=c[j-1]+1;}return true;}}false}

// All distinct codewords agreeing with z on >= t points, returned as (coeff, agreemask).
fn codewords_agree_ge(z:&[u64],mu:&[u64],k:usize,p:u64,t:usize)->Vec<(Vec<u64>,u64)>{
    let n=mu.len();
    let mut seen:HashSet<Vec<u64>>=HashSet::new();
    let mut out=vec![];
    let mut c:Vec<usize>=(0..k).collect();
    loop{
        let coef=interp(&c,mu,z,k,p);
        if !seen.contains(&coef){
            let m=agree_mask(&coef,mu,z,p);
            if (m.count_ones() as usize)>=t{ out.push((coef.clone(),m)); }
            seen.insert(coef);
        }
        if !next_comb(&mut c,n){break;}
    }
    out}

fn main(){
    let a:Vec<String>=std::env::args().collect();
    let n:usize=a[1].parse().unwrap();
    let k:usize=a[2].parse().unwrap();
    let mult:u32=a.get(3).and_then(|x|x.parse().ok()).unwrap_or(4);
    let gammacap:u64=a.get(4).and_then(|x|x.parse().ok()).unwrap_or(0);
    assert!(n<=64,"n<=64 (bitmask)");
    let p=big_prime(n as u64,mult);
    let g=proot(p);let h=powmod(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n).map(|i|powmod(h,i as u64,p)).collect();
    let powtab:Vec<Vec<u64>>=(0..n).map(|e|(0..n).map(|i|powmod(mu[i],e as u64,p)).collect()).collect();
    let rho=k as f64/n as f64; let john=1.0-rho.sqrt();
    println!("n={} k={} rho={:.4} p={} (beta~{:.2}) Johnson_delta={:.4} cap={:.4}",
        n,k,rho,p,(p as f64).ln()/(n as f64).ln(),john,1.0-rho);
    // Johnson agreement t_john = floor(sqrt(rho) n); window radii are delta in (john, cap), i.e.
    // agreement t in (rho n, sqrt(rho) n). We scan t from t_john DOWN to t_cap and below.
    let mono=|e:usize|->Vec<u64>{ powtab[e].clone() };
    let bino=|e1:usize,e2:usize,c2:u64|->Vec<u64>{ (0..n).map(|i|addmod(powtab[e1][i],mulmod(c2,powtab[e2][i],p),p)).collect() };
    // worst-case (u0,u1) family. We want NEAR u1 (the open end), so we ALSO test u1 close to code:
    //   - far monomials x^b (b>=k): the established proxy face
    //   - near directions: u1 = (codeword) + (small monomial), i.e. x^j + x^b with j<k  (j<k part is a real codeword)
    //   - pure low monomial x^j (j<k): u1 IS a codeword (fully near) -> pairJointAgrees easy, bad count should DROP
    let slim:bool = std::env::var("MCA_SLIM").ok().map(|v|v!="0").unwrap_or(false);
    let mut dirs:Vec<(String,Vec<u64>,Vec<u64>)>=vec![];
    let u0_mono=|e:usize| mono(e);
    // ALWAYS: far monomial PAIRS u0=x^a,u1=x^b (a,b>=k) -- the proven over-det worst-case carrier.
    for a in k..n { for b in k..n { if a!=b {
        dirs.push((format!("PAIR u0=x^{} u1=x^{}",a,b), mono(a), mono(b)));
    }}}
    // ALWAYS: NEAR directions u1 = codeword x^j + far x^b (under-det / agreement-sharing probe).
    for j in 0..k { for b in k..n {
        dirs.push((format!("NEAR u1=x^{}+x^{} u0=x^{}",j,b,k), u0_mono(k), bino(j,b,1)));
    }}
    // RANDOM/generic directions (under-det / agreement-sharing probe) -- HEAVY (dense explainability,
    // no early-exit), causes outer load imbalance, so only in non-slim and few of them.
    if !slim {
        let mut st:u64=0x9e3779b97f4a7c15;
        let mut nextr=|p:u64|->u64{ st=st.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); (st>>33)%p };
        for r in 0..8 {
            dirs.push((format!("RAND#{}",r), (0..n).map(|_|nextr(p)).collect(), (0..n).map(|_|nextr(p)).collect()));
        }
    }
    if !slim {
        for j in 0..k { dirs.push((format!("CODEWORD u1=x^{} u0=x^{}",j,k), u0_mono(k), mono(j))); }
        for j0 in 0..k { for b in k..n { dirs.push((format!("u0=x^{}(cw) u1=x^{}",j0,b), mono(j0), mono(b))); }}
    }

    // For a fixed (u0,u1) compute bad-count and far-line(proxy)-count at agreement threshold t.
    // bad(gamma): EX codeword w with A=agree(L,w),|A|>=t, AND NOT EX (v0,v1) with A subset agree(u0,v0) cap agree(u1,v1).
    // proxy(gamma): EX codeword w with |agree(L,w)|>=t  (drop no-joint).
    let scan_one=|u0:&[u64],u1:&[u64],t:usize|->(u64,u64){
        // precompute, for each codeword agreeing-set used: cheap. gamma loop is the heavy axis.
        let gmax=if gammacap>0 {gammacap.min(p)} else {p};
        // For no-joint: given A (mask), does EX (v0,v1) in C^2 with A subset agree(u0,v0) and A subset agree(u1,v1)?
        // For RS deg<k: a codeword agreeing with u0 on a set containing A exists IFF interpolant of any k pts of A
        //   (call it v0) agrees with u0 on ALL of A (since |A|>=k forces uniqueness if such v0 exists).
        // So: jointly explainable on A  <=>  (interp_A(u0) agrees u0 on A) AND (interp_A(u1) agrees u1 on A).
        // (need |A|>=k; if |A|<k it's trivially joint-explainable -> not bad.)
        let joint_on=|amask:u64,word0:&[u64],word1:&[u64]|->bool{
            let idx:Vec<usize>=(0..n).filter(|&i|amask&(1<<i)!=0).collect();
            if idx.len()<k {return true;} // <k points always jointly explainable
            let v0=interp(&idx[0..k],&mu,word0,k,p);
            for &i in &idx { if eval(&v0,mu[i],p)!=word0[i] {return false;} }
            let v1=interp(&idx[0..k],&mu,word1,k,p);
            for &i in &idx { if eval(&v1,mu[i],p)!=word1[i] {return false;} }
            true
        };
        // Per gamma we only need bad in {0,1} and proxy in {0,1}. Enumerate k-subsets of the line L,
        // interpolate, keep only agreement>=t; for the FIRST such codeword set proxy=1; if any such
        // codeword's agreement set is NOT joint_on, set bad=1 and stop. Early-exit, no dedup HashSet.
        let mut bad_total=0u64; let mut proxy_total=0u64;
        let mut l=vec![0u64;n];
        let mut seen:HashSet<u64>=HashSet::with_capacity(64);
        let mut c:Vec<usize>=(0..k).collect();
        for gamma in 0..gmax {
            for i in 0..n { l[i]=addmod(u0[i],mulmod(gamma,u1[i],p),p); }
            let mut proxy=0u64; let mut bad=0u64;
            seen.clear();
            for x in c.iter_mut().enumerate(){ *x.1 = x.0; } // reset comb to 0..k
            loop{
                let coef=interp(&c,&mu,&l,k,p);
                let m=agree_mask(&coef,&mu,&l,p);
                if (m.count_ones() as usize)>=t && seen.insert(m) {
                    proxy=1;
                    if !joint_on(m,u0,u1){ bad=1; break; }
                }
                if !next_comb(&mut c,n){break;}
            }
            bad_total+=bad; proxy_total+=proxy;
        }
        (bad_total,proxy_total)
    };

    // scan t from just below Johnson down a few rungs into the window, find worst-case over dirs.
    let t_john=((rho.sqrt())*n as f64).floor() as usize;
    let t_cap=((rho)*n as f64).ceil() as usize;
    println!("t_john={} t_cap={} (window agreement t in ({}..{}], delta=1-t/n)",t_john,t_cap,t_cap,t_john);
    // restrict to the window band around Johnson to capture the crossing cheaply (deep rungs explode).
    let depth:usize=std::env::var("MCA_DEPTH").ok().and_then(|x|x.parse().ok()).unwrap_or(4);
    let tlo = if t_john+1>=depth { (t_john+1-depth).max(k+1) } else { k+1 };
    let trange:Vec<usize>=( tlo..=(t_john+1) ).rev().collect();
    let budget=n as u64;
    for &t in &trange {
        let delta=1.0-(t as f64)/(n as f64);
        let region=if delta>john {"WINDOW"} else {"<=John"};
        // worst over dirs -- OUTER parallel (dirs), INNER (gamma) sequential. Good utilization.
        let res:Vec<(u64,u64,&String)>=dirs.par_iter().map(|(name,u0,u1)|{
            let (b,pr)=scan_one(u0,u1,t);(b,pr,name)
        }).collect();
        let mut best_bad=(0u64,0u64,&dirs[0].0);
        let mut best_proxy=(0u64,0u64,&dirs[0].0);
        for (b,pr,name) in &res {
            if *b>best_bad.0 {best_bad=(*b,*pr,name);}
            if *pr>best_proxy.1 {best_proxy=(*b,*pr,name);}
        }
        println!("t={} (delta={:.4} {}): worstTRUE_bad={} (proxy@that={}) | worstPROXY={} (bad@that={}) | budget={} TRUE>bud?{} PROXY>bud?{}  [bad dir: {}]",
            t,delta,region,best_bad.0,best_bad.1,best_proxy.1,best_proxy.0,budget,
            best_bad.0>budget, best_proxy.1>budget, best_bad.2);
    }
    println!("DONE n={} k={}",n,k);
}
