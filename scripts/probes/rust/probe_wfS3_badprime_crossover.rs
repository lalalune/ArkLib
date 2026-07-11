// wf-S3: the bad-prime / Chebotarev DICHOTOMY made precise.
//
// A prize prime p (~ n^beta, p == 1 mod n) is BAD at depth r iff p | N(sigma_T) for some
// antipodal-free signed config T of weight w <= 2r, where N = Norm_{Q(zeta_n)/Q}(sigma_T) is an
// EXACT integer = det of the negacyclic matrix of the {-1,0,1} coeff vector (deg < phi(n)=n/2).
//
// KEY MECHANISM (the S3 finding): the bad-prime SET in the band [n^beta, n^{beta+1}] = {band primes
// dividing SOME bounded-weight norm}. Since |N| <= (max conjugate)^{phi} but in PRACTICE the norm
// distribution is far thinner, the controlling quantity is  MAXNORM(n,w) = max_T |N(sigma_T)|.
//   - If MAXNORM(n,w) < n^beta  ==>  NO band prime can divide any norm  ==>  bad density = 0 PROVABLY.
//   - Once MAXNORM(n,w) crosses n^beta, bad primes appear; their COUNT is bounded by
//     (# norms) * (max prime factors per norm) <= (#configs) * log_2(MAXNORM) / beta*log2(n),
//     i.e. a SPARSE set of size O(#configs) in a band of ~ n^{beta+1}/(n ln) primes => density -> 0.
//
// This probe emits, per (n, weight w): exact MAXNORM (log2), the band floor log2(n^beta),
// the bad COUNT, the band-prime COUNT, density, and the "crossover margin" = log2 MAXNORM - beta*log2 n.
//
// build: rustc -O probe_wfS3_badprime_crossover.rs -o /tmp/wfS3

fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}

fn norm_exact(a:&[i64], d:usize)->i128{
    let mut m=vec![vec![0i128;d];d];
    for j in 0..d { for r in 0..d {
        let v = if r>=j { a[r-j] } else { -a[r-j+d] };
        m[r][j]=v as i128;
    }}
    let mut sign:i128=1; let mut prev:i128=1;
    for k in 0..d {
        if m[k][k]==0 {
            let mut piv=k+1; while piv<d && m[piv][k]==0 { piv+=1; }
            if piv==d { return 0; }
            m.swap(k,piv); sign=-sign;
        }
        for i in (k+1)..d { for j in (k+1)..d {
            m[i][j] = (m[i][j]*m[k][k] - m[i][k]*m[k][j]) / prev;
        } m[i][k]=0; }
        prev=m[k][k];
    }
    sign * m[d-1][d-1]
}
fn mpow128(mut a:i128,mut e:i128,m:i128)->i128{let mut r=1i128;a%=m;while e>0{if e&1==1{r=r*a%m;}a=a*a%m;e>>=1;}r}
fn isprime128(n:i128)->bool{
    if n<2{return false} for &q in &[2,3,5,7,11,13,17,19,23,29,31,37]{ if n%q==0 {return n==q;} }
    let mut d=n-1; let mut s=0; while d&1==0 {d>>=1;s+=1;}
    'w: for &a in &[2i128,3,5,7,11,13,17,19,23,29,31,37]{
        let mut x=mpow128(a,d,n); if x==1||x==n-1{continue;}
        for _ in 0..s-1 { x=x*x%n; if x==n-1 {continue 'w;} }
        return false;
    } true
}
fn prime_factors(mut x:i128, lo:i128, hi:i128, out:&mut std::collections::BTreeSet<u64>){
    if x<0 { x=-x; } if x==0||x==1 { return; }
    let mut d:i128=2;
    while d*d<=x { if x%d==0 { while x%d==0 { x/=d; } if d>=lo&&d<=hi { out.insert(d as u64); } } d+=1; }
    if x>1 && x>=lo && x<=hi && isprime128(x) { out.insert(x as u64); }
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = if args.len()>1 { args[1].parse().unwrap() } else { 16 };
    let wmax:usize = if args.len()>2 { args[2].parse().unwrap() } else { 8 };
    let beta:f64 = if args.len()>3 { args[3].parse().unwrap() } else { 4.0 };
    let d=(n/2) as usize;
    let plo=(n as f64).powf(beta) as i128;
    let phi_hi=(n as f64).powf(beta+1.0) as i128;
    let bandfloor_log2 = beta*(n as f64).log2();
    println!("== wf-S3 crossover: n={} phi(n)={} beta={} band=[n^{},n^{}] floor_log2={:.2} ==",
             n, d, beta, beta, beta+1.0, bandfloor_log2);

    use std::sync::{Arc,Mutex};
    use std::thread;
    let shared_bad:Arc<Mutex<std::collections::BTreeSet<u64>>>=Arc::new(Mutex::new(std::collections::BTreeSet::new()));
    let shared_max:Arc<Mutex<i128>>=Arc::new(Mutex::new(0i128));
    let shared_total:Arc<Mutex<u64>>=Arc::new(Mutex::new(0u64));
    let mut handles=vec![];
    for s in 0..9i64 {
        let sb=Arc::clone(&shared_bad); let smx=Arc::clone(&shared_max); let st=Arc::clone(&shared_total);
        handles.push(thread::spawn(move||{
            let a1=(s%3)-1; let a2=(s/3)-1;
            let mut a=vec![0i64;d]; a[0]=1; let mut used=1usize;
            a[1]=a1; if a1!=0 {used+=1;}
            if d>2 { a[2]=a2; if a2!=0 {used+=1;} }
            if used>wmax { return; }
            let mut lbad=std::collections::BTreeSet::new(); let mut lmax:i128=0; let mut ltot=0u64;
            fn rec(a:&mut Vec<i64>, pos:usize, d:usize, left:usize,
                   total:&mut u64, mx:&mut i128, bad:&mut std::collections::BTreeSet<u64>, plo:i128, phi:i128){
                if pos==d {
                    let nv=norm_exact(a,d); *total+=1;
                    let av=if nv<0 {-nv} else {nv};
                    if av>*mx {*mx=av;}
                    prime_factors(nv,plo,phi,bad);
                    return;
                }
                a[pos]=0; rec(a,pos+1,d,left,total,mx,bad,plo,phi);
                if left>0 {
                    a[pos]=1; rec(a,pos+1,d,left-1,total,mx,bad,plo,phi);
                    a[pos]=-1; rec(a,pos+1,d,left-1,total,mx,bad,plo,phi);
                    a[pos]=0;
                }
            }
            let startpos=if d>2 {3} else {2};
            rec(&mut a,startpos,d,wmax-used,&mut ltot,&mut lmax,&mut lbad,plo,phi_hi);
            { let mut g=sb.lock().unwrap(); for x in lbad {g.insert(x);} }
            { let mut g=smx.lock().unwrap(); if lmax>*g {*g=lmax;} }
            { let mut g=st.lock().unwrap(); *g+=ltot; }
        }));
    }
    for h in handles { h.join().unwrap(); }
    let bad=shared_bad.lock().unwrap().clone();
    let maxnorm=*shared_max.lock().unwrap();
    let total_configs=*shared_total.lock().unwrap();
    let maxnorm_log2 = if maxnorm>0 {(maxnorm as f64).log2()} else {0.0};

    let mut band_primes:u64=0; let mut p=plo as u64; if p%n!=1 { p+=(1+n-p%n)%n; }
    while (p as i128) <= phi_hi { if isp(p)&&p%n==1 { band_primes+=1; } p+=n; }
    let dens = if band_primes>0 { bad.len() as f64/band_primes as f64 } else {0.0};
    println!("  configs={} MAXNORM_log2={:.2}  margin(MAXNORM-floor)={:.2}  bad={}  band_primes={}  DENSITY={:.6}",
             total_configs, maxnorm_log2, maxnorm_log2-bandfloor_log2, bad.len(), band_primes, dens);
    let provable_zero = maxnorm_log2 < bandfloor_log2;
    println!("  PROVABLE-ZERO (MAXNORM<floor => no band prime can divide ANY norm): {}", provable_zero);
}
