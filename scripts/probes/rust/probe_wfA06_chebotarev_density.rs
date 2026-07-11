// wf-A06: effective-Chebotarev / Lagarias-Odlyzko bad-prime DENSITY vs the config explosion (#444).
//
// THE ANGLE. The S3 supply route asks: is the SPECIFIC prize prime p ~ n^beta good at depth
// r ~ ln q? A prime p (== 1 mod n, n=2^mu) is BAD at depth r iff p | N(sigma_T) for some
// antipodal-free signed config T of weight w = |T| <= 2r, where N = Norm_{Q(zeta_n)/Q}(sum +-zeta^i).
//
// The recorded wall: at fixed depth the bad set is FINITE (good rep EXISTS by pigeonhole), but at
// depth r ~ ln q the config count is C(phi(n), 2r) * 2^{2r} = n^{Theta(ln n)} (quasi-poly), defeating
// naive enumeration. A06 attempts the EFFECTIVE-CHEBOTAREV (Lagarias-Odlyzko / Bach-Sorenson-GRH)
// count of bad primes -- does the bad-prime DENSITY -> 0 fast enough that the prize prime is good w.h.p.?
//
// THE TWO QUANTITIES (this probe measures both, exactly, then extrapolates to prize scale):
//   B(n,r) = #{ band primes p == 1 mod n, p in [n^beta, n^{beta+1}], p | some weight-<=2r norm }
//   W(n,beta) = #{ band primes p == 1 mod n, p in [n^beta, n^{beta+1}] }   (the window supply)
// Density = B/W. The A06 verdict: does B/W -> 0 (prize prime good w.h.p.) or -> 1 (no escape)?
//
// THE EFFECTIVE-CHEBOTAREV / LAGARIAS-ODLYZKO PREDICTION (what we test against the data):
//   A prime p is bad iff some N(sigma_T) == 0 mod p. For fixed T with N != 0, this is ONE congruence
//   class mod (each prime factor of N). The UNION over all #configs T of "p | N_T" has, by inclusion-
//   exclusion / the trivial divisor bound, at most  Sum_T omega(|N_T|)  bad primes. omega(|N_T|) <=
//   log_2 |N_T| ~ phi(n)*c_w. So  B(n,r) <= #configs * phi(n) * c_w  =  C(phi(n),2r) 2^{2r} phi(n) c.
//   The window  W(n,beta) ~ (n^{beta+1}-n^beta)/(phi(n) ln(n^beta)) ~ n^{beta-1}/(beta phi(n) ln n).
//   At beta=4, phi(n)=n/2:  W ~ n^{beta-2}/(2 beta ln n) = n^2/(8 ln n).
//   So the trivial bound gives  B/W ~ [C(n/2, 2r) 2^{2r} (n/2) c] / [n^2/(8 ln n)]  -> infinity at
//   r ~ ln n. The trivial divisor bound LOSES. A06 asks whether the EFFECTIVE prime-splitting count
//   (density of p that ACTUALLY divides some norm, not the union upper bound) is much smaller.
//
// This probe measures the ACTUAL B(n,r) (exact, not the union bound) so we can see if the real bad
// density stays << 1 or saturates. Reuses the negacyclic-det exact-norm engine of c1/wfS3.
//
// build: rustc -O probe_wfA06_chebotarev_density.rs -o /tmp/wfA06

fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}

// exact integer norm N(sigma) = det(negacyclic matrix of a), a in {-1,0,1}^d, d=phi(n)=n/2.
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
// collect band prime factors (== 1 mod n, in [lo,hi]) of |x|, AND total omega over the band
fn band_factors(mut x:i128, lo:i128, hi:i128, n:u64,
                out:&mut std::collections::BTreeSet<u64>, omega:&mut u64){
    if x<0 { x=-x; } if x==0||x==1 { return; }
    let mut d:i128=2;
    while d*d<=x { if x%d==0 { while x%d==0 { x/=d; }
        if d>=lo&&d<=hi&&(d as u64)%n==1 { out.insert(d as u64); *omega+=1; } } d+=1; }
    if x>1 && x>=lo && x<=hi && (x as u64)%n==1 && isprime128(x) { out.insert(x as u64); *omega+=1; }
}

fn rec(a:&mut Vec<i64>, pos:usize, d:usize, need:usize,
       total:&mut u64, mx:&mut i128, bad:&mut std::collections::BTreeSet<u64>, omega:&mut u64,
       lo:i128, hi:i128, n:u64){
    if need==0 {
        let nv=norm_exact(a,d); *total+=1;
        let av=if nv<0 {-nv} else {nv}; if av>*mx {*mx=av;}
        band_factors(nv,lo,hi,n,bad,omega);
        return;
    }
    if d-pos < need { return; }
    a[pos]=0; rec(a,pos+1,d,need,total,mx,bad,omega,lo,hi,n);
    a[pos]=1;  rec(a,pos+1,d,need-1,total,mx,bad,omega,lo,hi,n);
    a[pos]=-1; rec(a,pos+1,d,need-1,total,mx,bad,omega,lo,hi,n);
    a[pos]=0;
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = if args.len()>1 { args[1].parse().unwrap() } else { 32 };
    let beta:f64 = if args.len()>2 { args[2].parse().unwrap() } else { 4.0 };
    let wmax:usize = if args.len()>3 { args[3].parse().unwrap() } else { 10 };
    let d=(n/2) as usize;
    let lo=(n as f64).powf(beta) as i128;
    let hi=(n as f64).powf(beta+1.0) as i128;
    let floor=beta*(n as f64).log2();

    let mut band_primes:u64=0; let mut p=lo as u64; if p%n!=1 { p+=(1+n-p%n)%n; }
    while (p as i128) <= hi { if isp(p)&&p%n==1 { band_primes+=1; } p+=n; }

    println!("== wf-A06 effective-Chebotarev bad density: n={} phi={} beta={} band=[n^{},n^{}] W={} floor_log2={:.2} ==",
             n,d,beta,beta,beta+1.0,band_primes,floor);
    println!("  w   r   configs       MAXNORM_l2   B(bad)   Sum_omega(union-UB)   B/W(real)   union-UB/W");
    for w in (2..=wmax).step_by(2) {
        if w > d { break; }
        let mut total=0u64; let mut mx:i128=0; let mut omega=0u64;
        let mut bad=std::collections::BTreeSet::new();
        let mut a=vec![0i64;d];
        rec(&mut a,0,d,w,&mut total,&mut mx,&mut bad,&mut omega,lo,hi,n);
        let mlog=if mx>0 {(mx as f64).log2()} else {0.0};
        let dens=if band_primes>0 {bad.len() as f64/band_primes as f64} else {0.0};
        let ubdens=if band_primes>0 {omega as f64/band_primes as f64} else {0.0};
        let _=floor;
        println!("  {:>2}  {:>2}  {:>10}  {:>10.2}   {:>7}   {:>15}     {:.6}   {:.6}",
                 w, w/2, total, mlog, bad.len(), omega, dens, ubdens);
    }
}
