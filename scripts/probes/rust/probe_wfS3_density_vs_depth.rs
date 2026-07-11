// wf-S3: bad-prime DENSITY in the prize window as a function of DEPTH r (#444).
//
// The S3 question the campaign left open: the LARGEST bad prime grows n^Theta(log n) (so the
// generic prize prime is bad at deep depth -- M2 refuted). BUT does the bad-prime SET stay
// SPARSE (density -> 0) in the prize window [n^beta, n^{beta+1}], so the prize could pick a good
// representative? And how does that density move as the depth r (weight w=2r) grows toward ln q?
//
// This probe enumerates EVERY antipodal-free signed config of weight EXACTLY w (not <= w) -- so we
// isolate the depth-r=w/2 layer -- computes the exact cyclotomic norm N(sigma_T) = det(negacyclic
// matrix), collects band primes (p == 1 mod n, in [n^beta, n^{beta+1}]) dividing some norm, and
// reports the density bad/band at each weight. The TREND of density vs w at fixed n is the S3
// deliverable: rising => the prize cannot pick a good rep (bad set is dense); falling => sparse.
//
// build: rustc -O probe_wfS3_density_vs_depth.rs -o /tmp/wfS3d

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
// collect prime factors of |x| that are == 1 mod n and lie in [lo,hi]
fn band_factors(mut x:i128, lo:i128, hi:i128, n:u64, out:&mut std::collections::BTreeSet<u64>){
    if x<0 { x=-x; } if x==0||x==1 { return; }
    let mut d:i128=2;
    while d*d<=x { if x%d==0 { while x%d==0 { x/=d; } if d>=lo&&d<=hi&&(d as u64)%n==1 { out.insert(d as u64); } } d+=1; }
    if x>1 && x>=lo && x<=hi && (x as u64)%n==1 && isprime128(x) { out.insert(x as u64); }
}

// recursively place EXACTLY `need` nonzero entries (+-1) among positions [pos..d), counting norm
fn rec(a:&mut Vec<i64>, pos:usize, d:usize, need:usize,
       total:&mut u64, mx:&mut i128, bad:&mut std::collections::BTreeSet<u64>,
       lo:i128, hi:i128, n:u64){
    if need==0 {
        let nv=norm_exact(a,d); *total+=1;
        let av=if nv<0 {-nv} else {nv}; if av>*mx {*mx=av;}
        band_factors(nv,lo,hi,n,bad);
        return;
    }
    if d-pos < need { return; }
    // skip pos
    a[pos]=0; rec(a,pos+1,d,need,total,mx,bad,lo,hi,n);
    // place +1 / -1 at pos
    a[pos]=1;  rec(a,pos+1,d,need-1,total,mx,bad,lo,hi,n);
    a[pos]=-1; rec(a,pos+1,d,need-1,total,mx,bad,lo,hi,n);
    a[pos]=0;
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let n:u64 = if args.len()>1 { args[1].parse().unwrap() } else { 32 };
    let beta:f64 = if args.len()>2 { args[2].parse().unwrap() } else { 4.0 };
    let wmax:usize = if args.len()>3 { args[3].parse().unwrap() } else { 14 };
    let d=(n/2) as usize;
    let lo=(n as f64).powf(beta) as i128;
    let hi=(n as f64).powf(beta+1.0) as i128;
    let floor=beta*(n as f64).log2();

    // band primes p==1 mod n in [lo,hi]
    let mut band_primes:u64=0; let mut p=lo as u64; if p%n!=1 { p+=(1+n-p%n)%n; }
    while (p as i128) <= hi { if isp(p)&&p%n==1 { band_primes+=1; } p+=n; }

    println!("== wf-S3 DENSITY vs DEPTH: n={} phi={} beta={} band=[n^{},n^{}] floor_log2={:.2} band_primes={} ==",
             n,d,beta,beta,beta+1.0,floor,band_primes);
    println!("  w (=2r)  r   configs    MAXNORM_log2  margin   bad_primes  DENSITY");
    // weight w must be even (antipodal-free signed config that can vanish: need even # of +-1 for real)
    // but enumerate all w to see the trend; the leading a[0]=+1 is canonical (norm invariant under global rotation)
    for w in (2..=wmax).step_by(2) {
        if w > d { break; }
        let mut total=0u64; let mut mx:i128=0;
        let mut bad=std::collections::BTreeSet::new();
        let mut a=vec![0i64;d];
        rec(&mut a,0,d,w,&mut total,&mut mx,&mut bad,lo,hi,n);
        let mlog=if mx>0 {(mx as f64).log2()} else {0.0};
        let dens=if band_primes>0 {bad.len() as f64/band_primes as f64} else {0.0};
        println!("  {:>3}    {:>2}  {:>9}  {:>10.2}    {:>+6.2}   {:>8}    {:.6}",
                 w, w/2, total, mlog, mlog-floor, bad.len(), dens);
    }
}
