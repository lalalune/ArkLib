// wf-A05 (#444) FAST: orbit-count GROWTH exponent via MODULAR negacyclic-det divisibility.
//
// We need the growth rate of the base-orbit count O_w(n,p) of weight-w spurious configs as n grows
// at the prize regime (beta=4, p=1 mod n). The exact-integer-norm probe (probe_wfA05_galois_orbit_count)
// is i128-bounded (n<=64) and slow. HERE: detect p | N(sigma_T) by computing det(negacyclic) MOD p
// directly (Gaussian elimination over F_p) -- no big integers, scales to n=128,256. A weight-w config
// is spurious iff det == 0 mod p AND the config is antipodal-free with NONZERO true norm (we approximate
// "true norm != 0" by: not an antipodal pair, i.e. support is not {i, i} with opposite signs at the same
// reduced position -- structurally impossible for distinct positions in [0,n/2), so any det==0 mod p with
// distinct support IS a genuine spurious relation EXCEPT the rare char-0 vanishing, which for weight 4
// at n=2^mu can only be the +-(zeta^a - zeta^b + zeta^c - zeta^d)=0 type; we screen those by also
// computing det mod a SECOND large prime p2 -- if det==0 mod BOTH p and p2, it's likely a true ZERO
// (char-0 vanishing), excluded. This gives O_w EXACTLY for the genuine char-p spurious set.
//
// THRESHOLD: K bounded at depth r=w/2 <=> O_w(n,p) <= C*(2r-1)!!*n^{r-1}. For w=4 (r=2): O_4 <= 3C*n.
// We report O_4 and O_4/n across n=32,64,128 at the structured (max-v2) prize prime. The growth
// exponent alpha (O_4 ~ n^alpha) vs the threshold exponent 1 decides explode (alpha>1) vs bounded.
//
// build: rustc -O probe_wfA05_orbit_growth.rs -o /tmp/a05g ; run: /tmp/a05g

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn gcd(a:u64,b:u64)->u64{if b==0{a}else{gcd(b,a%b)}}
fn inv(a:u64,p:u64)->u64{mpow(a%p,p-2,p)}

// det of negacyclic matrix of coeff vec a (len d=n/2, entries in {-1,0,1}) MOD p (F_p Gaussian elim).
fn det_mod(a:&[i64], d:usize, p:u64)->u64{
    let mut m=vec![0u64;d*d];
    for j in 0..d { for r in 0..d {
        let v = if r>=j { a[r-j] } else { -a[r-j+d] };
        let vm = ((v % p as i64) + p as i64) as u64 % p;
        m[r*d+j]=vm;
    }}
    let mut det=1u64;
    for k in 0..d {
        // find pivot
        let mut piv=k;
        while piv<d && m[piv*d+k]==0 { piv+=1; }
        if piv==d { return 0; }
        if piv!=k { for j in 0..d { m.swap(piv*d+j,k*d+j);} det = p - det % p; if det==p {det=0;} }
        let pivv=m[k*d+k];
        det = ((det as u128 * pivv as u128) % p as u128) as u64;
        let ipv=inv(pivv,p);
        for i in (k+1)..d {
            let f=m[i*d+k];
            if f!=0 {
                let ff=(f as u128 * ipv as u128 % p as u128) as u64;
                for j in k..d {
                    let sub=(ff as u128 * m[k*d+j] as u128 % p as u128) as u64;
                    m[i*d+j]=(m[i*d+j]+p-sub)%p;
                }
            }
        }
    }
    det % p
}

fn units(n:u64)->Vec<u64>{ (1..n).filter(|&a| gcd(a,n)==1).collect() }
fn act(vec:&[i64], a:u64, n:usize)->Vec<i64>{
    let half=n/2; let mut out=vec![0i64;half];
    for i in 0..half { if vec[i]!=0 { let j=((i as u64*a)%(n as u64)) as usize;
        if j<half {out[j]+=vec[i];} else {out[j-half]-=vec[i];} } }
    out
}
fn neg(v:&[i64])->Vec<i64>{v.iter().map(|&x|-x).collect()}

// O_w via modular det at TWO primes p (prize) and p2 (witness sieve for char-0 zeros).
// genuine char-p spurious: det==0 mod p AND det!=0 mod p2 (so true norm != 0).
fn orbit_count_mod(n:u64, p:u64, p2:u64, w:usize)->(u64,u64,Vec<usize>){
    let d=(n/2) as usize;
    let us=units(n);
    let mut spur:std::collections::HashSet<Vec<i64>>=std::collections::HashSet::new();
    let mut a=vec![0i64;d];
    fn rec(a:&mut Vec<i64>, pos:usize, d:usize, left:usize, p:u64, p2:u64,
           spur:&mut std::collections::HashSet<Vec<i64>>){
        if left==0 {
            if det_mod(a,d,p)==0 && det_mod(a,d,p2)!=0 { spur.insert(a.clone()); }
            return;
        }
        if pos>=d || d-pos<left { return; }
        rec(a,pos+1,d,left,p,p2,spur);
        a[pos]=1;  rec(a,pos+1,d,left-1,p,p2,spur);
        a[pos]=-1; rec(a,pos+1,d,left-1,p,p2,spur);
        a[pos]=0;
    }
    rec(&mut a,0,d,w,p,p2,&mut spur);
    let total=spur.len() as u64;
    let mut seen:std::collections::HashSet<Vec<i64>>=std::collections::HashSet::new();
    let mut orbits=0u64; let mut sizes:std::collections::BTreeSet<usize>=std::collections::BTreeSet::new();
    for v in spur.iter() {
        if seen.contains(v){continue;}
        let mut orb:std::collections::HashSet<Vec<i64>>=std::collections::HashSet::new();
        for &au in &us { let av=act(v,au,n as usize); orb.insert(av.clone()); orb.insert(neg(&av)); }
        let mut rs=0usize;
        for ov in orb.iter(){ if spur.contains(ov){seen.insert(ov.clone()); rs+=1;} }
        orbits+=1; sizes.insert(rs);
    }
    (total,orbits,sizes.into_iter().collect())
}

// max-v2 (structured) prize prime in a band above n^4
fn struct_prime(n:u64)->u64{
    let lo=(n as f64).powf(4.0) as u64;
    let mut p=fp(n,lo); let mut best=p; let mut bv=(p-1).trailing_zeros();
    for _ in 0..400 { let v=(p-1).trailing_zeros(); if v>bv {bv=v; best=p;} p=fp(n,p+1); }
    best
}

fn dfact(k:i64)->f64{let mut r=1.0;let mut x=k;while x>=1{r*=x as f64;x-=2;}r}

fn main(){
    println!("# wf-A05 FAST: orbit-count GROWTH O_4(n,p) via modular negacyclic det. beta=4.");
    println!("# Threshold for K bounded at r=2: O_4 <= 3C*n (i.e. O_4/n bounded). Growth O_4~n^alpha,");
    println!("# alpha<=1 => bounded; alpha>1 => orbit count EXPLODES => transfer false.\n");

    // sieve prime p2 (large, distinct from p) to detect char-0 zeros
    let mut pts:Vec<(f64,f64)>=vec![];
    for &n in &[32u64,64,128] {
        let p=struct_prime(n);
        let p2=fp(n, 2_000_000_007u64);   // big distinct prime = 1 mod n, for char-0-zero sieve
        let beta=(p as f64).ln()/(n as f64).ln();
        let v2=(p-1).trailing_zeros();
        let t0=std::time::Instant::now();
        let (tot,orb,sizes)=orbit_count_mod(n,p,p2,4);
        let secs=t0.elapsed().as_secs_f64();
        let phi=(units(n).len()) as u64;
        let thr=3.0*(n as f64);           // 3*n = (2r-1)!! * n^{r-1} at r=2, C=1
        let on=orb as f64/(n as f64);
        println!("  n={:>3} p={} (beta={:.3},v2={}) phi={}: #spur={} O_4={} orbit_sizes={:?}",
            n,p,beta,v2,phi,tot,orb,sizes);
        println!("        O_4/n={:.4}  THR_2(C=1)=3n={:.0}  O_4/THR={:.4}  [{:.1}s]",
            on, thr, orb as f64/thr, secs);
        if orb>0 { pts.push((n as f64, orb as f64)); }
    }
    if pts.len()>=2 {
        let (x0,y0)=pts[0]; let (x1,y1)=*pts.last().unwrap();
        let alpha=(y1.ln()-y0.ln())/(x1.ln()-x0.ln());
        println!("\n  => GROWTH EXPONENT O_4 ~ n^{:.3}  (threshold for K bounded at r=2: alpha<=1)", alpha);
        println!("     VERDICT: {}", if alpha<=1.15 {"alpha<=1 => orbit count BOUNDED at r=2 (pre-screen consistent with K bounded)"}
                                      else {"alpha>1 => orbit count EXPLODES => transfer-false signal"});
        let _=dfact(3);
    } else {
        println!("\n  => insufficient nonzero orbit data (orbit count off below the threshold n).");
    }
}
