// wf-A05 (#444): the GALOIS-ORBIT COUNT of spurious relations -- the open residual of _wfS7_galois_spread.
//
// SETUP. n=2^mu, p=1 mod n prime, prize regime p ~ n^4 (beta=4). A "spurious" relation is an
// antipodal-free signed config sigma_T = sum_i eps_i zeta_n^i (eps in {-1,0,1}, |support|=w) with
// p | N(sigma_T) = det(negacyclic matrix), N != 0 (antipodal-free => no char-0 vanishing).
//
// PRIOR (_wfS7_galois_spread, axiom-clean): the Galois group G=(Z/n)^* acts FREELY on the spurious
// set, every orbit is FULL of size phi(n)=n/2, so
//      #spurious(n,w,p) = O_w(n,p) * phi(n),   O_w = number of BASE ORBITS.
// The OPEN RESIDUAL stated there: "K bounded <=> the number of BASE ORBITS O_w is controlled".
//
// THE A05 QUESTION (this probe). The depth-r energy splits E_r = (2r-1)!! n^r + spur_r(p), and the
// spurious excess spur_r(p) is carried by signed weight-<=2r configs vanishing mod p. Via the free
// action spur_r(p) ~ (sum_{w<=2r} O_w) * phi(n). K bounded (= prize) needs
//      spur_r(p) <= C * (2r-1)!! n^r
//  <=> (sum O_w)*phi(n) <= C (2r-1)!! n^r
//  <=> O_band(n,p) := sum_{w<=2r} O_w(n,p) <= 2C * (2r-1)!! * n^{r-1}     [phi=n/2]   (*)
// So the EXACT threshold the orbit count must respect is THR_r(n) = (2r-1)!! n^{r-1}. We measure
// O_w and O_band EXACTLY at the prize prime (beta=4) across n, and the ratio rho = O_band / THR_r.
// If rho stays BOUNDED (does not grow with n) => the orbit count does NOT explode => K bounded at
// these depths. If rho GROWS like a power of n => orbit count explodes => K unbounded (transfer
// false). We pre-screen exactly at small n; this is a PRE-SCREEN, not a proof.
//
// Also: confirm the free-action law O_w*phi(n) == #spurious EXACTLY (cross-check of the Lean thm),
// and report O_w at FIXED small weight to see if O_w itself grows.
//
// build: rustc -O probe_wfA05_galois_orbit_count.rs -o /tmp/a05
// run:   /tmp/a05 [maxweight]

fn isp(n:u64)->bool{if n<2{return false}if n%2==0{return n==2}let mut d=3;while d*d<=n{if n%d==0{return false}d+=2}true}
// smallest prime p = 1 mod n with p >= lo
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}

// Exact integer norm = det of negacyclic matrix of coeff vec a (len d=phi(n)=n/2), entries {-1,0,1}.
// Bareiss fraction-free; i128 holds it for d<=16 (weight bounded). Returns 0 if singular.
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

// Galois action of a unit a in (Z/n)^* on a half-length coeff vector (len d=n/2).
// vec lives on residues 0..n-1 via the antipodal identification i ~ i+n/2 with sign flip
// (zeta^{i+n/2} = -zeta^i). a sends position i -> (a*i) mod n, folding into [0,n/2) with sign.
fn act(vec:&[i64], a:u64, n:usize)->Vec<i64>{
    let half=n/2;
    let mut out=vec![0i64;half];
    for i in 0..half {
        if vec[i]!=0 {
            let j=((i as u64 * a) % (n as u64)) as usize;
            if j<half { out[j]+=vec[i]; } else { out[j-half]-=vec[i]; }
        }
    }
    out
}
fn neg(vec:&[i64])->Vec<i64>{ vec.iter().map(|&x|-x).collect() }

fn units(n:u64)->Vec<u64>{ (1..n).filter(|&a| gcd(a,n)==1).collect() }
fn gcd(a:u64,b:u64)->u64{ if b==0 {a} else {gcd(b,a%b)} }

// Enumerate all antipodal-free signed configs of weight EXACTLY w (a[0] may be 0; we enumerate
// over choices of w positions in [0,half) with signs, fixing sign of the lowest chosen pos = +1 to
// kill the global negation -- the Galois orbit closure includes negation so we count true orbits).
// For each, compute norm; collect spurious set (p|N, N!=0). Then count Galois orbits (under (Z/n)^*
// and negation). Return (#spurious, #orbits, orbit_sizes_distinct, phi).
fn orbit_count(n:u64, p:u64, w:usize)->(u64,u64,Vec<usize>,u64){
    let d=(n/2) as usize;
    let us=units(n);
    let phi=us.len() as u64;
    // collect spurious vectors
    let mut spur:std::collections::HashSet<Vec<i64>>=std::collections::HashSet::new();
    let mut a=vec![0i64;d];
    // recursive: choose subset of size w from positions 0..d with signs; canonicalize by fixing the
    // first nonzero to +1 (so each {v,-v} pair appears once) -- we just store both v and -v? No:
    // store v as-is, dedup happens in orbit closure. Enumerate ALL sign patterns (2^w), all subsets.
    fn rec(a:&mut Vec<i64>, pos:usize, d:usize, left:usize, p:u64,
           spur:&mut std::collections::HashSet<Vec<i64>>){
        if left==0 {
            let nv=norm_exact(a,d);
            if nv!=0 && (nv.unsigned_abs() % (p as u128))==0 {
                spur.insert(a.clone());
            }
            return;
        }
        if pos>=d || d-pos<left { return; }
        // skip pos
        rec(a,pos+1,d,left,p,spur);
        // take pos with +1 then -1
        a[pos]=1;  rec(a,pos+1,d,left-1,p,spur);
        a[pos]=-1; rec(a,pos+1,d,left-1,p,spur);
        a[pos]=0;
    }
    rec(&mut a,0,d,w,p,&mut spur);
    let total=spur.len() as u64;
    // count orbits under G=(Z/n)^* and negation
    let mut seen:std::collections::HashSet<Vec<i64>>=std::collections::HashSet::new();
    let mut orbits=0u64;
    let mut sizes:std::collections::BTreeSet<usize>=std::collections::BTreeSet::new();
    for v in spur.iter() {
        if seen.contains(v) { continue; }
        let mut orb:std::collections::HashSet<Vec<i64>>=std::collections::HashSet::new();
        for &au in &us {
            let av=act(v,au,n as usize);
            orb.insert(av.clone());
            orb.insert(neg(&av));
        }
        // intersect with spur set (only count the real spurious members of the orbit)
        let mut realsz=0usize;
        for ov in orb.iter() {
            if spur.contains(ov) { seen.insert(ov.clone()); realsz+=1; }
        }
        orbits+=1; sizes.insert(realsz);
    }
    (total,orbits,sizes.into_iter().collect(),phi)
}

fn dfact(k:i64)->f64{ let mut r=1.0; let mut x=k; while x>=1 {r*=x as f64; x-=2;} r } // (2r-1)!!

// Total weight-<=W orbit count at a single prime (sum over w=2..W of O_w), plus per-w breakdown.
fn oband_at(n:u64,p:u64,wmax:usize)->(u64,Vec<u64>){
    let mut ob=0u64; let mut per=vec![];
    for w in 2..=wmax { let (_t,o,_s,_ph)=orbit_count(n,p,w); ob+=o; per.push(o); }
    (ob,per)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let _maxw:usize = if args.len()>1 { args[1].parse().unwrap() } else { 6 };
    println!("# wf-A05: GALOIS-ORBIT COUNT O_w(n,p) of spurious relations, prize regime beta=4.");
    println!("# Open residual of _wfS7_galois_spread: K bounded <=> O_band(n,p) <= THR_r(n)=(2r-1)!! n^(r-1).");
    println!("# (each spurious weight w<=2r contributes to depth r; phi(n)=n/2 cancels half of n^r.)\n");

    // ---- PART 0: VERIFY the free-action law + orbit count at the KNOWN witness prime n=64 ----
    println!("## PART 0: free-action cross-check at the _wfS7 witness prime n=64 p=17318209 (beta=4.008):");
    {
        let n=64u64; let p=17318209u64;
        for w in [3usize,4] {
            let (tot,orb,sizes,ph)=orbit_count(n,p,w);
            let ok = tot==orb*ph || tot==0;
            println!("        w={} #spur={:>5} O_w={:>4} phi={} spur==O_w*phi: {}  orbit_sizes={:?}",
                w,tot,orb,ph,if ok {"YES (Lean free-law confirmed)"} else {"NO!"},sizes);
        }
    }

    // ---- PART 1: SWEEP prize primes (p=1 mod n, beta~4), find the WORST (max O_band) per n ----
    // The smallest p>n^4 usually carries NO short spurious; the orbit count is nontrivial only at
    // SOME (structured) primes. We sweep K primes in the band and report the per-prime O_band dist.
    println!("\n## PART 1: SWEEP O_band over prize primes p=1(mod n), p>=n^4 (band weight<=4, r<=2):");
    println!("   n  #primes  maxO_band  worst_p(beta,v2)  #primes_with_spur  THR_2  maxRho");
    for &n in &[16u64,32,64] {
        let plo=(n as f64).powf(4.0) as u64;
        let kprimes = if n<=16 {200} else if n<=32 {120} else {40};
        let wmax = 4usize;
        let mut p=fp(n,plo);
        let mut maxob=0u64; let mut worstp=p; let mut nzcount=0u64; let mut perworst=vec![];
        let mut hist:std::collections::BTreeMap<u64,u64>=std::collections::BTreeMap::new();
        for _ in 0..kprimes {
            let (ob,per)=oband_at(n,p,wmax);
            *hist.entry(ob).or_insert(0)+=1;
            if ob>0 {nzcount+=1;}
            if ob>maxob {maxob=ob; worstp=p; perworst=per;}
            p=fp(n,p+1);
        }
        let thr2=dfact(3)*(n as f64).powf(1.0);
        let beta=(worstp as f64).ln()/(n as f64).ln();
        let v2w=(worstp-1).trailing_zeros();
        println!("  n={:>3} K={:>3} maxO_band={:>4} worst_p={} (beta={:.3},v2={}) #spur_primes={}/{} THR_2={:.0} maxRho={:.4}",
            n,kprimes,maxob,worstp,beta,v2w,nzcount,kprimes,thr2,maxob as f64/thr2);
        print!("       O_band histogram: "); for (k,v) in &hist {print!("[{}:{}]",k,v);} println!();
        if !perworst.is_empty() {
            print!("       worst-prime per-weight orbits: ");
            for (i,o) in perworst.iter().enumerate(){print!("O_{}={} ",i+2,o);} println!();
        }
    }

    // ---- PART 2: WORST-prime threshold ratio rho_2 = maxO_band/THR_2 across n ----
    // Use the WORST (max O_band) prize prime per n (where short spurious actually appear). THR_2 =
    // (2r-1)!! n^{r-1} = 3 n at r=2. K bounded at depth 2 <=> max-over-band-primes O_band <= O(THR_2).
    println!("\n## PART 2: WORST-prime ratio rho_2 = maxO_band(n)/THR_2(n), THR_2 = 3 n  (band w<=4, r=2):");
    println!("   (K bounded at r=2 <=> rho_2 stays BOUNDED across n; grows like power of n => explode)");
    let mut prev:Option<(f64,f64)>=None;   // (log n, log maxO)
    for &n in &[16u64,32,64] {
        let plo=(n as f64).powf(4.0) as u64;
        let kprimes = if n<=16 {400} else if n<=32 {240} else {80};
        let mut p=fp(n,plo);
        let mut maxob=0u64;
        for _ in 0..kprimes { let (ob,_)=oband_at(n,p,4); if ob>maxob {maxob=ob;} p=fp(n,p+1); }
        let thr2=dfact(3)*(n as f64);
        let rho=maxob as f64/thr2;
        let ln_n=(n as f64).ln(); let ln_o=(maxob.max(1) as f64).ln();
        let slope = match prev { Some((pn,po))=> format!(" d ln(maxO)/d ln(n)={:.2}", (ln_o-po)/(ln_n-pn)), None=>String::new() };
        prev=Some((ln_n,ln_o));
        println!("   n={:>3} K={:>3} maxO_band={:>4} THR_2={:.0} rho_2={:.4}{}", n,kprimes,maxob,thr2,rho,slope);
    }

    // ---- PART 3: per-weight max-over-primes O_w growth -- fit O_w ~ n^alpha (explode-vs-bounded) ----
    println!("\n## PART 3: max-over-prime O_w at FIXED weight ~ n^alpha (threshold for K bdd: alpha<=w/2-1):");
    for w in [4usize] {
        print!("   w={}: ", w);
        let mut pts=vec![];
        for &n in &[16u64,32,64] {
            let plo=(n as f64).powf(4.0) as u64;
            let kprimes = if n<=16 {400} else if n<=32 {240} else {80};
            let mut p=fp(n,plo);
            let mut mx=0u64;
            for _ in 0..kprimes { let (_t,o,_s,_ph)=orbit_count(n,p,w); if o>mx {mx=o;} p=fp(n,p+1); }
            pts.push((n as f64, mx as f64));
            print!("n{}:maxO_w={} ", n, mx);
        }
        if pts.len()>=2 {
            let (x0,y0)=pts[0]; let (x1,y1)=*pts.last().unwrap();
            let alpha = if y0>0.0 && y1>0.0 {(y1.ln()-y0.ln())/(x1.ln()-x0.ln())} else {f64::NAN};
            let need = (w as f64)/2.0 - 1.0;
            print!(" => maxO_w~n^{:.2} (need alpha<=n^{:.2}: {})", alpha, need,
                if alpha.is_nan() {"insufficient nonzero data"} else if alpha<=need+0.4 {"OK/bounded"} else {"EXPLODES"});
        }
        println!();
    }
}
