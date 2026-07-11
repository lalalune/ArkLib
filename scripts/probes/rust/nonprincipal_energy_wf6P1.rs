// P1: CRUX check. Exact identity: sum_{b!=0} eta_b^{2r} = q*E_r - n^{2r}.
// E_r = char-p additive energy = N0(G,2r)/... measured as (1/q) sum_b eta_b^{2r}.
// QUESTION: is char-p E_r <= (2r-1)!! n^r  (char-0 bound)?  If YES the subtraction route
// directly gives sum_{b!=0} <= q*char0 - n^{2r}, and at r~ln q this is the prize.
// We compute eta_b exactly for ALL b in F_p (integer Gauss periods? no - real cos sums).
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let _=&mut a;let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    // eta_b for representative b over each coset; period value repeats n times among b!=0
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let beta=(p as f64).ln()/(n as f64).ln();
    let lnq=(p as f64).ln();
    println!("== n={} p={} m={} beta={:.2} lnq={:.1} ==", n,p,m,beta,lnq);
    println!("  r |  E_r(charp)/char0  | sum_{{b!=0}} / (q*char0)  | (q*char0 - n^2r >0?) | route_ok");
    for r in 1..=rmax {
        // full sum over ALL b in F: principal eta_0=n contributes n^{2r}; each nonzero coset value repeats n times
        let mut snz=0.0; for &e in &eta { snz += e.powi(2*r as i32); } // sum over m distinct period values
        let sum_bnz = (n as f64)*snz; // each value repeats n times over b!=0  -- WAIT: m cosets * n = p-1 values? check
        // actually nonzero b: (p-1) of them, grouped into m cosets each size n. eta_b constant on cosets. so sum_{b!=0} = n * sum_{cosets} eta^{2r} = n*snz. yes.
        let principal = (n as f64).powi(2*r as i32);
        let full = sum_bnz + principal; // = q * E_r
        let er = full/(p as f64);
        let c0 = dfact(r)*(n as f64).powi(r as i32);
        let ratio_full = er/c0;
        let ratio_nz = sum_bnz/((p as f64)*c0);
        let rhs = (p as f64)*c0 - principal; // q*char0 - n^{2r}
        let route_ok = sum_bnz <= rhs; // i.e. E_r <= char0
        println!("  {:3}|  {:14.4}   |  {:18.6}     |  {:14.3e}  |  {}", r, ratio_full, ratio_nz, rhs, route_ok);
    }
}
fn main(){
    run(16, fp(16,60000), 16);
    run(32, fp(32,1000000), 20);
    run(64, fp(64,16000000), 24);
}

// === LANE wf-P1 VERDICT (exact numerics, p=Theta(n^4), depth r up to 1.5 ln q) ===
// FULL char-p E_r / [(2r-1)!! n^r]: EXCEEDS 1 past r>beta (peak 6.31x @ n=32,r=16;
//   >1.1e6x @ n=64,r=24)  => char-0 bound does NOT transfer to full E_r; literal P1 REFUTED.
// NONPRINCIPAL E_r' = E_r - n^{2r}/q : sub-char-0 for ALL r (sup at r=1 = n - n^2/q < n;
//   decays to <1e-3 at r~ln q) for n=16,32,64,128 => the FULL-E_r blowup is ENTIRELY the
//   isolated principal term n^{2r}; the P1 insight holds in PRINCIPAL-SUBTRACTED form.
// Moment bound (q E_r')^{1/2r} min over r: /prize = 1.28->1.42 (n=16->128); ground truth
//   max|eta|/prize = 1.15->1.29. Route gives prize with C ~ 1.42.
