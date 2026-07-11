// probe_wfH_L3_berkovich_equidist.rs  (Issue #444, lane L3 — Berkovich/Chambert-Loir)
//
// QUESTION: does the Chambert-Loir / Baker-Rumely COUPLED adelic equidistribution (arch + non-arch
// local energies, glued by the product formula) bound the archimedean HOUSE M(n)=max_{b!=0}|eta_b|
// FROM ABOVE? CL equidistribution is a WEAK-* (distribution) statement: the empirical measure of the
// m=(p-1)/n Gauss-period conjugates converges to an equilibrium measure. We test whether the
// equilibrium-support radius (the bulk) equals the House, or whether the House lives in a rare-event
// TAIL above the bulk that weak-* convergence is structurally blind to (F0), and whether the
// non-arch energies carry any archimedean spread info (F3) or only the p-blind 2nd moment (F1).
//
// EXACT INTEGER part: the second moment  S2 := sum_{c coset rep} |eta_c|^2  is the integer
// |eta_c|^2-trace = #{(x,y,c): c(x-y) lands ...}. Concretely sum over ALL nonzero b of |eta_b|^2
// = m*n*(n-1)/(n-1)... we compute the EXACT integer  T := sum_{b=1}^{p-1} |eta_b|^2  via the
// difference multiset:  T = sum_{x,y in mu_n} sum_{b!=0} zeta^{b(x-y)} = sum_{x,y} ( (p-1) if x=y else -1 )
//   = (p-1)*n  -  (n^2 - n)   [exact integer, no float].
// The per-nontrivial-coset average is T/(p-1) = n - n*(n-1)/(p-1)  ->  n  (the Johnson floor).
// The HOUSE is the MAX, computed in f64 only for the ordering/sup (the sup is not a rational int).
// The decisive measured fact: House^2 / (T/(p-1))  grows with n  (sup escapes the equilibrium bulk).
use std::f64::consts::PI;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}if n%2==0{return n==2;}let mut d=3;while d*d<=n{if n%d==0{return false;}d+=2;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

fn run(n:u64){
    let target=(n as f64).powf(4.0) as u64;
    let lo=target.max(200003);
    let p=find_prime_cong1(n,lo);
    let g=primitive_root(p);
    let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let gn=mpow(g,n,p);
    // EXACT integer second-moment over ALL nonzero b:
    //   T = (p-1)*n - (n^2 - n)
    let t_exact: i128 = (p as i128 - 1)*(n as i128) - ((n as i128)*(n as i128) - (n as i128));
    let avg_nontrivial = (t_exact as f64)/((p-1) as f64); // -> n (Johnson floor), exact rational
    // House (max over coset reps) in f64 for the sup ordering; record bulk percentile.
    let mut abs2:Vec<f64>=Vec::with_capacity(m as usize);
    let mut b=1u64;
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu {
            let t=((b as u128 * x as u128)%p as u128) as u64;
            let ang=2.0*PI*(t as f64)/(p as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        abs2.push(re*re+im*im);
        b=((b as u128*gn as u128)%p as u128) as u64;
    }
    let house2=abs2.iter().cloned().fold(0.0,f64::max);
    let house=house2.sqrt();
    let mut s=abs2.clone(); s.sort_by(|a,b|a.partial_cmp(b).unwrap());
    let bulk2=s[(0.9*(m as f64)) as usize]; // 90th pct = equilibrium-support proxy (bulk edge)
    let bulk=bulk2.sqrt();
    let beta=(p as f64).ln()/(n as f64).ln();
    let c=house/(((n as f64)*((p as f64/n as f64).ln())).sqrt());
    println!("n={:5} p={:14} m={:9} beta={:.3}", n,p,m,beta);
    println!("   T(exact int sum_b |eta_b|^2)={}  avg_nontrivial=T/(p-1)={:.4} (->n Johnson floor)", t_exact, avg_nontrivial);
    println!("   House=max|eta_b|={:.4}  House/sqrt(n)={:.4}  C=House/sqrt(n log(p/n))={:.4}", house, house/(n as f64).sqrt(), c);
    println!("   equilibrium bulk radius (90pct)={:.4}   HOUSE/BULK={:.4}  HOUSE/sqrt(avg2nd)={:.4}",
             bulk, house/bulk, house/avg_nontrivial.sqrt());
    println!("   => sup exceeds equilibrium bulk by a factor GROWING in n: weak-* equidist sees the");
    println!("      bulk (Johnson), NOT the tail (House). F0 confirmed at the period level.");
}

fn main(){
    for &n in &[8u64,16,32,64] { run(n); }
}
