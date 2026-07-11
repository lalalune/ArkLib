// wf-C1: direct measurement of the M1 SPURIOUS excess  Spur_r(p) = E_r(p) - E_r^{(0)}  at the
// ACTUAL prize prime, at BAND depth r > beta, in the NONPRINCIPAL reframing.
//
// Identity (substrate SubgroupGaussSumRawMoment):  sum_{b in F_p^*} eta_b^{2r} = p * E_r(p),
// where E_r(p) = #{2r-tuples (x_1..x_{2r}) in mu_n^{2r} : sum (-1)^? x = 0 ... } actually the raw
// 2r-th moment of the period. The char-0 (Lam-Leung antipodal) count is E_r^{(0)} = (2r-1)!! n^r.
// The spurious excess is Spur_r(p) = E_r(p) - E_r^{(0)} >= 0 (char-p only ADDS coincidences).
//
// NONPRINCIPAL reframing: exclude the principal frequency b=0 (eta_0 = n, gives n^{2r}/p blow-up
// past r>beta). Define  E_r'(p) = (1/p) sum_{b!=0} eta_b^{2r}. We measure:
//   (a) Spur'_r := E_r'(p) - E_r^{(0)}        [the nonprincipal spurious excess]
//   (b) ratio Spur'_r / E_r^{(0)}             [= eps in (S-M1); M1 needs this <= O(1)]
//   (c) at band depth r in [beta, 1.36 n]     [the actual needed range]
// Reconcile with K1: char-0 substrate says E_r^{(0)} is EXACT over Z; any char-p excess is Spur.
//
// We compute eta_b EXACTLY?? No -- eta_b is a real algebraic number, sum of cos. We compute the
// MOMENT sum_{b!=0} eta_b^{2r} in f64 (the periods are O(sqrt n) so eta^{2r} <= n^r, summable),
// and compare to the EXACT char-0 integer (2r-1)!! n^r. The excess is the char-p contamination.
use std::f64::consts::PI;
fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn run(n:u64,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n; let gn=mpow(g,n,p);
    let mut eta=Vec::with_capacity(m as usize); let mut b=1u64;
    for _ in 0..m { let mut re=0.0; for &x in &mu{let t=((b as u128*x as u128)%p as u128)as u64;re+=(2.0*PI*(t as f64)/p as f64).cos();} eta.push(re); b=((b as u128*gn as u128)%p as u128)as u64; }
    let beta=(p as f64).ln()/(n as f64).ln();
    // identify the principal coset rep: eta_b == n (b in mu_n, i.e. b a power of h -> the coset of 1)
    println!("== wf-C1 SPUR' band-depth: n={} p={} m={} beta={:.2} (band r in [{:.0}, {:.0}]) ==",
        n,p,m,beta, beta.ceil(), 1.36*n as f64);
    println!("   r    E_r'(p)        E_r^(0)=char0     Spur'_r/char0=eps   note");
    for r in 1..=rmax {
        let mut s=0.0; let mut maxe=0.0f64;
        for &e in &eta { if e>maxe {maxe=e;} if (e-n as f64).abs()>0.5 { s += e.powi(2*r as i32); } }
        // s = sum over NONprincipal cosets of eta^{2r}. But each coset rep counts the whole coset
        // orbit once; the moment identity sums over ALL b in F_p^*, which is n copies of each coset
        // (eta is coset-constant). So sum_{b!=0} eta_b^{2r} = n * sum_{coset reps != principal-coset} eta^{2r}
        //  ... actually we must include ALL nonprincipal b. eta is constant on cosets of mu_n. There
        // are m cosets, each of size n. The principal frequency b=0 is NOT a coset (it's 0). So
        // "b != 0" = all p-1 nonzero b = n * (sum over m coset reps). The coset of eta=n is the coset
        // of b in mu_n^perp... we exclude the PRINCIPAL b=0 only (eta_0 would be n but b=0 isn't in F_p^*).
        // The reframing's "exclude principal" excludes the coset where eta_b = n (b s.t. mu_n in ker).
        let er = (n as f64 * s)/(p as f64);
        let c0 = dfact(r)*(n as f64).powi(r as i32);
        let eps = (er-c0)/c0;
        let band = if (r as f64)>=beta {" <-- BAND (r>beta)"} else {""};
        println!("  {:3}  {:13.4}  {:14.4}    {:+.4}          {}", r, er, c0, eps, band);
    }
    println!("   (max nonprincipal eta = {:.3}, principal = n = {})", eta.iter().cloned().filter(|&e|(e-n as f64).abs()>0.5).fold(0.0f64,f64::max), n);
}
fn main(){
    run(16, fp(16,60000), 16);
    run(32, fp(32,1000000), 22);
    run(64, fp(64,16000000), 28);
}
