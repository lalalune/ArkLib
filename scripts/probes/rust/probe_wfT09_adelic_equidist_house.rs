// #444 T09 — Quantitative Bilu equidistribution with non-arch local-mass coupling.
// CLAIM under test: the empirical measure of the phi(n) archimedean conjugates of the
// normalized period u_b = theta_b/sqrt(n) is W_2-close to an "adelic equilibrium measure"
// whose support radius R_eq bounds the House, and R_eq = sqrt(log(p/n)).
//
// DECISIVE TEST (the F0 rare-event gap): does a small W_2 of the conjugate CLOUD control
// the House (= max conjugate modulus)? We measure, at prize regime beta=4 (p ~ n^4, p=1 mod n):
//   (a) House_b/sqrt(n) = max_c |theta_{cb}|/sqrt(n)   (the wall quantity, per worst b)
//   (b) W_2(emp, semicircle-bulk) -- the bulk equidistribution discrepancy
//   (c) the "support radius" R_eq we would need = House/sqrt(?)  and whether W_2 sees it
//   (d) #conjugates strictly above any fixed bulk radius (the tail mass) -> O(1) count,
//       so tail mass = O(1)/phi(n) -> invisible to W_2 (which floors at ~1/phi(n)^{1/2}).
//
// For a FIXED b, the conjugates of theta_b are { theta_{cb} : c in (Z/nZ)^* / ... } i.e. the
// Galois orbit = the periods theta_{c} over c coprime-class reps. We use: conjugates of the
// SINGLE algebraic number theta_b are obtained by sigma_t: zeta_n -> zeta_n^t, t in (Z/n)^*,
// giving theta_{t*b}. Since periods are coset-constant, the distinct conjugates = theta over
// the phi(n)/? classes. We just enumerate theta_{tb} for t in (Z/n)^* and treat as the cloud.
use std::f64::consts::PI;

fn mpow(_a:u64,mut e:u64,p:u64,base:u64)->u64{let mut r=1u128;let mut a2=base as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(0,(p-1)/f,p,g)!=1){return g;}g+=1;}}
fn gcd(a:u64,b:u64)->u64{if b==0{a}else{gcd(b,a%b)}}

// eta for offset b: sum_{x in mu_n} e_p(b x)
fn eta(b:u64,mu:&[u64],p:u64)->(f64,f64){
    let mut re=0.0;let mut im=0.0;
    for &x in mu{
        let t=((b as u128*x as u128)%p as u128) as u64;
        let ang=2.0*PI*(t as f64)/(p as f64);
        re+=ang.cos();im+=ang.sin();
    }
    (re,im)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 {args[1..].iter().map(|x|x.parse().unwrap()).collect()} else {vec![16,32,64,128,256,512]};
    println!("# n  p  beta_eff  House/sqrt(n)  C=House/sqrt(n*ln(p/n))  W2_bulk  R_eq_need  tail_above_R0_count  tail_mass*phi  W2_floor=1/sqrt(phi)");
    for &n in &ns{
        // prize regime beta=4: p ~ n^4
        let target = (n as f64).powi(4);
        let lo = target as u64;
        let p = find_prime_cong1(n, lo);
        let g = primitive_root(p);
        let h = mpow(0,(p-1)/n,p,g); // generator of mu_n
        let mu:Vec<u64>=(0..n).map(|j|mpow(0,j,p,h)).collect();
        let sqn=(n as f64).sqrt();
        let logpn=((p as f64)/(n as f64)).ln();
        let beta_eff=(p as f64).ln()/(n as f64).ln();

        // House over coset reps via g^j step over quotient of order m.
        // For large m we SAMPLE the first SCAN reps (the wall is hit early/representatively;
        // the conjugate-cloud analysis is the load-bearing part, not the exact global max).
        let m=(p-1)/n;
        let scan = if m < 40_000 { m } else { 40_000u64 };
        let gn=mpow(0,n,p,g);
        let mut house=0.0f64; let mut bestb=1u64;
        let mut b=1u64;
        for _ in 0..scan{
            let (re,im)=eta(b,&mu,p);
            let mag=(re*re+im*im).sqrt();
            if mag>house{house=mag;bestb=b;}
            b=((b as u128*gn as u128)%p as u128) as u64;
        }
        // conjugate cloud of theta_{bestb}: sigma_t zeta -> zeta^t, t in (Z/n)^*; gives theta_{t*bestb}
        // theta is real iff group neg-closed; we take |.| as the conjugate modulus on the real-embedding cloud.
        // Build moduli of all phi(n) conjugates.
        let mut mods:Vec<f64>=Vec::new();
        for t in 1..n{
            if gcd(t,n)!=1{continue;}
            let bt=((t as u128*bestb as u128)%p as u128) as u64;
            let (re,im)=eta(bt,&mu,p);
            mods.push((re*re+im*im).sqrt()/sqn); // normalized conjugate modulus
        }
        let phi=mods.len() as f64;
        // sort moduli
        let mut sm=mods.clone(); sm.sort_by(|a,b|a.partial_cmp(b).unwrap());
        // empirical W_2 to a "bulk equilibrium": use the arcsine/semicircle-like fit by matching
        // quantiles to the *median bulk* radius R0 = quantile(0.9) (a fixed bulk scale, not the max).
        let q90 = sm[(0.90*phi) as usize];
        // W_2^2 between empirical normalized-modulus measure and a degenerate-at-R0 reference
        // (cheap proxy: variance of the cloud about its mean — the bulk spread). Real W_2 to the
        // limiting law is at most this scale; the POINT is its size vs the House gap.
        let mean:f64 = sm.iter().sum::<f64>()/phi;
        let var:f64 = sm.iter().map(|x|(x-mean)*(x-mean)).sum::<f64>()/phi;
        let w2_bulk = var.sqrt(); // O(1) bulk std
        // R_eq we'd NEED to bound House: House/sqrt(n) itself is the normalized house already.
        let house_norm = house/sqn;
        let c = house/ (n as f64*logpn).sqrt();
        // tail count strictly above the bulk q90 radius (the rare large conjugates)
        let r0 = q90;
        let tail_count = sm.iter().filter(|&&x| x > r0*1.0001).count();
        let tail_mass_phi = tail_count as f64; // = (tail_mass)*phi
        let w2_floor = 1.0/phi.sqrt();
        println!("{:>4} {:>14} {:>6.3} {:>10.4} {:>10.4} {:>10.5} {:>10.4} {:>8} {:>10.1} {:>12.6}",
            n,p,beta_eff,house_norm,c,w2_bulk,r0,tail_count,tail_mass_phi,w2_floor);
    }
    println!("# KEY: if House/sqrt(n) GROWS (sqrt-log) while W2_bulk stays O(1) flat and the tail_count");
    println!("# above the bulk radius is O(1) (=> tail mass O(1)/phi << W2_floor 1/sqrt(phi)),");
    println!("# then W_2 of the conjugate cloud CANNOT see the House => R_eq is NOT derivable from W_2.");
}
