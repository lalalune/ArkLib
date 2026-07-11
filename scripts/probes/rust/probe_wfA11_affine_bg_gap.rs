// A11 pre-screen: Bourgain-Gamburd / superstrong-approximation spectral gap for the
// MULTIPLICATIVE dilation action of mu_n on F_p, packaged as the affine group
//   G = F_p rtimes mu_n  (the natural non-abelian envelope of the dilation action).
//
// Lindenstrauss-Varju (AFST 2016, "Spectral gap in the group of affine transformations
// over prime fields"), Theorem 1: for the affine group F_p^d rtimes SL_d(F_p),
//   gap_affine  >=  c_d * min{ gap(SL_d(F_p), S'),  |S|^{-1} }.
// The dilation action of mu_n is the d=1 case with LINEAR PART mu_n <= F_p^* ABELIAN
// (SL_1 = {1}); BG Theorem A needs a Zariski-dense subgroup of a PERFECT (non-abelian)
// group SL_d, d>=2. So the LV/BG envelope gives gap = 0 for the abelian torus.
//
// This probe verifies the two consequences at prize scale (beta=4, p ~ n^4):
//  (1) AFFINE NON-CONCENTRATION = M(n) (circular). The L2 mass of one step of the
//      affine additive part, equivalently the second-largest singular value of the
//      averaging operator restricted to additive characters, is governed EXACTLY by
//      hat{u}(b) = eta_b / n where u = uniform measure on mu_n. So
//         max_{b!=0} |hat{u}(b)| = M(n)/n,
//      and the BG "Fourier-flatness / non-concentration" input IS the prize object.
//      We print M(n)/n and M(n) so the circularity is exact (no new control).
//  (2) LINEAR-PART (mu_n) ABELIAN GAP. The Cayley graph of the ABELIAN quotient
//      F_p^*/mu_n-acting / the torus has eigenvalues = additive characters; the
//      relevant "linear-part spectral gap" for ANY symmetric generating set of the
//      abelian group mu_n itself is 1 - cos(2 pi / n) -> 0 (no UNIFORM gap as n grows),
//      so min{gap_lin, ...} -> 0 in LV Thm 1: BG cannot fire. We print the best
//      possible abelian gap for mu_n (cyclic, standard generators) to show it -> 0.
use std::f64::consts::PI;

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{v+=1;x>>=1;}v}

// M(n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(b x).  (= mn_wall)
fn measure_M(n:u64,p:u64)->f64{
    let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let m=(p-1)/n;
    let mut best=0.0f64;
    let mut b=1u64; let gn=mpow(g,n,p);
    for _ in 0..m {
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu {
            let t=((b as u128 * x as u128)%p as u128) as u64;
            let ang=2.0*PI*(t as f64)/(p as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        let mag=(re*re+im*im).sqrt();
        if mag>best{best=mag;}
        b=((b as u128*gn as u128)%p as u128) as u64;
    }
    best
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() }
                     else { vec![16,32,64,128,256,512] };
    eprintln!("# A11: affine F_p rtimes mu_n (dilation) -- BG/superstrong screen, beta~4");
    eprintln!("# n  v2  p  M=M(n)  M/n=|hat u|max  M/sqrt(n)  abelian_gap_mu_n(=1-cos(2pi/n))  c=M/sqrt(n ln(p/n))");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let mut lo=target.max(200003);
        // one representative prize prime (beta~4); pick high-v2 (worst, structured) too
        let mut found=0; let mut seen_v2=std::collections::HashSet::new();
        while found<2 {
            let p=find_prime_cong1(n, lo);
            let vv=v2(p-1);
            if !seen_v2.contains(&vv)||found<1 {
                let mm=measure_M(n,p);
                let abelian_gap = 1.0 - (2.0*PI/(n as f64)).cos(); // best uniform gap of cyclic mu_n
                let beta=(p as f64).ln()/(n as f64).ln();
                let c=mm/(((n as f64)*((p as f64/n as f64).ln())).sqrt());
                eprintln!("{:5} {:3} {:>14} {:9.3} {:8.5} {:7.3} {:12.6} {:7.4} (beta={:.2})",
                    n, vv, p, mm, mm/(n as f64), mm/(n as f64).sqrt(), abelian_gap, c, beta);
                seen_v2.insert(vv); found+=1;
            }
            lo=p+1;
        }
    }
    eprintln!("# READ: |hat u|_max = M/n is the affine non-concentration input (BG Fourier-flatness).");
    eprintln!("#       It EQUALS the prize object / n -> the affine route is circular, no new control.");
    eprintln!("#       abelian_gap_mu_n -> 0 as n grows: LV Thm 1 min{{gap_lin,...}}=0 -> BG cannot fire.");
}
