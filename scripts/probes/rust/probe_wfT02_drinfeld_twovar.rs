// probe_wfT02_drinfeld_twovar.rs  (#444 T02)
// Test the Drinfeld two-variable partial-Frobenius decoupling claim.
//
// Object: T(b,t) = sum_{x in mu_n} e_p(b x + t x^g),  g | n a fixed dilation exponent.
// Diagonal restriction t=0:  T(b,0) = eta_b  (the prize object).
// CLAIM (T02): the diagonal sup  max_b |T(b,0)| = M(n)  is BOUNDED BY an
// off-diagonal-decoupled Deligne bound that does NOT pay the rank-n of the diagonal.
//
// The honest test of "diagonal collapse" (T02's own stated danger):
//   (1) does the 2-D family have a controlling L^2 scale (= conductor/rank) SMALLER than n?
//       -> compute  (1/(p-1)^2) sum_{b,t != 0} |T(b,t)|^2   (the 2-D second moment).
//   (2) is the DIAGONAL sup  max_b |T(b,0)|  actually <= the 2-D sup  max_{b,t} |T(b,t)| ?
//   (3) is the 2-D sup itself smaller than the diagonal sup, or does the diagonal
//       saturate the family (collapse)?
//   (4) is x^g (g | n) just a re-indexing of mu_n (so T(b,t)=eta-of-mixed-frequency)?
//
// Run:  rustc -O probe_wfT02_drinfeld_twovar.rs -o /tmp/t02 && /tmp/t02

fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;
    while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2u64;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}
    let mut g=2u64;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}

fn main(){
    use std::f64::consts::PI;
    // sub-prize-scale but BETA=4 generic (exhaustive over b,t needs p^2 work, so keep n,p modest)
    for &mu in &[3u32,4] {
        let n = 1u64<<mu;
        let p = fp(n,(n as f64).powf(4.0) as u64);     // beta=4
        let g  = proot(p);
        let h  = mpow(g,(p-1)/n,p);                      // generator of mu_n
        let muv:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        // dilation exponent gd | n, nontrivial automorphism x -> x^gd of mu_n.
        // For mu_n (cyclic order n=2^mu) the maps x->x^gd with gcd(gd,n)=1 PERMUTE mu_n
        // (a re-indexing); with gd | n and gd>1 they are ENDO (collapse onto mu_{n/gd}).
        let gd:u64 = 2;  // x -> x^2  : the squaring (2-to-1 onto mu_{n/2})

        // ---- 1-D diagonal sup  M(n) = max_{b!=0} |eta_b| ----
        let mut mdiag=0.0f64;
        for b in 1..p {
            let mut re=0.0;let mut im=0.0;
            for &x in &muv{let t=((b as u128*x as u128)%p as u128)as u64;let a=2.0*PI*(t as f64)/p as f64;re+=a.cos();im+=a.sin();}
            let v=(re*re+im*im).sqrt(); if v>mdiag{mdiag=v;}
        }
        // x^gd cache
        let xg:Vec<u64>=muv.iter().map(|&x|mpow(x,gd,p)).collect();

        // ---- 2-D family: sup and second moment over (b,t), b,t in 0..p (skip b=t=0) ----
        let mut m2d=0.0f64;        // sup over all (b,t)
        let mut m2d_off=0.0f64;    // sup over t!=0 (genuinely 2-D, off the diagonal)
        let mut sm:f64=0.0;        // sum |T(b,t)|^2 over (b,t)!=(0,0)
        let mut cnt:u64=0;
        for b in 0..p {
            for t in 0..p {
                if b==0 && t==0 {continue;}
                let mut re=0.0;let mut im=0.0;
                for k in 0..muv.len(){
                    let phase=((b as u128*muv[k] as u128 + t as u128*xg[k] as u128)%p as u128)as u64;
                    let a=2.0*PI*(phase as f64)/p as f64; re+=a.cos(); im+=a.sin();
                }
                let v2=re*re+im*im; sm+=v2; cnt+=1;
                let v=v2.sqrt();
                if v>m2d{m2d=v;}
                if t!=0 && v>m2d_off{m2d_off=v;}
            }
        }
        let sm2 = sm/(cnt as f64);  // average |T|^2 over the family (= controlling L^2 scale)
        let logpn = (p as f64 / n as f64).ln();
        println!("mu={} n={} p={} | M(n)diag={:.3}  M_2Dfamily={:.3}  M_2Doff={:.3}",
            mu,n,p,mdiag,m2d,m2d_off);
        println!("   avg|T|^2 over (b,t) family = {:.3}  (rank/conductor proxy; n={})", sm2, n);
        println!("   M(n)/sqrt(n*log(p/n)) = {:.3}   M_2D/sqrt(n*log(p/n)) = {:.3}",
            mdiag/(n as f64*logpn).sqrt(), m2d/(n as f64*logpn).sqrt());
        println!("   DIAGONAL-COLLAPSE TEST: is diag sup == family sup? {}  (M2D-Mdiag={:.4})",
            (m2d-mdiag).abs()<1e-6, m2d-mdiag);
        println!();
    }
    println!("Interpretation: if avg|T|^2 ~ n and M_2D ~ M(n)diag (no shrinkage),");
    println!("the 2-D family inherits the SAME rank-n floor; the diagonal does NOT escape.");
}
