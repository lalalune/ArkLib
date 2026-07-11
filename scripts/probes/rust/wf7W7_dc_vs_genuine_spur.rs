// wf-W7b: SEPARATE the DC contribution from the genuine (1-zeta_p)-adic spurious mass.
//
// The DC-subtracted moment is  A_r = E_r(p) - n^{2r}/p.   Char-0 floor E_r^{(0)} <= (2r-1)!! n^r (Wick).
// W7b decomposes the char-p excess into TWO parts to locate where the slope-0 vs slope->=1 mass sits:
//
//   Spur_r := E_r(p) - E_r^{(0)}                  (total char-p excess over char-0)
//   DC_r   := n^{2r}/p                            (the principal/DC term, subtracted in A_r)
//   GEN_r  := A_r - E_r^{(0)} = E_r(p) - n^{2r}/p - E_r^{(0)} = Spur_r - DC_r
//
// GEN_r is the GENUINE post-DC spurious mass = the (1-zeta_p)-adic positive-slope segment count of the
// NORM polynomial AFTER the DC (slope-0 principal) segment is removed.  The NP picture:
//   - slope-0 (principal) segment = the DC term n^{2r}/p  (all-equal / constant configs through 0 mod p).
//   - slope->=1 segments = GEN_r, the genuine antipodal-free configs that vanish mod p.
// (S-W7) SHARP:  GEN_r = A_r - Wick_floor  <= (K^r - 1)(2r-1)!! n^r,  i.e.  A_r <= K^r Wick.
// We test whether GEN_r is SMALL (<=0 ideally) at band depth -- i.e. whether the DC term ALONE
// accounts for essentially all of Spur_r, so that A_r <= E_r^{(0)} <= Wick (=> K=1 transfer, PRIZE).
//
// We print, EXACT, the sign and ratio of GEN_r := A_r - E_r^{(0)} at band depth.  GEN_r <= 0 at r*
// would mean A_r <= Wick literally (K=1).  We track the cross-over.
// build: rustc -O wf7W7_dc_vs_genuine_spur.rs -o /tmp/w7b
use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn e_modp(mu:&[u64],r:usize,p:u64)->u128{
    let mut d:HashMap<u64,u128>=HashMap::new();d.insert(0,1);
    for _ in 0..r{let mut nd:HashMap<u64,u128>=HashMap::new();for(&s,&c)in &d{for &x in mu{let t=((s as u128+x as u128)%p as u128)as u64;*nd.entry(t).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&_s,&c)in &d{t+=c*c;}t
}
fn e_charzero(n:usize,r:usize)->u128{
    use std::f64::consts::PI;
    let cs:Vec<(f64,f64)>=(0..n).map(|e|((2.0*PI*e as f64/n as f64).cos(),(2.0*PI*e as f64/n as f64).sin())).collect();
    let scale=1e7;
    let mut d:HashMap<(i64,i64),u128>=HashMap::new();d.insert((0,0),1);
    for _ in 0..r{let mut nd:HashMap<(i64,i64),u128>=HashMap::new();
        for(&(kr,ki),&c)in &d{for &(cr,ci) in &cs{let nr=((kr as f64/scale+cr)*scale).round() as i64;let ni=((ki as f64/scale+ci)*scale).round() as i64;*nd.entry((nr,ni)).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&(_kr,_ki),&c)in &d{t+=c*c;}t
}
fn main(){
    println!("# wf-W7b DC vs genuine spurious mass.  GEN_r = A_r - E_r^0 = Spur_r - n^{{2r}}/p");
    println!("# n beta p r  Spur_r  DC=n^2r/p  GEN=A_r-E0  GEN/Wick  A_r/Wick  sign(GEN)");
    for &n in &[16usize,32,64]{
        for &beta in &[3.0f64,4.0,5.0]{
            let target=(n as f64).powf(beta);
            let p=fp(n as u64, target as u64);
            let g=proot(p);let h=mpow(g,(p-1)/n as u64,p);
            let mu:Vec<u64>=(0..n as u64).map(|j|mpow(h,j,p)).collect();
            let lnq=(p as f64).ln();
            let rstar=(lnq/2.0).round().max(2.0) as usize;
            let rmax=(rstar+2).min(11);
            for r in 2..=rmax{
                let emp=e_modp(&mu,r,p) as f64;
                let e0=e_charzero(n,r) as f64;
                let dc=(n as f64).powf(2.0*r as f64)/p as f64;
                let ar=emp-dc;
                let spur=emp-e0;
                let gen=ar-e0; // = spur - dc
                let wick=dfact(r)*(n as f64).powi(r as i32);
                let band=if r==rstar{" <-r*"}else{""};
                println!("{:3} {} {:>11} {:2}  {:>13.3e} {:>13.3e} {:>13.3e}  {:>10.3e} {:>8.4} {:>4}{}",
                    n,beta as i32,p,r,spur,dc,gen,gen/wick,ar/wick,if gen>0.0{"+"}else{"-"},band);
            }
            println!();
        }
    }
}
