// wf-P2: WHY is char-p A_r <= char-0 despite spurious non-antipodal zero-sums mod p?
// Decompose A_r = (antipodal zero-sums) + (spurious non-antipodal zero-sums mod p).
// And char-0 count C0_r = zeroSumCount over Z = exactly antipodal matchings count.
// Claim to test: over Z (char-0), antipodal zero-sum count = char0? NO - char0=(2r-1)!!n^r is an
//   UPPER BOUND (Lam-Leung), the actual antipodal count A_r^Z <= char0. And A_r^modp = A_r^Z + spur.
// So A_r^modp <= char0 means spur <= char0 - A_r^Z. Measure all three exactly for small n,r.
// Brute force over Z: count 2r-tuples in mu_n (as integers in exponent? no, roots are complex).
// Over Z: zero-sum means sum of the actual roots of unity = 0 in C. Count via FFT/exact rational? 
// Simpler: zero-sum over C of roots zeta_n^{e_i}. We brute small cases (n<=8, r<=4) exactly using
// the fact sum zeta^{e_i}=0 iff the multiset of exponents is a union of regular n/d-gons (for n=2^a, only antipodal pairs at the 2-level... actually full vanishing-sum structure).
// Pragmatic: count over Z numerically with tight tolerance, count over F_p exactly, compare.
use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn add_e_modp(mu:&[u64],r:usize,p:u64)->u128{let mut d:HashMap<u64,u128>=HashMap::new();d.insert(0,1);
 for _ in 0..r{let mut nd:HashMap<u64,u128>=HashMap::new();for(&s,&c)in &d{for &x in mu{let t=((s as u128+x as u128)%p as u128)as u64;*nd.entry(t).or_insert(0)+=c;}}d=nd;}
 let mut t:u128=0;for(&s,&c)in &d{let ns=((p-s)%p)as u64;if let Some(&c2)=d.get(&ns){t+=c*c2;}}t}
// zero-sum over C (char 0): exponents in 0..n, sum of zeta_n^{e_i} == 0. Count 2r-tuples.
fn add_e_charzero(n:usize,r:usize)->u128{
    use std::f64::consts::PI;
    let cs:Vec<(f64,f64)>=(0..n).map(|e|(2.0*PI*e as f64/n as f64).cos()).zip((0..n).map(|e|(2.0*PI*e as f64/n as f64).sin())).collect();
    // distribution of (re,im) sum of r elements, keyed by rounded coords (exact since algebraic, but use fine round)
    let scale=1e6;
    let mut d:HashMap<(i64,i64),u128>=HashMap::new();d.insert((0,0),1);
    for _ in 0..r{let mut nd:HashMap<(i64,i64),u128>=HashMap::new();
        for(&(kr,ki),&c)in &d{for &(cr,ci) in &cs{let nr=((kr as f64/scale+cr)*scale).round() as i64;let ni=((ki as f64/scale+ci)*scale).round() as i64;*nd.entry((nr,ni)).or_insert(0)+=c;}}d=nd;}
    // zero-sum 2r-tuples: pair r-sum s with r-sum -s
    let mut t:u128=0;for(&(kr,ki),&c)in &d{if let Some(&c2)=d.get(&(-kr,-ki)){t+=c*c2;}}t
}
fn main(){
    println!("  n  r   A_r^Z(char0 exact)  char0=(2r-1)!!n^r  A_r^modp   spur=modp-Z   (char0 - A_r^Z)");
    for &n in &[4usize,8,16] {
        let p=fp(n as u64,(n as f64).powi(4)as u64);
        let g=proot(p);let h=mpow(g,(p-1)/n as u64,p);
        let mu:Vec<u64>=(0..n as u64).map(|j|mpow(h,j,p)).collect();
        for r in 1..=4usize {
            let az=add_e_charzero(n,r);
            let amp=add_e_modp(&mu,r,p);
            let c0=(dfact(r)*(n as f64).powi(r as i32)) as u128;
            println!("  {:2} {:2}  {:14}  {:14}  {:10}  {:+10}  {:+10}", n,r,az,c0,amp,amp as i128-az as i128,c0 as i128-az as i128);
        }
    }
}
