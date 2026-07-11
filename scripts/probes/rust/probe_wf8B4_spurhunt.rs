// Hunt: does a_2 > W_2 (=> Phi_nz > Gaussian for some y) at ANY prize-band prime where the
// B1 char-p spur in E_2 is large enough? a_2 = (q E_2 - n^4)/q, W_2 = 3 n^2.
// a_2 > W_2  <=>  q(E_2 - 3n^2) > n^4  <=> E_2 > 3n^2 + n^4/q.
// char-0 E_2 = 3n^2 - 3n, spur = E_2 - (3n^2-3n). Need spur > 3n + n^4/q.
// Compute E_2 EXACTLY as integer: E_2 = #{(x1,x2,y1,y2) in mu_n^4 : x1+x2 = y1+y2 mod p}.
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn e2(n:u64,p:u64)->i64{
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    // count sums x1+x2 mod p
    use std::collections::HashMap;
    let mut cnt:HashMap<u64,i64>=HashMap::new();
    for &a in &mu { for &b in &mu { let s=((a as u128+b as u128)%p as u128) as u64; *cnt.entry(s).or_insert(0)+=1; } }
    let mut e=0i64; for (_,&c) in &cnt { e += c*c; } e
}
fn main(){
    let ns=[8u64,16,32];
    for &n in &ns {
        let c0 = (3*n*n - 3*n) as i64;
        let w2 = (3*n*n) as i64;
        println!("--- n={} : char0 E_2={}, W_2(as energy bound 3n^2)={} ---", n, c0, w2);
        // scan primes p = 1 mod n in prize band [n^3, n^5]
        let lo = n.pow(3); let hi = n.pow(5).min(50_000_000);
        let mut p = lo + ((1+n - lo%n)%n);
        let mut worst_ratio=0.0f64; let mut worst_p=0u64; let mut nviol=0; let mut ntot=0;
        let mut max_spur=0i64;
        while p < hi {
            if p%n==1 && isp(p) {
                ntot+=1;
                let e = e2(n,p);
                let spur = e - c0;
                if spur>max_spur {max_spur=spur;}
                let q=p as f64; let nn=n as f64;
                // a_2 = (q*e - n^4)/q
                let a2 = ((p as f64)*(e as f64) - nn.powi(4))/q;
                let ratio = a2/(3.0*nn*nn);
                if ratio>worst_ratio {worst_ratio=ratio; worst_p=p;}
                if ratio>1.0 {nviol+=1;
                    if nviol<=5 {println!("  VIOLATION a_2>W_2: p={} beta={:.2} E_2={} spur={} a_2/W_2={:.5}", p, q.ln()/nn.ln(), e, spur, ratio);}
                }
            }
            p += n;
            if ntot>4000 {break;}
        }
        println!("  scanned {} primes in [{},{}); max a_2/W_2 = {:.5} at p={} ; violations={} ; max_spur={}",
            ntot, lo, hi, worst_ratio, worst_p, nviol, max_spur);
    }
}
