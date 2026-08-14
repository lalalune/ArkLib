// G6d: characterize the n=64 rough-prime r=3 spurious deviation. Is it a CURVE (point count
// scaling with the rough factor ell, i.e. ~sqrt(ell) or ~ell), or a FIXED short ±1 relation
// among 2^mu-th roots vanishing mod p (prime-specific, NOT curve)? 
// We find, across MANY rough primes at n=64, the spurious count spur = E3 - E3_char0base,
// and check whether spur correlates with the rough factor ell (curve signature) or is a
// quantized small integer (short-relation signature).
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn largest_prime_factor(mut x:u64)->u64{let mut best=1;let mut d=2;while d*d<=x{if x%d==0{best=best.max(d);while x%d==0{x/=d;}}d+=1;}if x>1{best=best.max(x);}best}
fn e3(mu:&[u64],p:u64)->u64{use std::collections::HashMap;let mut cnt:HashMap<u64,u64>=HashMap::new();
    for &a in mu{for &b in mu{for &c in mu{let s=((a as u128+b as u128+c as u128)%p as u128) as u64;*cnt.entry(s).or_insert(0)+=1;}}}
    cnt.values().map(|&v|v*v).sum()}
fn main(){
    let n=64u64;
    // baseline char-0 E3 = the minimum observed (smoothest, no spurious mass)
    let target=(n as f64).powf(4.0) as u64; let mut lo=target;
    let mut base=u64::MAX;
    let mut rows=vec![];
    for _ in 0..400 {
        let p=find_prime_cong1(n,lo); lo=p+1;
        let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        let e=e3(&mu,p); let lpf=largest_prime_factor((p-1)/n);
        if e<base{base=e;}
        rows.push((p,lpf,e));
    }
    println!("# char-0 baseline E3(min over 400 primes) = {}", base);
    println!("# spur = E3 - base; check if spur ~ ell (curve) or quantized small (short relation)");
    let mut nonzero=0; let mut maxspur=0;
    for (p,lpf,e) in &rows {
        let spur=e-base;
        if spur>0 { nonzero+=1; if spur>maxspur{maxspur=spur;}
            if nonzero<=15 { println!("p={:>12} ell={:>12} spur={:>8} spur/ell={:.6} spur/sqrt(ell)={:.4}",p,lpf,spur,(spur as f64)/(*lpf as f64),(spur as f64)/(*lpf as f64).sqrt()); }
        }
    }
    println!("# {}/400 primes have spurious mass; max spur={}", nonzero, maxspur);
    println!("# n^3={} ; if spur were curve-over-F_ell point count it'd track ell (~262519); short relation => bounded/quantized", n*n*n);
}
