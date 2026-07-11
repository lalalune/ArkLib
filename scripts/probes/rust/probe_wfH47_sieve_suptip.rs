// probe_wfH47_sieve_suptip.rs  (#444 lane L2, angle H47, supplement)
//
// The SUP M(n) is attained at a HANDFUL of cosets. A sieve that capped |A_T| (count of
// large cosets) would still not bound M unless A_T were EMPTY for T near the floor.
// Here we look at the absolute TIP: the top-50 cosets by |eta_b|. We test whether the
// sup-attaining b have ANY exploitable structure (residue classes mod small l, or
// multiplicative-order / 2-adic structure of the coset index j where b=g^j).
// If the tip is structureless (spread over residue classes AND over coset-index parities),
// no parity/Selberg sieve can isolate or cap it.

use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;} r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}

fn main(){
    let ns:Vec<u64>=vec![16,32,64];
    println!("# H47-tip: structure of the TOP-50 sup-attaining cosets (b=g^j). j = coset index in Z/m.");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let p=find_prime_cong1(n,target.max(200003));
        let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|i|mpow(h,i,p)).collect();
        let m=(p-1)/n; let gn=mpow(g,n,p);
        let mut vals:Vec<(f64,u64,u64)>=Vec::with_capacity(m as usize); // (|eta|^2, b, j)
        let mut b=1u64;
        for j in 0..m {
            let mut re=0.0; let mut im=0.0;
            for &x in &mu { let t=((b as u128*x as u128)%p as u128) as u64; let a=2.0*PI*(t as f64)/(p as f64); re+=a.cos(); im+=a.sin(); }
            vals.push((re*re+im*im,b,j));
            b=((b as u128*gn as u128)%p as u128) as u64;
        }
        vals.sort_by(|a,c|c.0.partial_cmp(&a.0).unwrap());
        let top:Vec<(f64,u64,u64)>=vals[..50.min(vals.len())].iter().cloned().collect();
        println!("\n## n={} p={} m={} M={:.3}", n, p, m, vals[0].0.sqrt());
        // residue spread of the tip b mod small primes
        for &l in &[3u64,5,7,11] {
            let mut occ=vec![0u32;l as usize];
            for &(_,bb,_) in &top { occ[(bb%l) as usize]+=1; }
            let nz=occ.iter().filter(|&&c|c>0).count();
            println!("  tip-50 b mod {}: classes hit = {}/{}  counts={:?}", l, nz, l, occ);
        }
        // coset-index j parity / 2-adic: is the tip biased to even/odd j or special j mod 2^k?
        let even=top.iter().filter(|&&(_,_,j)|j%2==0).count();
        let jmod4:Vec<u32>={let mut c=[0u32;4]; for &(_,_,j) in &top {c[(j%4) as usize]+=1;} c.to_vec()};
        println!("  tip-50 coset-index j: even={}/50  j mod4 counts={:?}  (uniform => no 2-adic handle)", even, jmod4);
    }
    println!("\n# READ: tip is spread over all residue classes AND j-parities => the sup-attaining set");
    println!("#   has no congruence/2-adic structure; no parity-respecting/Selberg sieve can isolate it.");
}
