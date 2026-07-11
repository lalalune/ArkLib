// wf-P2 DECISIVE: is A_r <= (2r-1)!! n^r ALWAYS (char-p additive energy <= char-0 Lam-Leung ceiling)?
// If yes => E_r' = A_r - n^{2r}/p < A_r <= char0 => S-M1 with K=1, ZERO excess. Prize follows.
// We brute A_r exactly across many (n, prize p) and report max ratio. Also test depth r up to where feasible.
// CRITICAL: re-run at multiple primes per n (artifact check: is sub-char-0 prime-dependent?).
use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fpk(n:u64,lo:u64,k:usize)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}let mut c=0;loop{if p>2&&p%n==1&&isp(p){c+=1;if c>k{return p}}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn additive_energy_modp(mu:&[u64], r:usize, p:u64)->u128{
    let mut dist:HashMap<u64,u128>=HashMap::new(); dist.insert(0,1);
    for _ in 0..r { let mut nd:HashMap<u64,u128>=HashMap::with_capacity(dist.len()*2);
        for(&s,&c) in &dist { for &x in mu { let t=((s as u128+x as u128)%p as u128)as u64; *nd.entry(t).or_insert(0)+=c; } } dist=nd; }
    let mut tot:u128=0; for(&s,&c) in &dist { let ns=((p-s)%p)as u64; if let Some(&c2)=dist.get(&ns){tot+=c*c2;} } tot
}
fn main(){
    let mut worst=0.0f64; let mut worstdesc=String::new();
    for &a in &[2u32,3,4,5] { let n=1u64<<a;
        for kp in 0..4 { // 4 different prize primes per n (artifact check)
            let p=fpk(n,(n as f64).powi(4)as u64, kp);
            let g=proot(p); let h=mpow(g,(p-1)/n,p);
            let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
            for r in 1..=6usize {
                let ar=additive_energy_modp(&mu,r,p) as f64;
                let ratio=ar/(dfact(r)*(n as f64).powi(r as i32));
                if ratio>worst { worst=ratio; worstdesc=format!("n={} p={} r={} ratio={:.4}",n,p,r,ratio); }
                if ratio>1.0001 { println!("  VIOLATION n={} p={} r={} A_r/char0={:.4}",n,p,r,ratio); }
            }
        }
    }
    println!("MAX A_r/char0 over all (n,p,r): {:.4}  at {}", worst, worstdesc);
    println!("(<=1 everywhere => A_r <= char0 holds; E_r' < A_r <= char0 => S-M1 K=1)");
}
