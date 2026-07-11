// G6b: The DECISIVE structured-prime curve test.
// The curve/Stepanov-Weil engine bounds curve point counts by (deg)*sqrt(FIELD SIZE).
// For mu_n's spurious mass to be curve-bounded BELOW the trivial n, we'd need the relevant
// curve to live over a field of size << n^2 (so sqrt(field) << n). 
//
// CLAIM TO TEST (the rough-prime hope): at a rough prime p (ell | p-1, ell large prime), the
// "extra coincidences" defining the worst-b bad set are governed by the order-ell quotient,
// which might descend to a smaller-field curve.
//
// We test the ONLY concrete realization: the additive-energy / coincidence structure
// E = #{(a,b,c,d) in mu_n^4 : a-b = c-d}. The Stepanov-Weil curve attached to mu_n's
// spurious mass counts solutions of subgroup equations. If ROUGHNESS reduced this count
// (descent to smaller field), E_rough < E_smooth. We measure E (and 4th-moment-type counts)
// at rough vs smooth primes and check whether roughness LOWERS the coincidence count.
//
// Also: directly test the "subfield descent" — does mu_n, mod the rough factor structure,
// satisfy any relation over a proper subring of size < n^2? Since F_p is a prime field it has
// NO proper subfield; we verify the spurious mass count is INSENSITIVE to ell (no descent).
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn largest_prime_factor(mut x:u64)->u64{let mut best=1;let mut d=2;while d*d<=x{if x%d==0{best=best.max(d);while x%d==0{x/=d;}}d+=1;}if x>1{best=best.max(x);}best}
// additive energy E(mu_n) = #{(a,b,c,d): a+b=c+d} = sum_s r(s)^2 where r(s)=#{(a,b):a+b=s}
fn add_energy(mu:&[u64],p:u64)->u64{
    use std::collections::HashMap;
    let mut cnt:HashMap<u64,u64>=HashMap::new();
    for &a in mu { for &b in mu { let s=((a as u128+b as u128)%p as u128) as u64; *cnt.entry(s).or_insert(0)+=1; } }
    cnt.values().map(|&v|v*v).sum()
}
fn main(){
    // For mu_n, char-0 additive energy floor ~ 3n^2-3n+1 (Sidon-ish). Rough-prime hope: descent lowers it.
    let ns=[16u64,32,64,128];
    println!("# n  type  p  lpf  E_add  E/n^2  (char0 sidon floor 3n^2-2n)");
    for &n in &ns {
        let target=(n as f64).powf(4.0) as u64;
        let mut lo=target.max(200003);
        let mut roughest=(0.0f64,0u64); let mut smoothest=(1e18f64,0u64);
        for _ in 0..150 {
            let p=find_prime_cong1(n,lo); lo=p+1;
            let m=(p-1)/n; let lpf=largest_prime_factor(m);
            let score=(lpf as f64)/(m as f64);
            if score>roughest.0 { roughest=(score,p); }
            if score<smoothest.0 { smoothest=(score,p); }
        }
        for (label,p) in [("ROUGH",roughest.1),("SMOOTH",smoothest.1)] {
            let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
            let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
            let e=add_energy(&mu,p);
            let lpf=largest_prime_factor((p-1)/n);
            println!("{:5} {:7} {:>14} lpf={:>12} E={:8} E/n^2={:7.4}",n,label,p,lpf,e,(e as f64)/((n*n) as f64));
        }
        println!("      char0-sidon-floor 3n^2-2n = {}", 3*n*n-2*n);
    }
}
