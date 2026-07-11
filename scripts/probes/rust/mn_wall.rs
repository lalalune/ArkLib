// Direct measurement of the prize wall M(n) = max_{b != 0} |sum_{x in mu_n} e_p(b x)|.
// Periods are coset-constant (eta_{ub}=eta_b for u in mu_n), so we range b over m=(p-1)/n coset reps.
// Reports M/sqrt(n), C = M/sqrt(n*ln(p/n)), and stratifies by v2(p-1) (the thinness gate).
use std::f64::consts::PI;

fn mpow(mut a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn is_prime(n:u64)->bool{if n<2{return false;}let mut d=2;while d*d<=n{if n%d==0{return false;}d+=1;}true}
fn find_prime_cong1(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n;}loop{if p>2&&p%n==1&&is_prime(p){return p;}p+=n;}}
fn primitive_root(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d;}}d+=1;}if m>1{fs.push(m);}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g;}g+=1;}}
fn v2(mut x:u64)->u32{let mut v=0;while x&1==0{v+=1;x>>=1;}v}

fn measure(n:u64,p:u64)->(f64,u64){
    // mu_n elements
    let g=primitive_root(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    // precompute e_p(t) = exp(2 pi i t / p) cos/sin tables lazily via formula
    let m=(p-1)/n; // number of cosets
    // coset reps: powers of g step n -> but we just need b over a transversal of mu_n in F_p^*.
    // Use b = g^j for j=0..m-1 (these hit each coset once).
    let mut best=0.0f64;
    let mut b=1u64; let gn=mpow(g,n,p); // g^n generates the quotient (order m)
    for _ in 0..m {
        // eta_b = sum_{x in mu} e_p(b*x)
        let mut re=0.0f64; let mut im=0.0f64;
        for &x in &mu {
            let t=( (b as u128 * x as u128) % p as u128) as u64;
            let ang=2.0*PI*(t as f64)/(p as f64);
            re+=ang.cos(); im+=ang.sin();
        }
        let mag=(re*re+im*im).sqrt();
        if mag>best{best=mag;}
        b=(( b as u128 * gn as u128) % p as u128) as u64;
    }
    (best,m)
}

fn main(){
    let args:Vec<String>=std::env::args().collect();
    // ns to sweep
    let ns:Vec<u64>= if args.len()>1 { args[1..].iter().map(|x|x.parse().unwrap()).collect() }
                     else { vec![16,32,64,128,256,512,1024] };
    eprintln!("# n  v2(p-1)  p  M  M/sqrt(n)  C=M/sqrt(n*ln(p/n))");
    for &n in &ns {
        // pick a few primes p=1 mod n with VARYING v2(p-1), beta=log_n(p) ~ 4 (prize-ish) and also a thin one
        // beta~4: p ~ n^4
        let target = (n as f64).powf(4.0) as u64;
        let mut found=0; let mut lo=target.max(200003);
        let mut seen_v2=std::collections::HashSet::new();
        while found<6 {
            let p=find_prime_cong1(n, lo);
            let vv=v2(p-1);
            if !seen_v2.contains(&vv) || found<3 {
                let (mm,_m)=measure(n,p);
                let beta=(p as f64).ln()/(n as f64).ln();
                let c=mm/(((n as f64)*((p as f64/n as f64).ln())).sqrt());
                eprintln!("{:5} {:4}  {:>14} {:9.3} {:7.3} {:7.4}  (beta={:.2})", n, vv, p, mm, mm/(n as f64).sqrt(), c, beta);
                seen_v2.insert(vv); found+=1;
            }
            lo=p+1;
        }
    }
}
