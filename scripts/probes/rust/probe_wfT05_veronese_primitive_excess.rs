// probe_wfT05_veronese_primitive_excess.rs  (#444 attack T05)
//
// T05 (Veronese moment-curve primitive-cohomology sub-bound) claims:
//   the additive-energy EXCESS over Wick,  W_r := E_r(mu_n) - (2r-1)!! * n^r,
//   is O_r(1) -- bounded, n-INDEPENDENT -- because a "moment-curve (Veronese)
//   transversality" lowers the primitive cohomology weight by an extra p^{-1/2}
//   per primitive class, giving  W_r <= dim_prim = C(2r,r) - (2r-1)!!  (n-free).
//
// This probe MEASURES W_r EXACTLY at the prize regime (beta=4, p ~ n^4, p = 1 mod n,
//  mu_n = order-n=2^mu subgroup) and reports its n-scaling.
//
//   E_r(mu_n) = #{ (x_1..x_r, y_1..y_r) in mu_n^{2r} : sum x_i = sum y_i  (mod p) }
//             = sum_s c_r(s)^2,   c_r(s) = #{ r-tuples in mu_n^r summing to s }.
//
// Computed EXACTLY by r-fold additive convolution over Z_p (hashmap; mod-p reduction).
//
// THE TEST:
//   * Wick main term  W = (2r-1)!! * n^r.
//   * excess  ex = E_r - W.
//   * T05 prediction:  ex bounded by dim_prim = C(2r,r)-(2r-1)!!  (n-FREE).
//   * if ex/n^{r-1} or ex/W stays ~constant in n  ==> excess is Omega(n^{r-1}),
//     polynomial in n, NOT O(1)  ==> the Veronese transversality gain is fictional
//     ==> reduces to F2 (Weil error p^{r-1} not lowered) / F1 (excess = BGK content).
//
// Also reports the "moment-curve fold" fact (Reason 2 of VinogradovDecouplingVacuous):
//   the map  x |-> x^j  sends mu_n into mu_{n/gcd(j,n)} subset mu_n  (closes up).

use std::collections::HashMap;

fn mpow(a:u64, mut e:u64, p:u64)->u64{
    let mut r=1u128; let mut a2=a as u128; let pp=p as u128;
    while e>0 { if e&1==1 { r=r*a2%pp; } a2=a2*a2%pp; e>>=1; } r as u64
}
fn isp(n:u64)->bool{ if n<2 {return false} let mut d=2; while d*d<=n { if n%d==0 {return false} d+=1 } true }
// smallest prime p > lo with p = 1 mod n
fn fp(n:u64, lo:u64)->u64{
    let mut p = lo + ((n + 1 - lo%n)%n);
    if p%n!=1 { p += n - (p%n) + 1; }
    loop { if p>2 && p%n==1 && isp(p) { return p } p += n; }
}
fn proot(p:u64)->u64{
    let mut m=p-1; let mut fs=vec![]; let mut d=2;
    while d*d<=m { if m%d==0 { fs.push(d); while m%d==0 { m/=d } } d+=1 }
    if m>1 { fs.push(m) }
    let mut g=2; loop { if fs.iter().all(|&f| mpow(g,(p-1)/f,p)!=1) { return g } g+=1 }
}
// double factorial (2r-1)!!
fn dfact(r:u64)->u128{ let mut v=1u128; let mut k=1u128; while k<=2*r as u128-1 { v*=k; k+=2; } v }
// central binomial C(2r,r)
fn cbin(r:u64)->u128{ let mut num=1u128; let mut den=1u128; for i in 1..=r { num*=(r+i) as u128; den*=i as u128; } num/den }

// r-fold additive convolution of the indicator of mu (over Z_p), returns count map.
fn rfold(mu:&[u64], r:u32, p:u64)->HashMap<u64,u64>{
    // start with c_1(s) = 1 for s in mu
    let mut cur:HashMap<u64,u64>=HashMap::new();
    for &x in mu { *cur.entry(x).or_insert(0)+=1; }
    for _ in 1..r {
        let mut next:HashMap<u64,u64>=HashMap::with_capacity(cur.len()*mu.len()/2+8);
        for (&s,&c) in &cur {
            for &x in mu {
                let t=((s as u128 + x as u128)%p as u128) as u64;
                *next.entry(t).or_insert(0)+= c;
            }
        }
        cur=next;
    }
    cur
}
fn energy_from_counts(c:&HashMap<u64,u64>)->u128{
    let mut e=0u128; for (_,&v) in c { e += (v as u128)*(v as u128); } e
}

fn main(){
    println!("=== T05 Veronese primitive-cohomology excess test (beta=4, p~n^4, p=1 mod n) ===");
    println!("model: E_r(mu_n) = sum_s c_r(s)^2 ; Wick = (2r-1)!!*n^r ; excess = E_r - Wick");
    println!("T05 claim: excess <= dim_prim = C(2r,r)-(2r-1)!!  (n-FREE / O_r(1))\n");

    for r in 2u32..=4 {
        let df = dfact(r as u64);
        let dimprim = (cbin(r as u64) as i128) - (df as i128); // C(2r,r) - (2r-1)!!
        println!("---- r = {}   (2r-1)!! = {}   C(2r,r) = {}   dim_prim = {} ----",
                 r, df, cbin(r as u64), dimprim);
        println!("{:>5} {:>14} {:>18} {:>18} {:>16} {:>14} {:>14}",
                 "n","p","E_r","Wick=(2r-1)!!n^r","excess","ex/n^(r-1)","ex/Wick");
        for a in 3..=6u32 {            // n = 8,16,32,64
            let n = 1u64<<a;
            // depth feasibility: count space ~ n^r distinct sums; cap work
            if (n as u128).pow(r) > 60_000_000 { println!("{:>5}  (skipped: n^r too large)", n); continue; }
            let lo = (n as f64).powf(4.0) as u64;     // p ~ n^4  (beta = 4 exactly-ish)
            let p = fp(n, lo);
            let g = proot(p); let h = mpow(g,(p-1)/n,p);
            let mu:Vec<u64> = (0..n).map(|j| mpow(h,j,p)).collect();
            let counts = rfold(&mu, r, p);
            let e_r = energy_from_counts(&counts);
            let wick = df * (n as u128).pow(r);
            let exc = e_r as i128 - wick as i128;
            let nf = n as f64;
            let ex_over_npow = exc as f64 / nf.powi(r as i32 - 1);
            let ex_over_wick = exc as f64 / wick as f64;
            println!("{:>5} {:>14} {:>18} {:>18} {:>16} {:>14.4} {:>14.6}",
                     n, p, e_r, wick, exc, ex_over_npow, ex_over_wick);
        }
        // verdict line
        println!("  -> T05 says excess <= {} (n-free). Watch whether 'excess' and 'ex/n^(r-1)' grow with n.\n", dimprim);
    }

    // Moment-curve FOLD fact (the geometric input T05's transversality needs, and lacks):
    println!("=== moment-curve fold: x |-> x^j over mu_n closes up (zero net curvature) ===");
    for a in 4..=6u32 {
        let n=1u64<<a;
        let lo=(n as f64).powf(4.0) as u64; let p=fp(n,lo);
        let g=proot(p); let h=mpow(g,(p-1)/n,p);
        let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
        // image of mu under x->x^j : size = n/gcd(j,n)
        print!("n={:>3}: |image of x^j| for j=1..6 : ", n);
        for j in 1u64..=6 {
            let mut img:std::collections::HashSet<u64>=std::collections::HashSet::new();
            for &x in &mu { img.insert(mpow(x,j,p)); }
            let g=gcd(j,n);
            print!("j={}:{}(=n/{}) ", j, img.len(), g);
        }
        println!();
    }
    println!("\n  -> x^j stays inside mu_n (image = mu_{{n/gcd(j,n)}}). The Veronese v_r(b)=(b,..,b^r)");
    println!("     does NOT open r transversal directions over mu_n -- it folds back. No transversality gain.");
}

fn gcd(a:u64,b:u64)->u64{ if b==0 {a} else {gcd(b,a%b)} }
