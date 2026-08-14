// wf-P2: pin the EXACT identity. Full real moment sum_{b=0}^{p-1} eta_b^{2r} = p * S_r
// where S_r = #{signed 2r-tuples}? We verify numerically and isolate the PRINCIPAL contribution.
// eta_b = sum_{x in mu_n} cos(2pi b x/p) is real. Then
//   sum_b eta_b^{2r} = sum_b (sum_x cos(theta_{b,x}))^{2r}.
// Using cos = (e+e^-)/2 and mu_n negation-closed, eta_b = (1/2) sum_{x in mu_n} (e_p(bx)+e_p(-bx))
//   but mu_n closed under negation so eta_b = Re sum_x e_p(bx) = sum_x e_p(bx) (already real).
// So eta_b = sum_x e_p(bx), and sum_b eta_b^{2r} = sum_b |..|? No, eta_b real so eta_b^{2r} real.
// sum_{b=0}^{p-1} (sum_x e_p(bx))^{2r} = sum over (x_1..x_2r) of sum_b e_p(b(x_1+..+x_2r))
//   = p * #{(x_1..x_2r) in mu_n^{2r}: sum x_i == 0 mod p} = p * A_r.  <-- THIS is A_r exactly.
// So FULL real moment / p = A_r (additive energy). The PRINCIPAL b=0 term is eta_0^{2r}=n^{2r}.
// E_r' (nonprincipal) = A_r - n^{2r}/p.   Let's verify and tabulate the principal subtraction.
use std::f64::consts::PI;
use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn additive_energy_modp(mu:&[u64], r:usize, p:u64)->u128{
    let mut dist:HashMap<u64,u128>=HashMap::new(); dist.insert(0,1);
    for _ in 0..r {
        let mut nd:HashMap<u64,u128>=HashMap::with_capacity(dist.len()*mu.len());
        for(&s,&c) in &dist { for &x in mu { let t=((s as u128 + x as u128)%p as u128) as u64; *nd.entry(t).or_insert(0)+=c; } }
        dist=nd;
    }
    let mut tot:u128=0;
    for(&s,&c) in &dist { let ns=((p-s)%p) as u64; if let Some(&c2)=dist.get(&ns){ tot+=c*c2; } }
    tot
}
fn main(){
    let n=16u64; let p=fp(16,60000);
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    println!("n={} p={}: verify full real moment / p == A_r (additive energy)", n, p);
    // full real moment via direct eta_b
    for r in 1..=5usize {
        let mut full=0.0f64;
        for b in 0..p { let mut e=0.0; for &x in &mu { e += (2.0*PI*((b as u128*x as u128)%p as u128)as f64/p as f64).cos(); } full += e.powi(2*r as i32); }
        let ar = additive_energy_modp(&mu, r, p) as f64;
        let principal=(n as f64).powi(2*r as i32); // eta_0^{2r} = n^{2r}
        println!("  r={}: full/p={:.1}  A_r={:.0}  match?{}  principal/p={:.3}  (A_r - princ/p)/char0={:.4}",
            r, full/p as f64, ar, ((full/p as f64-ar).abs()<1.0), principal/p as f64,
            (ar - principal/p as f64)/(dfact(r)*(n as f64).powi(r as i32)));
    }
}
