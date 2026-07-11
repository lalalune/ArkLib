// wf-W6: the LOAD-BEARING relative spurious count Spur_r(p)/Wick AND Spur_r/E_r^char0 across the
// FULL band r in [1 .. >r*], at PRIZE SCALE, multiple primes.  This is the (S-M1) quantity:
//   (S-M1)  Spur_r(p) <= eps * (2r-1)!! n^r.
// Geometry-of-numbers prediction: spurious vectors are short vectors of L_p of trace-radius^2 = phi*w;
// their NUMBER at radius phi*2r is governed by the theta series of L_p.  We measure
//   Spur_r = E_r^modp - E_r^char0  (exact),  Wick = (2r-1)!! n^r,  E_r^char0 (exact).
// and report Spur_r/Wick and (E_r^modp/Wick) -- the latter is A_r/Wick + DC, the prize ratio.
// KEY question: does Spur_r/Wick stay <= eps (bounded) THROUGH the optimal depth r* ~ ln q /2 as n grows?
use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn e_modp(mu:&[u64],r:usize,p:u64)->u128{
    let mut d:HashMap<u64,u128>=HashMap::new();d.insert(0,1);
    for _ in 0..r{let mut nd:HashMap<u64,u128>=HashMap::new();for(&s,&c)in &d{for &x in mu{let t=((s as u128+x as u128)%p as u128)as u64;*nd.entry(t).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&s,&c)in &d{let ns=((p-s)%p)as u64;if let Some(&c2)=d.get(&ns){t+=c*c2;}}t
}
fn e_charzero(n:usize,r:usize)->u128{
    use std::f64::consts::PI;
    let cs:Vec<(f64,f64)>=(0..n).map(|e|((2.0*PI*e as f64/n as f64).cos(),(2.0*PI*e as f64/n as f64).sin())).collect();
    let scale=1e7;
    let mut d:HashMap<(i64,i64),u128>=HashMap::new();d.insert((0,0),1);
    for _ in 0..r{let mut nd:HashMap<(i64,i64),u128>=HashMap::new();
        for(&(kr,ki),&c)in &d{for &(cr,ci) in &cs{let nr=((kr as f64/scale+cr)*scale).round() as i64;let ni=((ki as f64/scale+ci)*scale).round() as i64;*nd.entry((nr,ni)).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&(kr,ki),&c)in &d{if let Some(&c2)=d.get(&(-kr,-ki)){t+=c*c2;}}t
}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn run(n:usize,p:u64,rmax:usize){
    let g=proot(p);let h=mpow(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n as u64).map(|j|mpow(h,j,p)).collect();
    let lnq=(p as f64).ln();let rstar=lnq/2.0;
    println!("== n={} p={} beta={:.2} ln q={:.1} r*~{:.1} ==", n,p,lnq/(n as f64).ln(),lnq,rstar);
    println!("   r  Spur_r          Spur/Wick   Emodp/Wick(=A/W+DC)  Echar0/Wick  [r vs r*]");
    for r in 1..=rmax {
        let emp=e_modp(&mu,r,p) as i128;
        let ez=e_charzero(n,r) as i128;
        let spur=emp-ez;
        let wick=dfact(r)*(n as f64).powi(r as i32);
        // A_r = E_r - n^{2r}/p (DC subtracted)
        let dc=(n as f64).powf(2.0*r as f64)/(p as f64);
        let ar = emp as f64 - dc;
        let mark = if (r as f64) < rstar {"<r*"} else {">=r*"};
        println!("  {:2}  {:14}  {:9.4}  {:12.4}  {:11.4}   [{} A/W={:.4}]",
            r, spur, spur as f64/wick, emp as f64/wick, ez as f64/wick, mark, ar/wick);
    }
}
fn main(){
    println!("# wf-W6: spurious relative count across band to depth > r*, prize scale");
    run(8,  fp(8,  4096), 9);
    run(16, fp(16, 65536), 8);
    run(32, fp(32, 1_048_576), 7);
    run(64, fp(64, 16_777_216), 6);
    println!("\n# higher beta (p~n^5) at n=16,32 -- pushes r* up:");
    run(16, fp(16, (16f64).powi(5) as u64), 9);
    run(32, fp(32, (32f64).powi(5) as u64), 7);
}
