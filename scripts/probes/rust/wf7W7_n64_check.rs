// wf-W7c: confirm GEN_r := A_r - E_r^0 < 0 (=> A_r <= Wick, K=1) at n=64, prize beta=3, through r*.
// build: rustc -O wf7W7_n64_check.rs -o /tmp/w7c
use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fp(n:u64,lo:u64)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}loop{if p>2&&p%n==1&&isp(p){return p}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
// dense-array DP (p ~ 2.6e5 fits) for speed
fn e_modp_dense(mu:&[u64],r:usize,p:u64)->f64{
    let pn=p as usize;
    let mut d=vec![0f64;pn]; d[0]=1.0;
    for _ in 0..r{
        let mut nd=vec![0f64;pn];
        for s in 0..pn{ let c=d[s]; if c==0.0{continue;} for &x in mu{ let t=(s+x as usize)%pn; nd[t]+=c; } }
        d=nd;
    }
    let mut t=0f64; for s in 0..pn{ t+=d[s]*d[s]; } t
}
fn e_charzero(n:usize,r:usize)->u128{
    use std::f64::consts::PI;
    let cs:Vec<(f64,f64)>=(0..n).map(|e|((2.0*PI*e as f64/n as f64).cos(),(2.0*PI*e as f64/n as f64).sin())).collect();
    let scale=1e7;
    let mut d:HashMap<(i64,i64),u128>=HashMap::new();d.insert((0,0),1);
    for _ in 0..r{let mut nd:HashMap<(i64,i64),u128>=HashMap::new();
        for(&(kr,ki),&c)in &d{for &(cr,ci) in &cs{let nr=((kr as f64/scale+cr)*scale).round() as i64;let ni=((ki as f64/scale+ci)*scale).round() as i64;*nd.entry((nr,ni)).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&(_kr,_ki),&c)in &d{t+=c*c;}t
}
fn main(){
    let n=64usize; let beta=3.0f64;
    let p=fp(n as u64,(n as f64).powf(beta) as u64);
    let g=proot(p);let h=mpow(g,(p-1)/n as u64,p);
    let mu:Vec<u64>=(0..n as u64).map(|j|mpow(h,j,p)).collect();
    let rstar=((p as f64).ln()/2.0).round() as usize;
    println!("# wf-W7c  n=64 beta=3 p={} r*={}", p, rstar);
    println!("# r  E_r(p)  E_r^0  A_r=E-DC  Wick  GEN=A-E0  GEN/Wick  A_r/Wick sign");
    for r in 2..=7{
        let emp=e_modp_dense(&mu,r,p);
        let e0=e_charzero(n,r) as f64;
        let dc=(n as f64).powf(2.0*r as f64)/p as f64;
        let ar=emp-dc;
        let wick=dfact(r)*(n as f64).powi(r as i32);
        let gen=ar-e0;
        let band=if r==rstar{" <-r*"}else{""};
        println!("{:2}  {:>13.3e} {:>13.3e} {:>13.3e} {:>11.3e} {:>13.3e}  {:>9.4} {:>8.4} {}{}",
            r,emp,e0,ar,wick,gen,gen/wick,ar/wick,if gen>0.0{"+"}else{"-"},band);
    }
}
