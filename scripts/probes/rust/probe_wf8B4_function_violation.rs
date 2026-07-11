use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn chk(n:u64,p:u64){
    let nn=n as f64; let q=p as f64;
    let g=proot(p); let h=mpow(g,(p-1)/n,p);
    let mu:Vec<u64>=(0..n).map(|j|mpow(h,j,p)).collect();
    let mut eta=Vec::with_capacity((p-1)as usize);
    for b in 1..p { let mut re=0.0; for &x in &mu { let t=((b as u128*x as u128)%p as u128) as u64; re+=(2.0*PI*(t as f64)/p as f64).cos(); } eta.push(re); }
    let ystar=(2.0*q.ln()/nn).sqrt();
    let mut worst=0.0f64; let mut atw=0.0; let steps=8000; let ymax=ystar*1.6;
    for i in 1..=steps { let y=ymax*(i as f64)/(steps as f64); let bound=(nn*y*y/2.0).exp();
        let mut s=0.0; for &ev in &eta { s+=(ev*y).cosh(); } s/=q;
        let r=s/bound; if r>worst{worst=r;atw=y;} }
    println!("n={} p={} beta={:.3} : max_y Phi_nz/exp(ny^2/2) = {:.5} @ y={:.3} (y*={:.3}) {}",
        n,p,q.ln()/nn.ln(), worst, atw, ystar, if worst>1.0 {"<<< W1-MGF FALSE"} else {"holds"});
}
fn main(){ chk(32,32993); chk(32,37217); chk(32,65537); chk(32,50177); }
