// wf-P2: the SHARP S-M1 form. A_r^modp <= char0  <=>  spur_r(p) <= slack_r := char0 - A_r^Z.
// Test the slack-domination spur/slack across (n, prize p, r) at multiple primes, find max.
// If spur/slack < 1 robustly => A_r^modp <= char0 with margin. Re-run at multiple primes (artifact).
use std::collections::HashMap;
use std::f64::consts::PI;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r=1u128;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2;while d*d<=n{if n%d==0{return false}d+=1}true}
fn fpk(n:u64,lo:u64,k:usize)->u64{let mut p=lo+((1+n-lo%n)%n);if p<=2{p+=n}let mut c=0;loop{if p>2&&p%n==1&&isp(p){if c==k{return p}c+=1;}p+=n}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn add_e_modp(mu:&[u64],r:usize,p:u64)->u128{let mut d:HashMap<u64,u128>=HashMap::new();d.insert(0,1);
 for _ in 0..r{let mut nd:HashMap<u64,u128>=HashMap::new();for(&s,&c)in &d{for &x in mu{let t=((s as u128+x as u128)%p as u128)as u64;*nd.entry(t).or_insert(0)+=c;}}d=nd;}
 let mut t:u128=0;for(&s,&c)in &d{let ns=((p-s)%p)as u64;if let Some(&c2)=d.get(&ns){t+=c*c2;}}t}
fn add_e_charzero(n:usize,r:usize)->u128{
    let cs:Vec<(f64,f64)>=(0..n).map(|e|((2.0*PI*e as f64/n as f64).cos(),(2.0*PI*e as f64/n as f64).sin())).collect();
    let scale=1e7; let mut d:HashMap<(i64,i64),u128>=HashMap::new();d.insert((0,0),1);
    for _ in 0..r{let mut nd:HashMap<(i64,i64),u128>=HashMap::new();
        for(&(kr,ki),&c)in &d{for &(cr,ci) in &cs{let nr=((kr as f64/scale+cr)*scale).round() as i64;let ni=((ki as f64/scale+ci)*scale).round() as i64;*nd.entry((nr,ni)).or_insert(0)+=c;}}d=nd;}
    let mut t:u128=0;for(&(kr,ki),&c)in &d{if let Some(&c2)=d.get(&(-kr,-ki)){t+=c*c2;}}t}
fn main(){
    println!("  n  r  prime#  A_r^modp/char0   spur          slack         spur/slack");
    let mut worst=0.0f64;let mut wd=String::new();
    for &n in &[8usize,16,32] {
        let az:Vec<u128>=(0..=5).map(|r|add_e_charzero(n,r)).collect();
        for kp in 0..3 {
            let p=fpk(n as u64,(n as f64).powi(4)as u64,kp);
            let g=proot(p);let h=mpow(g,(p-1)/n as u64,p);
            let mu:Vec<u64>=(0..n as u64).map(|j|mpow(h,j,p)).collect();
            for r in 2..=5usize {
                let amp=add_e_modp(&mu,r,p);
                let c0=(dfact(r)*(n as f64).powi(r as i32)) as u128;
                let spur=amp as i128 - az[r] as i128;
                let slack=c0 as i128 - az[r] as i128;
                let ratio=amp as f64/c0 as f64;
                let ss=if slack>0 {spur as f64/slack as f64} else {0.0};
                if r==5 || (n==32&&r>=4) { // print interesting deep rows
                  println!("  {:2} {:2}   {}     {:.5}      {:+12}  {:12}  {:.4}", n,r,kp,ratio,spur,slack,ss);
                }
                if ratio>worst {worst=ratio;wd=format!("n={} p={} r={} ratio={:.5} spur/slack={:.4}",n,p,r,ratio,ss);}
            }
        }
    }
    println!("WORST A_r^modp/char0: {:.5}  ({})", worst, wd);
}
