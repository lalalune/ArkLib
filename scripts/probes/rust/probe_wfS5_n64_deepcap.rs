use std::collections::HashMap;
fn mpow(a:u64,mut e:u64,p:u64)->u64{let mut r:u128=1;let mut a2=a as u128;let pp=p as u128;while e>0{if e&1==1{r=r*a2%pp;}a2=a2*a2%pp;e>>=1;}r as u64}
fn isp(n:u64)->bool{if n<2{return false}let mut d=2u64;while d*d<=n{if n%d==0{return false}d+=1}true}
fn npm(n:u64,mut p:u64)->u64{if p%n!=1{p+=(n+1-p%n)%n;}loop{if p>2&&isp(p){return p}p+=n;}}
fn proot(p:u64)->u64{let mut m=p-1;let mut fs=vec![];let mut d=2u64;while d*d<=m{if m%d==0{fs.push(d);while m%d==0{m/=d}}d+=1}if m>1{fs.push(m)}let mut g=2u64;loop{if fs.iter().all(|&f|mpow(g,(p-1)/f,p)!=1){return g}g+=1}}
fn pb(p:u64,n:u64)->Vec<u64>{let g0=proot(p);let h=mpow(g0,(p-1)/n,p);let d=(n/2)as usize;(0..d).map(|j|mpow(h,j as u64,p)).collect()}
fn ht(gens:&[u64],p:u64,cap:usize)->Vec<HashMap<u64,u64>>{let mut dp:Vec<HashMap<u64,u64>>=(0..=cap).map(|_|HashMap::new()).collect();dp[0].insert(0u64,1u64);for &g in gens{let mut ndp:Vec<HashMap<u64,u64>>=(0..=cap).map(|_|HashMap::new()).collect();for w in 0..=cap{for(&res,&cnt)in &dp[w]{*ndp[w].entry(res).or_insert(0)+=cnt;let mut add=0u64;for k in 1..=(cap-w){add=(add+g)%p;let rp=(res+add)%p;let rm=(res+p-add)%p;*ndp[w+k].entry(rp).or_insert(0)+=cnt;*ndp[w+k].entry(rm).or_insert(0)+=cnt;}}}dp=ndp;}dp}
fn dfact(r:usize)->f64{let mut v=1.0;for j in 1..=r{v*=(2*j-1)as f64}v}
fn shells(n:u64,p:u64,cap:usize)->Vec<u64>{let g=pb(p,n);let d=(n/2)as usize;let half=d/2;let tl=ht(&g[..half],p,cap);let tr=ht(&g[half..],p,cap);let mut s=vec![0u64;cap+1];for w in 0..=cap{let mut t=0u64;for wl in 0..=w{let wr=w-wl;for(&rl,&cl)in &tl[wl]{let need=(p-rl)%p;if let Some(&cr)=tr[wr].get(&need){t+=cl*cr;}}}s[w]=t;}s[0]=s[0].saturating_sub(1);s}
fn main(){
  let n=64u64; let cap=12usize; let mut p=npm(n,n.pow(4));
  for _ in 0..2{
    let s=shells(n,p,cap);
    let g=(1..=cap).find(|&w|s[w]>0).unwrap_or(cap+1);
    let mut bmax=0.0f64; for w in 1..=cap{if s[w]>0{let b=(s[w]as f64).powf(1.0/w as f64);if b>bmax{bmax=b;}}}
    let mut cum=0u64; let mut line=String::new();
    for w in 1..=cap{cum+=s[w];if w%2==0{let r=w/2;let ra=cum as f64/dfact(r);line.push_str(&format!("r{}:{:.3} ",r,ra));}}
    println!("n=64 p={} girth={} B={:.4} B^2/n={:.4} shells={:?}",p,g,bmax,bmax*bmax/64.0,&s);
    println!("   R-by-r: {}",line);
    p=npm(n,p+1);
  }
}
