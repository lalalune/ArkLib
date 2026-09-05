// Exact bounded T-interpolant/cutoff search. This is not a ProtocolClaim.
// Official source pin: 032154395c51fd6f77715a7f42d9a987ab9fb48a.
// Formulas: SubmissionLower/PackedLocatorTail.lean, LocatorFastKernelArithmetic,
// LocatorLowQuotient.quotient_box_of_full_divisor, and LocatorCaps.
// Build: clang++ -O3 -std=c++17 astra_t_cutoff.cpp -o /tmp/astra-t-cutoff
// Bounds are deliberately fixed: m=1..270, S=0..min(m,81), L<=130000.
// These are the T-box embeddings into the published C ambient, with error80791.
#include <algorithm>
#include <array>
#include <cassert>
#include <iostream>
#include <string>
#include <vector>

using Integer = __int128_t;
constexpr int n=262144, w=131071, agreements=181353;
constexpr int max_m=270, max_s=81, max_l=130000;

std::string decimal(Integer x) {
  if (x<0) return "-"+decimal(-x);
  if (!x) return "0";
  std::string s;
  while (x) { s.push_back('0'+x%10); x/=10; }
  std::reverse(s.begin(),s.end());
  return s;
}
Integer positive(Integer x) { return std::max<Integer>(0,x); }
Integer ceiling(Integer x,Integer y) {
  assert(y>0);
  return x>=0 ? (x+y-1)/y : x/y;
}
Integer rectangle(Integer a,Integer b,Integer offset,Integer limit) {
  return positive(a*b*positive(limit+1-offset)
                  -b*a*positive(a-1)/2-a*b*positive(b-1)/2);
}
Integer local_rank(int m,int limit,int slope) {
  assert(limit>=m+slope);
  Integer result=0;
  for (int r=0;r<m;++r) {
    int degree=std::min(r,limit), contact=std::min(r+1,m-r);
    result+=positive(rectangle(degree+1,slope+1,0,limit)
       -rectangle(std::max(0,degree+1-contact),
                  std::max(0,slope+1-contact),contact,limit));
  }
  return result;
}
Integer coefficient_count(Integer weighted,int limit,int slope) {
  Integer result=0;
  for (int j=0;j<=slope;++j) {
    Integer a=weighted-Integer(w-1)*j,b=limit+1-j;
    if (a<=0 || b<=0) break;
    Integer last=std::min<Integer>(b-1,(a-1)/w);
    Integer sum1=last*(last+1)/2,sum2=last*(last+1)*(2*last+1)/6;
    result+=(last+1)*a*b-(a+b*w)*sum1+w*sum2;
  }
  return result;
}

struct Row {
  int selected,m,limit,slope,y,cutoff;
  Integer weighted,nullity,quotient,margin,lambda,beta;
};
auto key(const Row& row) {
  return std::array<int,4>{row.selected,row.m,row.limit,row.slope};
}
void print_row(const Row& row) {
  std::cout<<"{\"selected_cap\":"<<row.selected<<",\"m\":"<<row.m
    <<",\"L\":"<<row.limit<<",\"S\":"<<row.slope<<",\"Y\":"<<row.y
    <<",\"k\":"<<row.cutoff<<",\"D\":"<<decimal(row.weighted)
    <<",\"nullity\":"<<decimal(row.nullity)
    <<",\"quotient\":"<<decimal(row.quotient)
    <<",\"margin\":"<<decimal(row.margin)
    <<",\"lambda\":"<<decimal(row.lambda)
    <<",\"beta\":"<<decimal(row.beta)<<"}";
}

int main(int argc,char** argv) {
  bool all=argc==2 && std::string(argv[1])=="--all";
  if (argc>1 && !all) { std::cerr<<"usage: astra-t-cutoff [--all]\n"; return 2; }
  std::vector<Row> rows;
  int shapes=0,shape_rejections=0,nonpositive_slopes=0,small_checks=0;
  for (int m=1;m<=max_m;++m) for (int s=0;s<=std::min(m,max_s);++s) {
    ++shapes;
    Integer weighted=Integer(m)*agreements;
    int y=int((weighted-1)/w);
    if (weighted+s>Integer(w)*(y+1)) { ++shape_rejections; continue; }
    int support=std::max(m+s,y+s+1);
    Integer rank0=local_rank(m,support,s);
    Integer rank_slope=local_rank(m,support+1,s)-rank0;
    Integer base=coefficient_count(weighted,support,s)-n*rank0;
    Integer lambda=coefficient_count(weighted,support+1,s)
                   -n*(rank0+rank_slope)-base;
    // The rectangular rank is affine for L>=m+S. The coefficient count is
    // affine once every weighted (Y,R) channel is present. Check the finite
    // region between these bounds too; no positive kernel is discarded there.
    for (int limit=m+s;limit<=support;++limit) {
      Integer rank=rank0+rank_slope*(limit-support);
      assert(rank==local_rank(m,limit,s));
      Integer nullity=coefficient_count(weighted,limit,s)-n*rank;
      assert(nullity<=0);
      ++small_checks;
    }
    if (lambda<=0) { ++nonpositive_slopes; continue; }
    Integer beta=base-lambda*support;
    auto quotient=[&](int k) { return coefficient_count(weighted,k,s); };
    // Q(k) is a sum of nonnegative weighted ramps, so Delta Q is monotone.
    // min_k ceil((Q(k)+1-beta)/lambda)-k-1 is attained where Delta Q
    // first reaches lambda: ceil is monotone and k is an integer.
    int low=0,high=y+s+2;
    assert(quotient(high+1)-quotient(high)>=lambda);
    while (low<high) {
      int middle=(low+high)/2;
      if (quotient(middle+1)-quotient(middle)>=lambda) high=middle;
      else low=middle+1;
    }
    // Before the crossing, L and the selected cap trade off. Preserve the
    // nondominated choices too: minimizing the selected cap alone can raise
    // the residual count because it raises L. At equal selected cap retain
    // the earlier/smaller L; at equal L retain the later/smaller selected cap.
    std::vector<Row> shape_rows;
    for (int k=0;k<=low;++k) {
      Integer limit=ceiling(quotient(k)+1-beta,lambda);
      assert(limit>support && limit>k);
      if (limit>max_l) continue;
      int L=int(limit),selected=L-k-1;
      Integer nullity=coefficient_count(weighted,L,s)-n*local_rank(m,L,s);
      assert(nullity==lambda*L+beta && nullity>quotient(k));
      assert(lambda*(L-1)+beta<=quotient(k));
      if (!shape_rows.empty() && shape_rows.back().selected==selected) continue;
      if (!shape_rows.empty() && shape_rows.back().limit==L) shape_rows.pop_back();
      shape_rows.push_back({selected,m,L,s,y,k,weighted,nullity,quotient(k),
                           nullity-quotient(k),lambda,beta});
    }
    rows.insert(rows.end(),shape_rows.begin(),shape_rows.end());
  }
  std::sort(rows.begin(),rows.end(),[](const Row& a,const Row& b){return key(a)<key(b);});
  assert(!rows.empty());
  assert((key(rows.front())==std::array<int,4>{6917,197,6922,61}));
  assert(rows.front().cutoff==4 && rows.front().margin==181447290);
  std::cout<<"{\"status\":\"BOUNDED_T_CAP_SEARCH_NOT_PROTOCOL_PROOF\","
    <<"\"m_max\":"<<max_m<<",\"S_max\":"<<max_s<<",\"L_max\":"<<max_l
    <<",\"shapes\":"<<shapes<<",\"shape_rejections\":"<<shape_rejections
    <<",\"nonpositive_slopes\":"<<nonpositive_slopes
    <<",\"small_L_checks\":"<<small_checks<<",\"eligible_rows\":"<<rows.size()
    <<",\"best_rows\":[";
  for (int i=0;i<(all?int(rows.size()):std::min<int>(20,rows.size()));++i) {
    if (i) std::cout<<",";
    print_row(rows[i]);
  }
  std::cout<<"]}\n";
}
