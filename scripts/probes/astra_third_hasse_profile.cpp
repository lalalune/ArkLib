// Exact third-Hasse local rank profiles. No surface-properness/prize claim.
#include <algorithm>
#include <charconv>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

using Integer = long long;
constexpr Integer production_prime = 2130706433;

Integer power(Integer a, Integer k, Integer prime) {
  Integer result = 1;
  for (; k; k >>= 1, a = a*a % prime)
    if (k & 1) result = result*a % prime;
  return result;
}

struct Column { int degree, y, r1, r2, r3; };
struct Row { int weight, v, r1, r2, r3; };
using Profile = std::vector<std::pair<int, int>>;

Profile base_profile(int h, int s1, int s2, int s3, Integer prime) {
  std::vector<Column> columns;
  for (int j=0; j<=std::min(s1,h); ++j)
    for (int k=0; k<=std::min(s2,h-j); ++k)
      for (int l=0; l<=std::min(s3,h-j-k); ++l)
        columns.push_back({3*h-j-2*k-3*l,h-j-k-l,j,k,l});
  std::sort(columns.begin(),columns.end(),[](Column a, Column b) {
    return std::tie(a.degree,a.y,a.r1,a.r2,a.r3) <
           std::tie(b.degree,b.y,b.r1,b.r2,b.r3);
  });
  std::vector<Row> rows;
  for (int v=0; v<=h; ++v)
    for (int a=0; a<=h-v; ++a)
      for (int b=0; b<=h-v-a; ++b)
        rows.push_back({2*a+b-v,v,a,b,h-v-a-b});
  std::sort(rows.begin(),rows.end(),[](Row a, Row b) {
    return std::tie(a.weight,a.v,a.r1,a.r2) >
           std::tie(b.weight,b.v,b.r1,b.r2);
  });
  // Pascal coefficients also work when h is at least the characteristic.
  std::vector<std::vector<Integer>> choose(h+1,std::vector<Integer>(h+1));
  for (int i=0; i<=h; ++i) {
    choose[i][0]=choose[i][i]=1;
    for (int j=1; j<i; ++j)
      choose[i][j]=(choose[i-1][j-1]+choose[i-1][j]) % prime;
  }
  int length=columns.size();
  std::vector<std::vector<Integer>> echelon(length);
  Profile result;
  for (auto row: rows) {
    std::vector<Integer> values(length);
    for (int j=0; j<length; ++j) {
      auto c=columns[j];
      int a=row.r1-c.r1, b=row.r2-c.r2, t=row.r3-c.r3;
      if (a<0 || b<0 || t<0 || row.v>c.y) continue;
      Integer value=choose[c.y][row.v]*choose[c.y-row.v][a] % prime;
      value=value*choose[c.y-row.v-a][b] % prime;
      values[j]=(b % 2) ? (prime-value) % prime : value;
    }
    for (int j=0; j<length; ++j) {
      if (!values[j]) continue;
      if (echelon[j].empty()) {
        Integer inverse=power(values[j],prime-2,prime);
        for (int k=j; k<length; ++k) values[k]=values[k]*inverse % prime;
        echelon[j]=values;
        result.push_back({columns[j].degree,row.weight});
        break;
      }
      Integer scalar=values[j];
      for (int k=j; k<length; ++k) {
        Integer value=(values[k]-scalar*echelon[j][k]) % prime;
        values[k]=value<0 ? value+prime : value;
      }
    }
    if (int(result.size())==length) break;
  }
  if (int(result.size())!=length) throw std::runtime_error("rank failure");
  return result;
}

int argument(const char* text, int low, int high) {
  int value=0;
  std::string input(text);
  auto parsed=std::from_chars(input.data(),input.data()+input.size(),value);
  if (parsed.ec!=std::errc() || parsed.ptr!=input.data()+input.size() ||
      value<low || value>high) throw std::runtime_error("argument out of range");
  return value;
}

void source(int m, int s1, int s2, int s3) {
  constexpr Integer n=262144,w=131071,agreements=181353;
  Integer D=m*agreements;
  int H=(D-1)/(w-3), stop=std::min(H,s1+s2+s3);
  std::vector<Profile> profiles;
  for (int h=0; h<=stop; ++h)
    profiles.push_back(base_profile(h,s1,s2,s3,production_prime));
  Integer slope=0,moment=0,running=0,value=0,first=-1;
  std::vector<Integer> coefficients,ranks;
  for (int h=0; h<=H; ++h) {
    Integer C=0,L=0,cap=D-(w-3)*h;
    int b=std::min(h,stop),shift=h-b;
    for (auto [input,output]: profiles[b]) {
      Integer degree=input+3*shift,weight=output+2*shift;
      C+=std::max(Integer(0),cap-degree);
      L+=std::max(Integer(0),std::min(cap,m+weight)-degree);
    }
    Integer excess=C-n*L;
    coefficients.push_back(C); ranks.push_back(L);
    slope+=excess; moment+=h*excess; running+=excess; value+=running;
    if (first<0 && value>0) first=h;
  }
  if (first<0 && slope>0) first=std::max(Integer(H),moment/slope);
  // This is a bounded research CLI, not an arbitrary-size arithmetic engine.
  if (first>100000) throw std::runtime_error("first total cap exceeds 100000");
  Integer C=0,L=0;
  if (first>=0) for (int h=0; h<=std::min(Integer(H),first); ++h) {
    C+=(first+1-h)*coefficients[h]; L+=(first+1-h)*ranks[h];
  }
  std::cout << "{\"m\":" << m << ",\"s1\":" << s1 << ",\"s2\":" << s2
            << ",\"s3\":" << s3 << ",\"D\":" << D << ",\"H\":" << H
            << ",\"T\":" << first << ",\"slope\":" << slope
            << ",\"moment\":" << moment << ",\"coefficients\":" << C
            << ",\"single_node_rank\":" << L << ",\"margin\":" << C-n*L << "}\n";
}

int main(int argc, char** argv) {
  try {
    if (argc==7 && std::string(argv[1])=="profile") {
      int h=argument(argv[2],0,55),s1=argument(argv[3],0,40);
      int s2=argument(argv[4],0,12),s3=argument(argv[5],0,3);
      Integer prime=argument(argv[6],2,production_prime);
      if (prime!=2 && prime!=5 && prime!=17 && prime!=production_prime)
        throw std::runtime_error("prime must be 2, 5, 17, or 2130706433");
      auto points=base_profile(h,s1,s2,s3,prime);
      std::cout << '[';
      for (size_t j=0; j<points.size(); ++j) {
        if (j) std::cout << ',';
        std::cout << '[' << points[j].first << ',' << points[j].second << ']';
      }
      std::cout << "]\n";
    } else if (argc==5) {
      source(argument(argv[1],1,160),argument(argv[2],0,40),
             argument(argv[3],0,12),argument(argv[4],0,3));
    } else throw std::runtime_error("use m S1 S2 S3, or profile h S1 S2 S3 prime");
    return 0;
  } catch (const std::exception& error) {
    std::cerr << "third-Hasse profile error: " << error.what() << '\n';
    return 1;
  }
}
