// BFS from target t over states with total length <= L, keyed by signed-perm canonical form.
// For each member s (by canonical key), output: id q(swap,nx,ny) moves from t reaching permS q s.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int8_t> W;
static W red(const W&w){W o;o.reserve(w.size());for(auto c:w){if(!o.empty()&&o.back()==-c)o.pop_back();else o.push_back(c);}return o;}
static W winv(const W&w){W o(w.rbegin(),w.rend());for(auto&c:o)c=-c;return o;}
static W cat3(const W&a,const W&b,const W&c){W o=a;o.insert(o.end(),b.begin(),b.end());o.insert(o.end(),c.begin(),c.end());return red(o);}
static inline int code(int8_t c){return c==1?0:c==-1?1:c==2?2:3;}
uint64_t pack(const W&a,const W&b){uint64_t k=a.size()|(b.size()<<5);int s=10;for(auto c:a){k|=(uint64_t)code(c)<<s;s+=2;}for(auto c:b){k|=(uint64_t)code(c)<<s;s+=2;}return k;}
pair<W,W> mv(int m,const W&a,const W&b){static W X={1},Xi={-1},Y={2},Yi={-2},E={};
  switch(m){case 0:return{winv(a),b};case 1:return{a,winv(b)};
  case 2:return{cat3(a,b,E),b};case 3:return{cat3(a,winv(b),E),b};
  case 4:return{a,cat3(b,a,E)};case 5:return{a,cat3(b,winv(a),E)};
  case 6:return{cat3(X,a,Xi),b};case 7:return{cat3(Xi,a,X),b};
  case 8:return{cat3(Y,a,Yi),b};case 9:return{cat3(Yi,a,Y),b};
  case 10:return{a,cat3(X,b,Xi)};case 11:return{a,cat3(Xi,b,X)};
  case 12:return{a,cat3(Y,b,Yi)};case 13:return{a,cat3(Yi,b,Y)};case 14:return{b,a};}return{a,b};}
// Lean SPerm semantics: swap x<->y, then negate letters of (new) x if nx, (new) y if ny
int8_t act(int p,int8_t a){bool sw=p&4,nx=p&2,ny=p&1;int b=a;if(sw){b=(abs(a)==1?2:1)*(a>0?1:-1);} if(abs(b)==1&&nx)b=-b; else if(abs(b)==2&&ny)b=-b; return b;}
W permW(int p,const W&w){W o=w;for(auto&c:o)c=act(p,c);return o;}
pair<uint64_t,int> canon(const W&a,const W&b){ // returns min key and perm q such that permS q (a,b) has min key
  uint64_t best=~0ULL;int bq=0;for(int p=0;p<8;p++){uint64_t k=pack(permW(p,a),permW(p,b));if(k<best){best=k;bq=p;}}return{best,bq};}
W parse(const string&s){W w;for(char c:s)w.push_back(c=='x'?1:c=='X'?-1:c=='y'?2:-2);return w;}
int main(int argc,char**argv){
  int L=atoi(argv[1]); string ta=argv[2],tb=argv[3]; long cap=atol(argv[4]);
  W A=parse(ta),B=parse(tb);
  map<uint64_t,vector<pair<string,pair<W,W>>>> want; string id,sa,sb;
  while(cin>>id>>sa>>sb){W a=parse(sa),b=parse(sb);want[canon(a,b).first].push_back({id,{a,b}});}
  unordered_map<uint64_t,pair<uint64_t,int8_t>> par; // canon key -> (parent canon key, move)
  unordered_map<uint64_t,pair<W,W>> ex; // canon -> exact state reached (only stored for wanted keys)
  deque<pair<W,W>> q; auto k0=canon(A,B).first; par[k0]={0,-1}; q.push_back({A,B});
  size_t found=0;
  auto report=[&](uint64_t k,const pair<W,W>&E){
    vector<int> path; uint64_t c=k; while(par[c].second>=0){path.push_back(par[c].second);c=par[c].first;} reverse(path.begin(),path.end());
    for(auto&[sid,S]:want[k]){ int qq=-1; for(int p=0;p<8;p++) if(permW(p,S.first)==E.first&&permW(p,S.second)==E.second){qq=p;break;}
      cout<<sid<<" "<<qq<<" "<<path.size()<<" ";for(size_t i=0;i<path.size();i++)cout<<(i?",":"")<<path[i];cout<<"\n";found++;}
  };
  if(want.count(k0))report(k0,{A,B});
  long n=0;
  while(!q.empty()&&n<cap&&found<(size_t)0+1e9){auto [a,b]=q.front();q.pop_front();n++;uint64_t kc=canon(a,b).first;
    for(int m=0;m<15;m++){auto [C,D]=mv(m,a,b);if((int)(C.size()+D.size())>L||C.empty()||D.empty())continue;
      uint64_t kk=canon(C,D).first; if(par.count(kk))continue; par[kk]={kc,(int8_t)m}; q.push_back({C,D});
      if(want.count(kk))report(kk,{C,D});}
  }
  cerr<<"visited "<<n<<" found "<<found<<endl;
}
