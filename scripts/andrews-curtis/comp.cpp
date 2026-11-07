// flood-fill AC components restricted to total length <= L, starting from pool presentations.
#include <bits/stdc++.h>
using namespace std;
typedef vector<int8_t> W; // letters: 1,-1,2,-2
static W red(const W&w){W o;o.reserve(w.size());for(auto c:w){if(!o.empty()&&o.back()==-c)o.pop_back();else o.push_back(c);}return o;}
static W winv(const W&w){W o(w.rbegin(),w.rend());for(auto&c:o)c=-c;return o;}
static W cat3(const W&a,const W&b,const W&c){W o=a;o.insert(o.end(),b.begin(),b.end());o.insert(o.end(),c.begin(),c.end());return red(o);}
static inline int code(int8_t c){return c==1?0:c==-1?1:c==2?2:3;}
static const int8_t DEC[4]={1,-1,2,-2};
uint64_t pack(const W&a,const W&b){uint64_t k=a.size()|(b.size()<<5);int s=10;for(auto c:a){k|=(uint64_t)code(c)<<s;s+=2;}for(auto c:b){k|=(uint64_t)code(c)<<s;s+=2;}return k;}
void unpack(uint64_t k,W&a,W&b){int la=k&31,lb=(k>>5)&31;int s=10;a.resize(la);b.resize(lb);for(int i=0;i<la;i++){a[i]=DEC[(k>>s)&3];s+=2;}for(int i=0;i<lb;i++){b[i]=DEC[(k>>s)&3];s+=2;}}
pair<W,W> mv(int m,const W&a,const W&b){static W X={1},Xi={-1},Y={2},Yi={-2},E={};
  switch(m){case 0:return{winv(a),b};case 1:return{a,winv(b)};
  case 2:return{cat3(a,b,E),b};case 3:return{cat3(a,winv(b),E),b};
  case 4:return{a,cat3(b,a,E)};case 5:return{a,cat3(b,winv(a),E)};
  case 6:return{cat3(X,a,Xi),b};case 7:return{cat3(Xi,a,X),b};
  case 8:return{cat3(Y,a,Yi),b};case 9:return{cat3(Yi,a,Y),b};
  case 10:return{a,cat3(X,b,Xi)};case 11:return{a,cat3(Xi,b,X)};
  case 12:return{a,cat3(Y,b,Yi)};case 13:return{a,cat3(Yi,b,Y)};}return{a,b};}
// symmetry canonical key: signed perms of generators (8), swap relators, invert each relator
W applyperm(const W&w,int p){W o=w;for(auto&c:o){int g=abs(c),s=c>0?1:-1;if(p&4)g=3-g; if((g==1&&(p&1))||(g==2&&(p&2)))s=-s;c=s*g;}return o;}
uint64_t canon(const W&a,const W&b){uint64_t best=~0ULL;for(int p=0;p<8;p++){W A=applyperm(a,p),B=applyperm(b,p);W Ai=winv(A),Bi=winv(B);
  const W* as[2]={&A,&Ai};const W* bs[2]={&B,&Bi};for(int i=0;i<2;i++)for(int j=0;j<2;j++){best=min(best,pack(*as[i],*bs[j]));best=min(best,pack(*bs[j],*as[i]));}}return best;}
int main(int argc,char**argv){
  int L=atoi(argv[1]); long cap=atol(argv[2]);
  vector<string> ids; vector<pair<W,W>> P; string id,sa,sb;
  auto parse=[](const string&s){W w;for(char c:s)w.push_back(c=='x'?1:c=='X'?-1:c=='y'?2:-2);return w;};
  while(cin>>id>>sa>>sb){ids.push_back(id);P.push_back({parse(sa),parse(sb)});}
  unordered_map<uint64_t,int> comp; comp.reserve(1<<26);
  vector<int> pc(P.size(),-1); vector<long> csize; vector<int> ctriv;
  for(size_t i=0;i<P.size();i++){
    uint64_t k0=canon(P[i].first,P[i].second);
    auto it=comp.find(k0); if(it!=comp.end()){pc[i]=it->second;continue;}
    int c=csize.size(); csize.push_back(0); ctriv.push_back(0);
    vector<uint64_t> st; comp[k0]=c; st.push_back(k0); long n=0; bool over=false;
    while(!st.empty()){uint64_t k=st.back();st.pop_back();n++;W a,b;unpack(k,a,b);
      if(a.size()+b.size()==2){ctriv[c]=1;}
      for(int m=0;m<14;m++){auto [C,D]=mv(m,a,b);if((int)(C.size()+D.size())>L||C.empty()||D.empty())continue;
        uint64_t kk=canon(C,D);auto r=comp.emplace(kk,c);if(r.second)st.push_back(kk);
        else if(r.first->second!=c){ /* merged with earlier comp: shouldn't happen since comps closed */ }}
      if(n>cap){over=true;break;}}
    if(over){csize[c]=-n;} else csize[c]=n; pc[i]=c;
    if(i%100==0)cerr<<i<<" comps="<<csize.size()<<" states="<<comp.size()<<endl;
  }
  for(size_t i=0;i<P.size();i++)cout<<ids[i]<<" "<<pc[i]<<" "<<csize[pc[i]]<<" "<<ctriv[pc[i]]<<"\n";
}
