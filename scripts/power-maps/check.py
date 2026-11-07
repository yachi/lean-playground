from model import make
from collections import Counter
def pw(mul,e,g,n):
    r=e
    for _ in range(n): r=mul(r,g)
    return r
for kind in (610,621):
    elts,mul=make(kind); e=(0,)*6
    P={ (g,n):pw(mul,e,g,n) for g in elts for n in range(13)}
    cnt=Counter()
    for g in elts:
        g4,g6,g8=P[g,4],P[g,6],P[g,8]
        if g4==e or g6==e: continue
        a=sum(1 for h in elts if (P[h,4]==g4 or P[h,4]==g8) and P[h,6]!=e)
        b=sum(1 for k in elts if P[k,2]==g6)
        cnt[(a,b)]+=1
    print(kind,sorted(cnt.items()))
