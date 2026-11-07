from model import make
import json,sys
sys.setrecursionlimit(10000)
def pw(mul,e,g,n):
    r=e
    for _ in range(n): r=mul(r,g)
    return r
def structure(f,n):
    # cyclic nodes
    x=set(range(n))
    for _ in range(n): x={f[i] for i in x}
    cyc=x
    ch={i:[] for i in range(n)}
    for i in range(n):
        if i not in cyc: ch[f[i]].append(i)
    lab={}; table={}
    def L(v):
        k=tuple(sorted(L(c) for c in ch[v]))
        if k not in table: table[k]=len(table)
        lab[v]=table[k]; return lab[v]
    return cyc,ch,lab,table,L
def iso_fg(f1,f2,n):
    c1,ch1,lab1,T,L1=structure(f1,n)
    c2,ch2,lab2,_,_=structure(f2,n)
    # shared table: recompute with shared dict
    table={}
    def mk(ch,lab):
        def L(v):
            k=tuple(sorted(L(c) for c in ch[v]))
            if k not in table: table[k]=len(table)
            lab[v]=table[k]; return lab[v]
        return L
    lab1={};lab2={}
    L1=mk(ch1,lab1);L2=mk(ch2,lab2)
    for v in c1: L1(v)
    for v in c2: L2(v)
    def cycles(cyc,f,lab):
        seen=set();out=[]
        for v in sorted(cyc):
            if v in seen: continue
            seq=[];u=v
            while u not in seen: seen.add(u);seq.append(u);u=f[u]
            labs=[lab[u] for u in seq]
            rots=[(tuple(labs[i:]+labs[:i]),i) for i in range(len(seq))]
            best,i=min(rots)
            out.append((best,seq[i:]+seq[:i]))
        return sorted(out)
    C1=cycles(c1,f1,lab1);C2=cycles(c2,f2,lab2)
    assert [c[0] for c in C1]==[c[0] for c in C2], "cycle mismatch"
    phi={}
    def match(u,v):
        assert lab1[u]==lab2[v]
        phi[u]=v
        a=sorted(ch1[u],key=lambda x:lab1[x]); b=sorted(ch2[v],key=lambda x:lab2[x])
        for x,y in zip(a,b): match(x,y)
    for (k1,s1),(k2,s2) in zip(C1,C2):
        for u,v in zip(s1,s2): match(u,v)
    return phi
A=make(610);B=make(621)
ea,ma=A;eb,mb=B;e=(0,)*6;n=288
ia={g:i for i,g in enumerate(ea)}; ib={g:i for i,g in enumerate(eb)}
out={}
for t in range(12):
    f1=[ia[pw(ma,e,g,t)] for g in ea]; f2=[ib[pw(mb,e,g,t)] for g in eb]
    phi=iso_fg(f1,f2,n)
    assert sorted(phi.values())==list(range(n))
    for u in range(n): assert phi[f1[u]]==f2[phi[u]]
    out[t]=[phi[u] for u in range(n)]
    print(t,'ok')
json.dump(out,open('bij.json','w'))
