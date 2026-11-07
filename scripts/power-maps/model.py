import itertools
def make(kind):
    def w(A):
        a,b,c=A
        if kind==610: return (a,(b+c)%2,(c+2*a)%4)
        else: return (a,(b+a)%2,c)
    def kmul(k1,k2):
        A1,e1=k1[:3],k1[3]; A2=k2[:3]
        if e1: A2=w(A2)
        return (( A1[0]+A2[0])%2,(A1[1]+A2[1])%2,(A1[2]+A2[2])%4,(e1+k2[3])%2)
    def chi(k):
        a,b,c,e=k
        if kind==610: return (c%2,(c+e)%2)
        else: return (c%2,(a+c)%2)
    def mul(g,h):
        s1,t1=g[:2];k1=g[2:]; s2,t2=h[:2];k2=h[2:]
        x1,x2=chi(k1)
        s2=s2 if x1==0 else (-s2)%3
        t2=t2 if x2==0 else (-t2)%3
        return ((s1+s2)%3,(t1+t2)%3)+kmul(k1,k2)
    elts=[(s,t,a,b,c,e) for s in range(3) for t in range(3) for a in range(2) for b in range(2) for c in range(4) for e in range(2)]
    return elts,mul
if __name__=='__main__':
    for kind in (610,621):
        elts,mul=make(kind); idx={g:i for i,g in enumerate(elts)}
        # associativity check
        import random
        for _ in range(20000):
            a,b,c=random.choice(elts),random.choice(elts),random.choice(elts)
            assert mul(mul(a,b),c)==mul(a,mul(b,c))
        # regular perm rep generators (all elements' right mult would be large); output gens = a few elements
        gens=[(1,0,0,0,0,0),(0,1,0,0,0,0),(0,0,1,0,0,0),(0,0,0,1,0,0),(0,0,0,0,1,0),(0,0,0,0,0,1)]
        perms=[]
        for g in gens:
            perms.append([idx[mul(x,g)]+1 for x in elts])
        with open(f'perm{kind}.g','w') as f:
            f.write(f"gens{kind} := [" + ",".join("PermList(%s)"%p for p in perms) + "];\n")
        print(kind,'ok')
