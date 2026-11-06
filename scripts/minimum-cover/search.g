# For every non-abelian group G of order p^n, merge (componentwise max of the sorted
# exponent partitions) the types of all abelian subgroups of G.  If the merged type has
# total exponent > n, no abelian group of order |G| contains all abelian subgroups of G
# (Cameron et al., Lemma 7.5), so the set of those subgroups has no abelian minimum cover.
# Only hit for p^n in {2^3..2^6, 3^3..3^5, 5^3, 5^4}: SmallGroup(64,99), merged type [3,2,1,1].
Merge := function(L) local m,i,l; m:=[]; for l in L do l:=Reversed(SortedList(l)); for i in [1..Length(l)] do if i>Length(m) then Add(m,l[i]); else m[i]:=Maximum(m[i],l[i]); fi; od; od; return m; end;
CoverScan := function(p, n) local i,G,ab,types,m;
  for i in [1..NrSmallGroups(p^n)] do G:=SmallGroup(p^n,i);
    if IsAbelian(G) then continue; fi;
    ab := Filtered(List(ConjugacyClassesSubgroups(G), Representative), IsAbelian);
    types := Filtered(List(ab, H->List(AbelianInvariants(H), q->Length(Factors(q)))), t->t<>[]);
    m := Merge(types);
    if Sum(m) > n then Print("HIT ", p,"^",n," id ",i," ",m,"\n"); fi;
  od; Print("done ",p,"^",n,"\n"); end;
for pn in [[2,3],[2,4],[2,5],[2,6],[3,3],[3,4],[3,5],[5,3],[5,4]] do CoverScan(pn[1],pn[2]); od;
QUIT;
