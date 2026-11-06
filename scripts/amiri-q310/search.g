# Search for counterexamples to Amiri, arXiv:2511.08320, Question 3.10.
# Q1-CE: G LCM, exp(H) | exp(G), psi(G) = psi(H) but different order types (none for |G| <= 255;
#   the least is order 256, see pgroups.g).
# Q2-CE: G LCM, H not LCM, exp(H) | exp(G), psi(H) >= psi(G).
# Run: gap -q -b search.g < /dev/null
IsLCMp := function(P)
  local p, e, i, S;
  if Size(P) = 1 then return true; fi;
  p := PrimePGroup(P); e := Exponent(P);
  for i in [1..Log(e,p)-1] do
    S := Filtered(AsList(P), x -> IsOne(x^(p^i)));
    if Size(Subgroup(P, S)) <> Size(S) then return false; fi;
  od;
  return true;
end;
IsLCM := G -> IsNilpotentGroup(G) and ForAll(SylowSystem(G), IsLCMp);
DataQ := function(G)
  local ords, cc, ot, d;
  cc := ConjugacyClasses(G);
  ot := Collected(Concatenation(List(cc, c -> ListWithIdenticalEntries(Size(c), Order(Representative(c))))));
  return rec(psi := Sum(ot, x -> x[1]*x[2]), ot := ot, exp := Exponent(G), lcm := IsLCM(G));
end;
SearchQ := function(n)
  local k, D, i, j, G, H, out;
  D := List([1..NrSmallGroups(n)], k -> DataQ(SmallGroup(n,k)));
  out := [];
  for i in [1..Length(D)] do if D[i].lcm then
    for j in [1..Length(D)] do if j <> i and D[i].exp mod D[j].exp = 0 then
      if D[i].psi = D[j].psi and D[i].ot <> D[j].ot then
        Print("Q1-CE n=",n," G=",i," H=",j," psi=",D[i].psi,"\n"); fi;
      if (not D[j].lcm) and D[j].psi >= D[i].psi then
        Print("Q2-CE n=",n," G=",i," H=",j," psiG=",D[i].psi," psiH=",D[j].psi, " strict=", D[j].psi > D[i].psi, "\n"); fi;
    fi; od;
  fi; od;
end;
for n in [2..255] do SearchQ(n); od;
Print("done\n");
QUIT;
