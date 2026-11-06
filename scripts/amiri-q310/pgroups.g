# Amiri, arXiv:2511.08320, Question 3.10 (1), for groups of prime-power order p^n.
# For a p-group write c_i = #{x : x^(p^i) = 1}. Then psi = c_0 + sum_i p^i (c_i - c_{i-1}),
# and the order type is the vector c. An LCM p-group has every c_i a power of p
# (the sets Omega_i are subgroups), which filters the candidates for G.
# Prints CAND lines: G LCM (lcmG=true), exp(H) | exp(G), psi(G) = psi(H), different order type.
# RunP(2, 8) (order 256, ~1 h) finds the least counterexamples, e.g. G = SmallGroup(256, 13503)
# = C4 x C8 x Q8 against H = SmallGroup(256, 2761), psi = 1519.
# Run: gap -q -b pgroups.g < /dev/null
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
CVec := function(G, p, e)
  local cc, c, i;
  cc := ConjugacyClasses(G);
  c := List([0..e], i -> Sum(Filtered(cc, x -> IsOne(Representative(x)^(p^i))), Size));
  return c;
end;
RunP := function(p, n)
  local N, k, G, e, c, recs, byPsi, key, psi, r, s, isPow;
  N := NrSmallGroups(p^n); recs := [];
  for k in [1..N] do
    G := SmallGroup(p^n, k); e := Log(Exponent(G), p);
    c := CVec(G, p, e);
    psi := c[1] + Sum([1..e], i -> p^i * (c[i+1] - c[i]));
    isPow := ForAll(c, x -> x = p^Log(x,p));
    Add(recs, rec(k := k, e := e, c := c, psi := psi, pow := isPow));
  od;
  Print("computed ", p^n, "\n");
  for r in recs do if r.pow then
    for s in recs do
      if s.k <> r.k and s.e <= r.e and s.psi = r.psi then
        # compare full order type: pad s.c to length r.e+1
        if Concatenation(s.c, ListWithIdenticalEntries(r.e - s.e, p^n)) <> r.c then
          Print("CAND n=", p^n, " G=", r.k, " cG=", r.c, " H=", s.k, " cH=", s.c, " psi=", r.psi, " lcmG=", IsLCMp(SmallGroup(p^n, r.k)), "\n");
        fi;
      fi;
    od;
  fi; od;
  Print("done ", p^n, "\n");
end;
Print(IdGroup(DirectProduct(CyclicGroup(4), CyclicGroup(8), QuaternionGroup(8))), "\n");
RunP(2, 8);
QUIT;
