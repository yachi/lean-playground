LoadPackage("grape");
Read("funcs.g");
OrderStats := G -> Collected(List(G, Order));
LambdaGraph := function(elts, ords)
  local reps, gens, i, cyc, sets, n, orders, colours, d, gr;
  # cyclic subgroups as sets of positions
  sets := [];
  for i in [1..Length(elts)] do
    Add(sets, Set(List([1..ords[i]], k -> PositionSorted(elts, elts[i]^k))));
  od;
  sets := Set(sets);
  n := Length(sets);
  orders := List(sets, Length);
  gr := Graph(Group(()), [1..n], OnPoints,
      function(x, y) return x <> y and (IsSubset(sets[x], sets[y]) or IsSubset(sets[y], sets[x])); end, true);
  colours := List(Set(orders), d -> Filtered([1..n], i -> orders[i] = d));
  return rec(graph := gr, colourClasses := colours, orders := Set(orders));
end;
Sim5 := function(A, B)
  local t, D;
  if A.e <> B.e then return false; fi;
  for t in [0..A.e - 1] do
    D := rec();
    if FGCanon(PowMap(A.elts, t), D) <> FGCanon(PowMap(B.elts, t), D) then return false; fi;
  od;
  return true;
end;
Run61b := function(n)
  local nr, classes, key, cls, data, i, G, elts, ords, a, b, La, Lb, iso;
  nr := NrSmallGroups(n);
  classes := rec();
  for i in [1..nr] do
    G := SmallGroup(n, i);
    if IsNilpotentGroup(G) then continue; fi;
    key := String(OrderStats(G));
    if not IsBound(classes.(key)) then classes.(key) := []; fi;
    Add(classes.(key), i);
  od;
  for key in RecNames(classes) do
    cls := classes.(key);
    if Length(cls) < 2 then continue; fi;
    data := [];
    for i in cls do
      G := SmallGroup(n, i);
      elts := AsSSortedList(G);
      ords := List(elts, Order);
      Add(data, rec(id := i, e := Exponent(G), elts := elts, ords := ords, inv := DPGInv(elts, ords)));
    od;
    for a in [1..Length(data)] do for b in [a+1..Length(data)] do
      if Sim5(data[a], data[b]) then
        if data[a].inv <> data[b].inv then
          Print("COUNTEREXAMPLE(inv) ", n, " ", data[a].id, " ", data[b].id, "\n");
        else
          if not IsBound(data[a].L) then data[a].L := LambdaGraph(data[a].elts, data[a].ords); fi;
          if not IsBound(data[b].L) then data[b].L := LambdaGraph(data[b].elts, data[b].ords); fi;
          iso := data[a].L.orders = data[b].L.orders and IsIsomorphicGraph(
              rec(graph := data[a].L.graph, colourClasses := data[a].L.colourClasses),
              rec(graph := data[b].L.graph, colourClasses := data[b].L.colourClasses));
          if not iso then Print("COUNTEREXAMPLE(lambda) ", n, " ", data[a].id, " ", data[b].id, "\n");
          else Print("sim2 ", n, " ", data[a].id, " ", data[b].id, "\n"); fi;
        fi;
      fi;
    od; od;
  od;
end;

