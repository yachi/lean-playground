# Canonical invariants for Problem 6.1 (Fernandes-Qureshi-Reis-Ribas 2609.20516)
PowMap := function(elts, t)
  return List(elts, g -> PositionSorted(elts, g^t));
end;

# canonical id of functional graph f on [1..n], ids via global dictionary D (record of strings)
FGCanon := function(f, D)
  local n, cyc, x, i, inC, children, order, lab, done, stack, v, key, comps, seen, c, seq, rots, best, j, cs, res;
  n := Length(f);
  # cyclic nodes: image of f^n ; compute by iterating set
  x := [1..n];
  for i in [1..n] do
    x := Set(f{x});
    if Length(x) = Length(Set(f{x})) then break; fi;
  od;
  inC := BlistList([1..n], x);
  children := List([1..n], i -> []);
  for i in [1..n] do
    if not inC[i] then Add(children[f[i]], i); fi;
  od;
  # label trees bottom-up: process nodes in order of decreasing depth via DFS postorder
  lab := ListWithIdenticalEntries(n, 0);
  for i in x do
    stack := [[i, false]];
    while Length(stack) > 0 do
      v := Remove(stack);
      if v[2] then
        key := String(SortedList(List(children[v[1]], c -> lab[c])));
        if not IsBound(D.(key)) then D.(key) := Length(RecNames(D)) + 1; fi;
        lab[v[1]] := D.(key);
      else
        Add(stack, [v[1], true]);
        for c in children[v[1]] do Add(stack, [c, false]); od;
      fi;
    od;
  od;
  # cycles
  seen := BlistList([1..n], []);
  comps := [];
  for i in x do
    if not seen[i] then
      seq := []; j := i;
      repeat seen[j] := true; Add(seq, lab[j]); j := f[j]; until j = i;
      best := seq;
      for c in [1..Length(seq)-1] do
        rots := Concatenation(seq{[c+1..Length(seq)]}, seq{[1..c]});
        if rots < best then best := rots; fi;
      od;
      Add(comps, best);
    fi;
  od;
  Sort(comps);
  return comps;
end;

# directed power graph invariant: for each g, (ord g, sorted multiset of orders of h with g in <h>)
DPGInv := function(elts, ords)
  local n, bins, h, k, p, cur, o;
  n := Length(elts);
  bins := List([1..n], i -> []);
  for h in [1..n] do
    o := ords[h];
    cur := elts[h];
    for k in [1..o] do
      p := PositionSorted(elts, cur);
      Add(bins[p], o);
      cur := cur * elts[h];
    od;
  od;
  return SortedList(List([1..n], i -> [ords[i], SortedList(bins[i])]));
end;
