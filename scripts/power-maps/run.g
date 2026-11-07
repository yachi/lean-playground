# Usage: gap -q run.g   (searches all orders 1..287; prints COUNTEREXAMPLE lines)
# The first counterexample appears at order 288: SmallGroup(288,610) vs SmallGroup(288,621).
Read("search.g");
for n in [1..288] do
  if n = 256 then continue; fi;   # 2-groups are nilpotent
  Run61b(n);
od;
QUIT;
