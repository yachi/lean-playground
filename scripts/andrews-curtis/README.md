# Andrews–Curtis: AC-classes in the SAIR ACC unsolved pool

Inputs and search code behind `LeanPlayground/AndrewsCurtis/{AK3Class,PoolClasses}.lean`.

- `unsolved-2026-11-07.txt`: the 2,672 presentations listed as unsolved in the public snapshot
  `https://api.sair.foundation/api/acc/discoveries/snapshot?problem=ac` at 2026-11-07 12:55 UTC,
  as `id r0 r1` with `x, X = x⁻¹, y, Y = y⁻¹` (relators from the official `ac.jsonl`),
  sorted by total length.
- `comp.cpp`: flood-fills the AC graph restricted to total relator length `≤ L` from every pool
  member, keyed up to signed generator permutations, relator order and relator inversion,
  and reports which members share a component. `./comp 20 20000000 < unsolved-2026-11-07.txt`.
  (Keys pack at most 27 letters; longer members are only trusted through the certificates.)
- `certify.cpp`: breadth-first search from a representative, keyed up to signed generator
  permutations, with moves `0–13` plus the relator swap `14`; prints, for each member it reaches,
  `id q n moves` where the moves take the representative to `permS q member`
  (`q` = bits `swap·4 + nx·2 + ny`). `./certify 20 xyxYXY xxxYYYY 100000000 < members.txt`.
- `ak3-class-L20.txt`: `certify` output from `AK(3)` for its 47-member class.
- `classes-L20.txt`: `class rep id q n moves` for the 228 classes (731 members) at `L = 20`.

The Lean files replay every certificate in the kernel, so the search code is not trusted.
