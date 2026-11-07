import json
bij={int(k):v for k,v in json.load(open('bij.json')).items()}
inv={t:[0]*288 for t in bij}
for t,v in bij.items():
    for i,j in enumerate(v): inv[t][j]=i
def lst(v): 
    s=", ".join(map(str,v)); 
    # wrap
    out=[];line="    ["
    for tok in s.split(", "):
        if len(line)+len(tok)+2>100: out.append(line); line="     "
        line+=tok+", "
    out.append(line.rstrip(", ")+"]")
    return "\n".join(out)
tabs=",\n".join(lst(bij[t]) for t in range(12))
itabs=",\n".join(lst(inv[t]) for t in range(12))
open('tables.lean.part','w').write(f"""/-- `tab[r]` lists, for each index `i` of `G610`, the index of `Φ_r (elt i)` in `G621`. -/
def tab : List (List ℕ) := [
{tabs}]

/-- The inverse tables. -/
def itab : List (List ℕ) := [
{itabs}]
""")
