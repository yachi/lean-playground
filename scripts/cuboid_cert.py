#!/usr/bin/env python3
"""Certificate generator for the perfect-cuboid fiber descent.

For a fiber (m, n) of the master-tuple parametrization, with p = 2mn, q = m^2 + n^2 and
a = m^2 - n^2, the descent of LeanPlayground/PerfectCuboid/Descent.lean splits into the cases
(lam, c1, c2, c3, c4, sigma) enumerated by `fiberCases` in DescentCheck.lean. This script
enumerates them in exactly the same order, and for each case finds

* `torsionOK` (the case is a torsion translate and gives a smaller solution), or
* the cheapest modulus (N, l), N a prime power and l its prime, for which the residue check
  `check` (via `tupleOK [(N, l)]`) rules the case out.

The result is a certificate `List Cert` that the Lean kernel replays with `fiberCheckCert`: one
`torsionOK` or one O(N^2) residue check per case, instead of trying every modulus.

Everything below mirrors the Lean definitions of DescentCheck.lean literally (natural-number
semantics: truncated subtraction, x / 0 = 0, x % 0 = x), so that a certificate that passes
here also passes in the kernel.

The moduli tried are the prime powers N <= --max-modulus, smallest first (the kernel cost of
one check is O(N^2)), and then the prime factors of q above that bound (q itself is often
needed, e.g. for 12 : 35 and 28 : 45). If some case of a fiber cannot be certified (no torsion
family applies and no such modulus kills it), the case is reported on stderr and the fiber is
skipped: nothing is emitted for it.

Usage:
  python3 scripts/cuboid_cert.py [--max-modulus B] [--budget S] [--certs-only]
      [-o OUT.lean] m,n [m,n ...]
"""

import argparse
import math
import sys
import textwrap
import time

import numpy as np

# ---------------------------------------------------------------------------------------------
# Natural-number primitives with Lean semantics


def ndiv(x, y):
    return 0 if y == 0 else x // y


def nmod(x, y):
    return x if y == 0 else x % y


def nsub(x, y):
    return max(x - y, 0)


def nsqrt(n):
    return math.isqrt(n)


def negMod(N, x):
    return nmod(nsub(N, nmod(x, N)), N)


# ---------------------------------------------------------------------------------------------
# The residue check (`sqMask`, `okB`, `check`, `tupleOK`)


def sqMask(N, l, s, z):
    m = 0
    for d in range(N):
        if (nmod(d, l) == 0) == z:
            m |= 1 << nmod(s * d * d, N)
    return m


def okB(az, bz, gz, dz, c1z, c2z, c3z, c4z):
    return (not (az and bz) and not (az and gz) and not (az and dz) and not (bz and gz)
            and not (bz and dz) and not (gz and dz)
            and (not c1z or (not gz and not dz)) and (not c2z or (not az and not bz))
            and (not c3z or (not bz and not dz)) and (not c4z or (not az and not gz)))


def check_slow(N, l, A1, B1, s1, A2, B2, s2, c1, c2, c3, c4):
    """`check`, literally (half range `b, g <= N / 2`). Only used to test `check_fast_vec`."""
    m1 = {True: sqMask(N, l, s1, True), False: sqMask(N, l, s1, False)}
    m2 = {True: sqMask(N, l, s2, True), False: sqMask(N, l, s2, False)}
    for b in range(ndiv(N, 2) + 1):
        bb = nmod(b * b, N)
        for g in range(ndiv(N, 2) + 1):
            gg = nmod(g * g, N)
            r1 = nmod(A1 * gg + B1 * bb, N)
            r2 = nmod(A2 * bb + B2 * gg, N)
            for az in (True, False):
                for dz in (True, False):
                    if ((m1[dz] >> r1) & 1 and (m2[az] >> r2) & 1
                            and okB(az, nmod(b, l) == 0, nmod(g, l) == 0, dz, nmod(c1, l) == 0,
                                    nmod(c2, l) == 0, nmod(c3, l) == 0, nmod(c4, l) == 0)):
                        return False
    return True


def mask_array(N, l, s, z):
    m = sqMask(N, l, s, z)
    return np.array([(m >> i) & 1 == 1 for i in range(N)], dtype=bool)


def _okB_vec(az, bz, gz, dz, c1z, c2z, c3z, c4z):
    return (~(az & bz) & ~(az & gz) & ~(az & dz) & ~(bz & gz) & ~(bz & dz) & ~(gz & dz)
            & (~c1z | (~gz & ~dz)) & (~c2z | (~az & ~bz)) & (~c3z | (~bz & ~dz))
            & (~c4z | (~az & ~gz)))


def check_fast_vec(N, l, A1, B1, s1, A2, B2, s2, c1, c2, c3, c4):
    """`check`, vectorized over all `(b, g)`; the same result as the half range of `check`,
    since `b` and `N − b` give the same residues and flags (`exists_half`)."""
    r = np.arange(N, dtype=np.int64)
    sq = (r * r) % N
    e1 = (A1 % N * sq[None, :] + B1 % N * sq[:, None]) % N
    e2 = (A2 % N * sq[:, None] + B2 % N * sq[None, :]) % N
    bz = np.broadcast_to((r % l == 0)[:, None], (N, N))
    gz = np.broadcast_to((r % l == 0)[None, :], (N, N))
    c1z, c2z, c3z, c4z = (np.bool_(c % l == 0) for c in (c1, c2, c3, c4))
    for az in (np.bool_(True), np.bool_(False)):
        for dz in (np.bool_(True), np.bool_(False)):
            m1 = mask_array(N, l, s1, bool(dz))
            m2 = mask_array(N, l, s2, bool(az))
            ok = _okB_vec(az, bz, gz, dz, c1z, c2z, c3z, c4z)
            if np.any(m1[e1] & m2[e2] & ok):
                return False
    return True


def tuple_coeffs(N, q, lam, c1, c2, c3, c4, s):
    """The arguments of `check` in `tupleOK [(N, l)]`."""
    A1 = q * c3 ** 2
    B1 = lam * c1 ** 2
    g1 = math.gcd(math.gcd(A1, B1), s)
    A2 = q * c4 ** 2
    B2 = lam * c2 ** 2
    g2 = math.gcd(math.gcd(A2, B2), s)
    return (nmod(ndiv(A1, g1), N), negMod(N, ndiv(B1, g1)), nmod(ndiv(s, g1), N),
            nmod(ndiv(A2, g2), N), negMod(N, ndiv(B2, g2)), nmod(ndiv(s, g2), N))


def tupleOK1(N, l, q, lam, c1, c2, c3, c4, s, slow=False):
    co = tuple_coeffs(N, q, lam, c1, c2, c3, c4, s)
    f = check_slow if slow else check_fast_vec
    return f(N, l, *co, c1, c2, c3, c4)


# ---------------------------------------------------------------------------------------------
# The torsion families (`boundOK`, `linOK`, `quadDOK`, `quadKOK`, `torsionOK`)


def isSq(n):
    return nsqrt(n) * nsqrt(n) == n


def leB(weak, x, y):
    return x <= y if weak else x < y


def boundOK(weak, p, q, P, Nn, X, Y):
    return (leB(weak, Y, X) or leB(weak, Y * p ** 2, X * (4 * P ** 2))
            or leB(weak, Y * q ** 2, X * Nn ** 2))


def linOK(p, q, lam, c1, c2, c3, c4, s):
    return (isSq(q * lam) and isSq(lam * s) and isSq(q * s)
            and boundOK(False, p, q, c1 * c2, c3 * c4,
                        1 if q * c3 ** 2 == lam * c1 ** 2 + s else 4,
                        ndiv(c3, math.gcd(c3, c2 * nsqrt(q * lam))) ** 2))


def coprimePart(n, F, x):
    while n > 0:
        if math.gcd(F, x) == 1:
            return F
        F = ndiv(F, math.gcd(F, x))
        n -= 1
    return F


def quadDF(p, q, lam, c1, c2, c3, c4, s):
    return coprimePart(64, math.gcd(math.gcd(nsqrt(c1 * c2) * nsub(q, p) * (c3 * c4),
                                             nsqrt(c1 * c2) * s),
                                    math.gcd(nsqrt(c3 * c4) * c4 * c3 ** 2 * nsub(q, p),
                                             nsqrt(c3 * c4) * c4 * s)), lam * c1)


def quadDOK(p, q, lam, c1, c2, c3, c4, s):
    if not (isSq(c1 * c2) and isSq(c3 * c4) and isSq(s * nsub(q, p))):
        return False
    F = quadDF(p, q, lam, c1, c2, c3, c4, s)
    return (0 < F
            and nmod(nsqrt(c1 * c2) * nsub(q, p) * (c3 * c4), F) == 0
            and nmod(nsqrt(c1 * c2) * s, F) == 0
            and nmod(nsqrt(c3 * c4) * c4 * c3 ** 2 * nsub(q, p), F) == 0
            and nmod(nsqrt(c3 * c4) * c4 * s, F) == 0
            and math.gcd(F, lam * c1) == 1
            and boundOK(True, p, q, c1 * c2, c3 * c4, p * q * F ** 2,
                        c1 * c2 * nsub(q, p) ** 2 * (c3 * c4) ** 2))


def quadKOK(p, q, c1, c2, c3, c4, s):
    return (isSq(c1 * c2) and isSq(c3 * c4) and isSq(s * nsub(q, p))
            and boundOK(True, p, q, c1 * c2, c3 * c4, math.gcd(q, nsqrt(c3 * c4)) ** 2,
                        nsqrt(c3 * c4) ** 2 * (c1 * c2) ** 2))


def torsionOK1(p, q, lam, c1, c2, c3, c4, s):
    return (linOK(p, q, lam, c1, c2, c3, c4, s) or quadDOK(p, q, lam, c1, c2, c3, c4, s)
            or quadKOK(p, q, c1, c2, c3, c4, s))


def torsionOK(p, q, lam, c1, c2, c3, c4, s):
    return torsionOK1(p, q, lam, c1, c2, c3, c4, s) or torsionOK1(p, q, lam, c2, c1, c4, c3, s)


# ---------------------------------------------------------------------------------------------
# The case list (`divs`, `divsMul`, `divsSq`, `lamCases`, `fiberCases`)


def divs(n):
    out = []
    for d in range(nsqrt(n) + 1):
        if d != 0 and nmod(n, d) == 0:
            out += [d] if d * d == n else [d, ndiv(n, d)]
    return out


def divsMul(x, y):
    if math.gcd(x, y) == 1:
        return [u * v for u in divs(x) for v in divs(y)]
    return divs(x * y)


def divsSq(D, m):
    return [u * v for u in D for v in D if math.gcd(u * v, m) == u]


def caseKey(p, q, lam, c1, c3):
    return (lam * (p + 1) + c1) * (p * q + 1) + c3


def keyBound(p, q):
    """The upper end of the range of `Covered p q a`."""
    return (p * q + 1) * ((p + 1) * (p * q + 1))


def lamCases(p, q, a, lo, hi, lam):
    g = math.gcd(p, lam)
    pp, ll = ndiv(p, g), ndiv(lam, g)
    out = []
    sigmas = divsSq(divsMul(ll, a), ll * a)
    for c1 in divs(pp):
        if math.gcd(c1, ndiv(pp, c1)) != 1:
            continue
        for c3 in divs(ll):
            if math.gcd(c3, ndiv(ll, c3)) != 1 or not lo <= caseKey(p, q, lam, c1, c3) < hi:
                continue
            for s in sigmas:
                out.append((c1, ndiv(pp, c1), c3, ndiv(ll, c3), s))
    return out


def fiberCases(p, q, a, lo, hi):
    K = (p + 1) * (p * q + 1)
    return [(lam,) + c for lam in divs(p * q) if lam * K < hi and lo < (lam + 1) * K
            for c in lamCases(p, q, a, lo, hi, lam)]


# ---------------------------------------------------------------------------------------------
# Search


def prime_powers(bound):
    out = []
    for l in range(2, bound + 1):
        if all(l % d for d in range(2, nsqrt(l) + 1)):
            N = l
            while N <= bound:
                out.append((N, l))
                N *= l
    out.sort()
    return out


def certify(p, q, a, max_modulus):
    """The certificate of the fiber `(p, q, a)`, a list of `None` (torsion) or `(N, l)`, and
    the list of cases that could not be certified."""
    cases = fiberCases(p, q, a, 0, keyBound(p, q))
    big = [l for l in range(max_modulus + 1, q + 1)
           if q % l == 0 and all(l % d for d in range(2, nsqrt(l) + 1))]
    mods = prime_powers(max_modulus) + [(l, l) for l in big]
    cert, bad, memo = [], [], {}
    for (lam, c1, c2, c3, c4, s) in cases:
        key = (lam, c1, c2, c3, c4, s)
        if key in memo:
            cert.append(memo[key])
            continue
        if torsionOK(p, q, lam, c1, c2, c3, c4, s):
            entry = None
        else:
            entry = next(((N, l) for (N, l) in mods
                          if tupleOK1(N, l, q, lam, c1, c2, c3, c4, s)), False)
            if entry is False:
                bad.append(key)
        memo[key] = entry
        cert.append(entry)
    return cases, cert, bad


# ---------------------------------------------------------------------------------------------
# Lean output

ONES = ["zero", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine", "ten",
        "eleven", "twelve", "thirteen", "fourteen", "fifteen", "sixteen", "seventeen",
        "eighteen", "nineteen"]
TENS = ["", "", "twenty", "thirty", "forty", "fifty", "sixty", "seventy", "eighty", "ninety"]


def words(n):
    """`n` in English words without separators, as in `twelve_thirtyfive` (for `n < 100`)."""
    if n < 20:
        return ONES[n]
    return TENS[n // 10] + (ONES[n % 10] if n % 10 else "")


def name(n):
    """`n` in declaration names: in words below `100` (`thirteen_eightyfour`), else digits."""
    return words(n) if n < 100 else str(n)


def cost(e):
    """Estimated kernel seconds of one certificate entry: a fixed cost per case, plus the
    `(N / 2 + 1)²` iterations of `check`. Kernel memory grows about as fast (~65 MB/s)."""
    return 0.0045 if e is None else 0.0037 + 0.00012 * (e[0] // 2 + 1) ** 2


def chunks(p, q, cases, cert, budget):
    """Ranges `[lo, hi)` of `caseKey` whose cases cost at most about `budget` kernel seconds
    each. The cases of one `(λ, c₁, c₃)` are never split."""
    groups = {}
    for c, e in zip(cases, cert):
        k = caseKey(p, q, c[0], c[1], c[3])
        groups[k] = groups.get(k, 0) + cost(e)
    out, lo, t = [], 0, 0.0
    for k in sorted(groups):
        if t > 0 and t + groups[k] > budget:
            out.append((lo, k))
            lo, t = k, 0.0
        t += groups[k]
        if groups[k] > budget:
            print(f"  warning: the cases with (λ, c1, c3) of key {k} alone cost about "
                  f"{groups[k]:.0f}s", file=sys.stderr)
    out.append((lo, keyBound(p, q)))
    return out


def cert_entry(e):
    return ".torsion" if e is None else f".modulus {e[0]} {e[1]}"


def lean_list(entries, indent="  "):
    lines, line = [], indent + "["
    for i, e in enumerate(entries):
        s = cert_entry(e) + ("," if i + 1 < len(entries) else "]")
        if len(line) + 1 + len(s) > 100:
            lines.append(line)
            line = indent + " " + s
        else:
            line += ("" if line.endswith("[") else " ") + s
    if not entries:
        line += "]"
    lines.append(line)
    return "\n".join(lines)


def emit_certs(m, n, p, q, a, cases, cert, budget):
    """The certificate definitions and the theorem `covered_<p>_<q> : Covered p q a`."""
    tag = f"{name(p)}_{name(q)}"
    rngs = chunks(p, q, cases, cert, budget)
    out = []
    ntors = sum(1 for e in cert if e is None)
    out.append(f"/-! ### The fiber `(m, n) = ({m}, {n})`: `(p, q, a) = ({p}, {q}, {a})`, "
               f"{len(cases)} cases, {ntors} torsion -/\n")
    names = []
    for i, (lo, hi) in enumerate(rngs, 1):
        sel = [(c, e) for c, e in zip(cases, cert) if lo <= caseKey(p, q, c[0], c[1], c[3]) < hi]
        part = [e for _, e in sel]
        suffix = f"_{i}" if len(rngs) > 1 else ""
        first, last = min(sel, key=lambda x: caseKey(p, q, x[0][0], x[0][1], x[0][3]))[0], \
            max(sel, key=lambda x: caseKey(p, q, x[0][0], x[0][1], x[0][3]))[0]
        out.append(wrap_doc(f"The certificate of the {len(part)} cases with `(λ, c₁, c₃)` from "
                            f"`({first[0]}, {first[1]}, {first[3]})` to "
                            f"`({last[0]}, {last[1]}, {last[3]})`."))
        out.append(fit(f"def cert_{tag}{suffix} : List Cert :=", ":"))
        out.append(lean_list(part))
        out.append("")
        out.append(fit(f"theorem coveredOn_{tag}{suffix} : CoveredOn {p} {q} {a} {lo} {hi} :=",
                       ":"))
        out.append(fit(f"  coveredOn_of_fiberCheckCert (cert := cert_{tag}{suffix}) "
                       "(by decide +kernel)", ")"))
        out.append("")
        names.append(f"coveredOn_{tag}{suffix}")
    out.append(fit(f"theorem covered_{tag} : Covered {p} {q} {a} :=", ":"))
    out.append("  " + " <|\n    ".join([f"CoveredOn.trans {nm}" for nm in names[:-1]]
                                        + [names[-1]]))
    out.append("")
    return "\n".join(out)


def wrap_doc(text, first="/-- ", last=" -/"):
    """A doc comment, wrapped at 100 columns without breaking inside code spans."""
    parts = text.split("`")
    text = "`".join(x.replace(" ", "\0") if i % 2 else x for i, x in enumerate(parts))
    body = textwrap.fill(first + text + last, width=100, break_on_hyphens=False,
                         break_long_words=False)
    return body.replace("\0", " ")


def fit(line, at, indent="    "):
    """Break `line` after the separator `at` if it is longer than 100 columns."""
    if len(line) <= 100:
        return line
    i = line.index(at) + len(at)
    return line[:i].rstrip() + "\n" + indent + line[i:].lstrip()


def emit_theorems(m, n, p, q, a):
    """`not_isSol_…`, `not_isSquare_…` and `not_isPerfectCuboid_…` for one fiber."""
    tag = f"{name(p)}_{name(q)}"
    lo, hi = sorted((a, p))
    ratio = f"{name(lo)}_{name(hi)}"
    P2, Q2 = p * p, q * q
    sol = "\n".join([
        wrap_doc(f"The fiber `(m, n) = ({m}, {n})`: the descent for `(p, q) = ({p}, {q})`."),
        fit(f"theorem not_isSol_{tag} (M e r s : ℤ) : ¬ IsSol {p} {q} M e r s := by", "ℤ) :"),
        f"  simpa using not_isSol (p := {p}) (q := {q}) (a := {a}) (by norm_num) (by norm_num)",
        fit(f"    (by norm_num) (by norm_num) (by decide) covered_{tag} M e r s", "(by decide)"),
        ""])
    sq = "\n".join([
        wrap_doc(f"For rational `t ≠ 0`, `t² + {P2}` and `t² + {Q2}` are not both squares."),
        f"theorem not_isSquare_sq_add_{P2}_and_sq_add_{Q2} {{t : ℚ}} (ht : t ≠ 0) :",
        f"    ¬ (IsSquare (t ^ 2 + {P2}) ∧ IsSquare (t ^ 2 + {Q2})) := by",
        f"  have := Descent.not_isSquare_sq_add_sq_and_sq_add_sq (p := {p}) (q := {q}) (a := {a})",
        "    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)",
        f"    Descent.covered_{tag} ht",
        "  norm_num at this",
        "  exact fun h ↦ this h.1 h.2", ""])
    cub = "\n".join([
        wrap_doc(f"**No perfect cuboid has two edges in ratio `{lo} : {hi}`.** This is the fiber "
                 f"`(m, n) = ({m}, {n})`: with `X = {p}k`, `Z = {a}k`, the face diagonal "
                 f"`√(Y² + {P2}k²)` and the space diagonal `√(Y² + {Q2}k²)` cannot both be "
                 "integers."),
        fit(f"theorem not_isPerfectCuboid_{ratio} {{X Y Z : ℕ}} (h : IsPerfectCuboid X Y Z) :",
            "{X Y Z : ℕ}"),
        f"    {a} * X ≠ {p} * Z := by",
        "  intro hXZ",
        f"  obtain ⟨k, rfl⟩ : {p} ∣ X := by omega",
        f"  obtain rfl : Z = {a} * k := by omega",
        "  obtain ⟨r, hr⟩ := h.sq_ab",
        "  obtain ⟨s, hs⟩ := h.sq_abc",
        "  have hY := h.pos_b",
        "  have hk : 0 < k := by have := h.pos_a; omega",
        f"  apply Descent.not_isSol_{tag} (Y : ℤ) k r s",
        "  refine ⟨by exact_mod_cast hY.ne', by exact_mod_cast hk.ne', ?_, ?_⟩",
        fit(f"  · have : ((({p} * k) ^ 2 + Y ^ 2 : ℕ) : ℤ) = ((r * r : ℕ) : ℤ) := by rw [hr]",
            ":=", "      "),
        "    push_cast at this",
        "    linear_combination this",
        fit(f"  · have : ((({p} * k) ^ 2 + Y ^ 2 + ({a} * k) ^ 2 : ℕ) : ℤ) = ((s * s : ℕ) : ℤ) "
            ":= by rw [hs]", ":=", "      "),
        "    push_cast at this",
        "    linear_combination this", ""])
    return sol, sq, cub


HEADER_CERTS = """module

public import LeanPlayground.PerfectCuboid.DescentCheck

/-!
# Certificates for the fiber descent

Generated by `scripts/cuboid_cert.py` (do not edit by hand):

```
{args}
```

For each fiber `(p, q, a)` the certificate lists, for every case of `fiberCases p q a` in order,
`.torsion` (a torsion translate, `torsionOK`) or the modulus `.modulus N l` that rules the case
out. The kernel replays it with `fiberCheckCert` (`decide +kernel`), and `covered_…` is the
resulting `Covered p q a`, the hypothesis of `LeanPlayground.PerfectCuboid.Descent.not_isSol`.
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

"""

HEADER_FULL = """module

public import LeanPlayground.PerfectCuboid.Descent

/-!
# No perfect cuboid has two edges in ratio {ratios}

Generated by `scripts/cuboid_cert.py` (do not edit by hand):

```
{args}
```

These are fibers `(m, n)` of Peschmann's master-tuple parametrization (arXiv:2604.28072),
handled by the generic descent of `LeanPlayground.PerfectCuboid.Descent`: with
`(p, q, a) = (2mn, m² + n², m² − n²)`, a perfect cuboid with edges `X = p k`, `Z = a k`
would give a solution of `IsSol p q`. For each fiber the certificate lists, for every case of
`fiberCases p q a` in order, `.torsion` (a torsion translate, `torsionOK`) or the modulus
`.modulus N l` that rules the case out; the kernel replays it with `fiberCheckCert`.

## Main results

{results}
-/

@[expose] public section

namespace PerfectCuboid

namespace Descent

"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("fibers", nargs="+", help="fibers m,n")
    ap.add_argument("--max-modulus", type=int, default=211,
                    help="largest prime power N tried (default 211)")
    ap.add_argument("--budget", type=float, default=15.0,
                    help="estimated kernel seconds per declaration (default 15)")
    ap.add_argument("--certs-only", action="store_true",
                    help="emit only the certificates and `covered_…`, not the fiber theorems")
    ap.add_argument("-o", "--output", help="output Lean file (default: stdout)")
    args = ap.parse_args()

    blocks, fibers = [], []
    for spec in args.fibers:
        m, n = map(int, spec.split(","))
        if not (0 < n < m and math.gcd(m, n) == 1 and (m - n) % 2 == 1):
            print(f"fiber ({m}, {n}): need 0 < n < m, coprime, opposite parity; skipped",
                  file=sys.stderr)
            continue
        p, q, a = 2 * m * n, m * m + n * n, m * m - n * n
        t0 = time.time()
        cases, cert, bad = certify(p, q, a, args.max_modulus)
        dt = time.time() - t0
        if bad:
            print(f"fiber ({m}, {n}) = (p, q, a) = ({p}, {q}, {a}): {len(bad)} of {len(cases)} "
                  f"cases not certified (N <= {args.max_modulus}); fiber skipped:",
                  file=sys.stderr)
            for b in bad:
                print("  (lam, c1, c2, c3, c4, sigma) = " + str(b), file=sys.stderr)
            continue
        ms = sorted(set(e for e in cert if e is not None))
        print(f"fiber ({m}, {n}) = (p, q, a) = ({p}, {q}, {a}): {len(cases)} cases, "
              f"{sum(e is None for e in cert)} torsion, moduli {[N for N, _ in ms]}, "
              f"{dt:.1f}s", file=sys.stderr)
        blocks.append(emit_certs(m, n, p, q, a, cases, cert, args.budget))
        fibers.append((m, n, p, q, a))

    if not fibers:
        print("no fiber certified; nothing written", file=sys.stderr)
        sys.exit(1)
    cmd = " ".join(["python3 scripts/cuboid_cert.py"] + [
        x for x in sys.argv[1:] if x != args.output and x not in ("-o", "--output")])
    argstr = " \\\n".join(textwrap.wrap(cmd, width=96, subsequent_indent="  ",
                                         break_on_hyphens=False))
    if args.certs_only:
        text = HEADER_CERTS.format(args=argstr)
        text += "\n".join(blocks)
        text += "\nend Descent\n\nend PerfectCuboid\n"
    else:
        sols, sqs, cubs, results = [], [], [], []
        for (m, n, p, q, a) in fibers:
            sol, sq, cub = emit_theorems(m, n, p, q, a)
            sols.append(sol)
            sqs.append(sq)
            cubs.append(cub)
            lo, hi = sorted((a, p))
            results.append(wrap_doc(f"`not_isPerfectCuboid_{name(lo)}_{name(hi)}` — no perfect "
                                    f"cuboid has `{a} X = {p} Z`.", first="* ", last="")
                           .replace("\n", "\n  "))
        ratios = ", ".join(f"`{min(a, p)} : {max(a, p)}`" for (_, _, p, _, a) in fibers)
        text = HEADER_FULL.format(ratios=ratios or "(none)", args=argstr,
                                  results="\n".join(results) or "(none)")
        text += "\n".join(blocks)
        text += "\n".join(sols)
        text += "\nend Descent\n\n"
        text += "\n".join(sqs) + "\n" + "\n".join(cubs)
        text += "\nend PerfectCuboid\n"
    if args.output:
        with open(args.output, "w") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
