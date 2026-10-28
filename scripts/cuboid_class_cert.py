#!/usr/bin/env python3
"""Grouped certificate generator for the perfect-cuboid descent with the class lemma.

For a fiber (m, n) with U = m^2 - n^2, V = 2mn, W = m^2 + n^2, the curve E'' of the fiber is
2-isogenous to the pair curve of (p, q) = (2UV, W^2) (`IsPerfectCuboid.not_onFiber_of_isogeny`
in LeanPlayground/PerfectCuboid/Kubert.lean), with D = q^2 - p^2 = (U^2 - V^2)^2. The descent
of LeanPlayground/PerfectCuboid/Descent.lean splits into millions of cases
(lam, c1, c2, c3, c4, sigma) for this pair. LeanPlayground/PerfectCuboid/DescentClass.lean
groups them by lam and by sigma0, where sigma = sigma0 t^2 (`sqGroups`), and kills a whole group
when its 2-descent class (q lam, D lam sigma0) is not in the 2-Selmer group, as seen modulo a
prime power (`classCheck`). The few surviving groups are split into their cases, each handled
by a torsion family (`torsionOKL`) or a residue check (`tupleOK`).

This script mirrors the Lean definitions of DescentClass.lean literally (the divisor lists
`divsF`, `sqGroups`, `groupCases` in the same order), finds the certificate, and writes the
Lean file of the fiber. The functions of the torsion families and the residue check come from
scripts/cuboid_cert.py.

With --sq, the pair is (U^2, V^2) of E'' itself (`IsPerfectCuboid.not_onFiber_of_sq`): its
solutions with M^2 = pq e^2 come from the point T4 of order 4, so the cases in the class of a
point of order 8 use family TR of LeanPlayground/PerfectCuboid/DescentTR.lean (`trOK`).

Usage:
  python3 scripts/cuboid_class_cert.py [--budget S] [--parts K] [--sq] [-d DIR] m,n
"""

import argparse
import math
import os
import sys
import time

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import cuboid_cert as C  # noqa: E402

# ---------------------------------------------------------------------------------------------
# Factorizations (`primeB`, `valF`, `facOf`, `prodF`, `powsUpTo`, `divsF`, `sqGroups`)


def primeB(l):
    return l >= 2 and all(l % d != 0 for d in range(2, l))


def valF(l, f, n):
    v = 0
    while f > 0 and n != 0 and C.nmod(n, l) == 0:
        n = C.ndiv(n, l)
        v += 1
        f -= 1
    return v


def facOf(Ps, n):
    return [(l, valF(l, 256, n)) for l in Ps]


def prodF(F):
    r = 1
    for l, e in F:
        r *= l ** e
    return r


def powsUpTo(l, e):
    return [l ** i for i in range(e + 1)]


def divsF(F):
    if not F:
        return [1]
    (l, e), rest = F[0], F[1:]
    return C.divsProd(powsUpTo(l, e), l ** e, divsF(rest))


def sqGroups(F):
    if not F:
        return [(1, [1])]
    (l, e), rest = F[0], F[1:]
    out = []
    for s0, ts in sqGroups(rest):
        out.append((s0, [l ** j * t for j in range(e // 2 + 1) for t in ts]))
        if e != 0:
            out.append((l * s0, [l ** j * t for j in range((e - 1) // 2 + 1) for t in ts]))
    return out


def groupCases(pp, ll, s0, ts, C1, C3):
    out = []
    for t in ts:
        for c1 in C1:
            if math.gcd(c1, C.ndiv(pp, c1)) != 1:
                continue
            for c3 in C3:
                if math.gcd(c3, C.ndiv(ll, c3)) != 1:
                    continue
                out.append((c1, C.ndiv(pp, c1), c3, C.ndiv(ll, c3), s0 * t * t))
    return out


def sqf(F):
    """The squarefree part of `prodF F`."""
    r = 1
    for l, e in F:
        if e % 2:
            r *= l
    return r


def addF(F, G):
    return [(l, e + f) for (l, e), (_, f) in zip(F, G)]


# ---------------------------------------------------------------------------------------------
# The torsion families with a box limit (`quadKOKL`, `torsionOK1L`, `torsionOKL`)


def quadKOKL(lim, p, q, lam, c1, c2, c3, c4, s):
    """Mirrors `quadKOKL`; also adds the small cases searched to `PAIRS[0]`."""
    ok, pairs = C.quadKOKL(lim, p, q, lam, c1, c2, c3, c4, s)
    PAIRS[0] += pairs
    return ok


PAIRS = [0]


def torsionOK1L(lim, p, q, lam, c1, c2, c3, c4, s):
    return (C.linOK(p, q, lam, c1, c2, c3, c4, s) or C.quadDOK(p, q, lam, c1, c2, c3, c4, s)
            or quadKOKL(lim, p, q, lam, c1, c2, c3, c4, s))


def torsionOKL(lim, p, q, lam, c1, c2, c3, c4, s):
    return (torsionOK1L(lim, p, q, lam, c1, c2, c3, c4, s)
            or torsionOK1L(lim, p, q, lam, c2, c1, c4, c3, s))


# ---------------------------------------------------------------------------------------------
# The class check (`classCheck`)

SQ = {}


def sqset(N):
    if N not in SQ:
        s = np.zeros(N, bool)
        d = np.arange(N, dtype=np.int64)
        s[(d * d) % N] = True
        SQ[N] = s
    return SQ[N]


def classCheck(N, l, a, b, c, P, Q):
    S = sqset(N)
    r = np.arange(N, dtype=np.int64)
    x = a * (r * r % N) % N
    if np.any(S[b * ((x + P) % N) % N] & S[c * ((x + Q) % N) % N]):
        return False
    t = np.arange(N // l, dtype=np.int64)
    y = (l * t) * (l * t) % N
    return not np.any(S[b * ((a + P * y) % N) % N] & S[c * ((a + Q * y) % N) % N])


# ---------------------------------------------------------------------------------------------
# The certificate


# ---------------------------------------------------------------------------------------------
# Family TR (`trOK` of DescentTR.lean), for the pair `(U², V²)`


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pscale(c, a):
    return [c * x for x in a]


def psub(a, b):
    return padd(a, pscale(-1, b))


def pmul(a, b):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def ppow(a, k):
    out = [1]
    for _ in range(k):
        out = pmul(out, a)
    return out


def tr_polys(p, q, L, c1, c2, c3, c4, d1):
    """`trG` and `trR0 · trRM · trRe` of DescentTR.lean."""
    A, Dd, T = [-(L * c2 ** 2), q * c4 ** 2], [q * c3 ** 2, -(L * c1 ** 2)], [0, 1]
    d2, d3, DD = d1 + p ** 2, d1 + q ** 2, q ** 2 - p ** 2
    AD = pmul(A, Dd)
    A0 = psub(pscale(c1 ** 2 * c4 ** 2 * q * L,
                     padd(pscale(d2 * d3, AD), pscale(d1 * c3 ** 2 * c4 ** 2 * DD ** 2, T))),
              pscale(p * q, ppow(psub(pscale(q * L * c1 ** 2, A), pscale(d1 * c4 ** 2, Dd)), 2)))
    R0 = psub(ppow(A0, 2), pscale(4 * c1 ** 4 * c3 ** 2 * c4 ** 6 * q ** 2 * L ** 2 * DD ** 2 * d1
                                  * d2 * d3, pmul(AD, T)))
    RM = psub(pscale(d2 * d3, AD), pscale(d1 * c3 ** 2 * c4 ** 2 * DD ** 2, T))
    Re = psub(pscale(q * L * c1 ** 2, A), pscale(d1 * c4 ** 2, Dd))
    K1, K2 = pscale(c1 ** 2, pmul(A, T)), pscale(c2 ** 2, Dd)
    G = psub(pscale(p, ppow(psub(K1, K2), 2)), pscale(4 * q, pmul(K1, K2)))
    return G, pmul(pmul(R0, RM), Re)


def pdivexact(a, b):
    """`a / b` over `ℚ` if `b` divides `a`, else `None` (little-endian lists)."""
    from fractions import Fraction
    a = [Fraction(x) for x in a]
    while b and b[-1] == 0:
        b = b[:-1]
    while a and a[-1] == 0:
        a.pop()
    if len(a) < len(b):
        return [] if not a else None
    out = [Fraction(0)] * (len(a) - len(b) + 1)
    for i in range(len(out) - 1, -1, -1):
        c = a[i + len(b) - 1] / b[-1]
        out[i] = c
        for j, y in enumerate(b):
            a[i + j] -= c * y
    return out if all(x == 0 for x in a) else None


def tr_cert(p, q, L, c1, c2, c3, c4, d1, kmax=8):
    """`(N, k, Z)` with `N G^k = R Z`, or `None`."""
    G, R = tr_polys(p, q, L, c1, c2, c3, c4, d1)
    for k in range(1, kmax + 1):
        Gk = ppow(G, k)
        Zq = pdivexact(Gk, R)
        if Zq is not None:
            N = 1
            for z in Zq:
                N = N * z.denominator // math.gcd(N, z.denominator)
            Z = [int(z * N) for z in Zq]
            assert all(x == 0 for x in psub(pscale(N, Gk), pmul(R, Z)))
            return N, k, Z
    return None


def tr_points(U, V, W):
    """The `x > 0` of the half-points of `T₄ = (U²V², ·)`, with `y_T`."""
    p, q = sorted((U * U, V * V))
    out = set()
    for e1 in (1, -1):
        for e2 in (1, -1):
            x = U * U * V * V + e1 * U * U * V * W + e2 * U * V * V * W + e1 * e2 * U * V * W * W
            if x > 0:
                y2 = x * (x + p * p) * (x + q * q)
                y = math.isqrt(y2)
                if y * y == y2:
                    out.add((x, y))
    return sorted(out)


def trOK(p, q, lam, c1, c2, c3, c4, s, Ts):
    """A certificate `("tr", d₁, y_T, X, Y, N, k, Z, pairs)` of family TR, or `None`."""
    best = None
    D = q * q - p * p
    for d1, yT in Ts:
        d2, d3 = d1 + p * p, d1 + q * q
        if not (C.isSq(q * lam * d1) and C.isSq(D * lam * s * d2) and C.isSq(D * q * s * d3)):
            continue
        w, h, H = C.nsqrt(q * lam * d1), C.nsqrt(D * lam * s * d2), C.nsqrt(D * q * s * d3)
        F = math.gcd(math.gcd(c4 * c1 * w * d2 * d3 * s ** 2, c4 * c1 * d1 * c3 * c4 * h * H),
                     math.gcd(yT * s ** 2 * q * lam * c1 ** 2, yT * s ** 2 * d1 * c4 ** 2))
        KA = (yT * s ** 2 * q * lam * c1 ** 2) ** 2 * (q * c4 ** 2)
        KB = (yT * s ** 2 * d1 * c4 ** 2) ** 2 * (q * c3 ** 2)
        X = max(0, math.isqrt(KA // (s * F * F)) - 1)
        while not KA < s * F * F * (X + 1) ** 2:
            X += 1
        Y = max(0, math.isqrt(KB // (s * F * F)) - 1)
        while not KB < s * F * F * (Y + 1) ** 2:
            Y += 1
        pairs = C.hypPairs(X, Y)
        if best is not None and pairs >= best[-1]:
            continue
        if not C.hypCheck(q, lam, c1, c2, c3, c4, s, X, Y, p):
            continue
        cert = tr_cert(p, q, lam, c1, c2, c3, c4, d1)
        if cert is None:
            continue
        best = ("tr", d1, yT, X, Y, *cert, pairs)
    return best


def certify(p, q, D, Ps, max_class=10 ** 6, max_modulus=211, lims=(65536, 1 << 20), Ts=None):
    """For each `λ` of `divsF (facOf Ps (p q))`: `(λ, a₀, [group certificates])`, where a group
    certificate is `("kill", key, b₀)` or `("cases", [tuple certificates])`, and a tuple
    certificate is `("torsion", lim, pairs)` (`pairs` small cases searched), `("modulus", N, l)`
    or, with the torsion points `Ts` of family TR, `("tr", …)`. Also returns the keys in
    order."""
    mods = []
    for l in Ps:
        N, k = l, 1
        while N <= max_class:
            mods.append((N, l, k))
            N, k = N * l, k + 1
    mods.sort()
    tmods = C.prime_powers(max_modulus)
    keys, keyidx = [], {}
    P2, Q2 = p * p, q * q
    FD = facOf(Ps, D)
    out, bad = [], []
    stats = dict(groups=0, killed=0, tuples=0, torsion=0)
    for lam in divsF(facOf(Ps, p * q)):
        g = math.gcd(p, lam)
        pp, ll = C.ndiv(p, g), C.ndiv(lam, g)
        F1 = facOf(Ps, pp)
        F3 = facOf(Ps, ll)
        Fs = facOf(Ps, ll * ll * D)
        assert prodF(F1) == pp and prodF(F3) == ll and prodF(Fs) == ll * ll * D
        Fql = facOf(Ps, q * lam)
        assert prodF(Fql) == q * lam
        a0 = sqf(Fql)
        Fl = facOf(Ps, lam)
        C1, C3 = divsF(F1), divsF(F3)
        gcs, sigs = [], []
        for s0, ts in sqGroups(Fs):
            stats["groups"] += 1
            b0 = sqf(addF(addF(FD, Fl), facOf(Ps, s0)))
            assert C.isSq(D * lam * s0 * b0) and C.isSq(q * lam * a0)
            hit = None
            for N, l, k in mods:
                key = (N, l, k, a0 % N, b0 % N)
                if key in keyidx or classCheck(N, l, a0 % N, b0 % N, a0 * b0 % N, P2 % N,
                                               Q2 % N):
                    hit = key
                    break
            if hit is not None:
                stats["killed"] += 1
                if hit not in keyidx:
                    keyidx[hit] = len(keys)
                    keys.append(hit)
                gcs.append(("kill", keyidx[hit], b0))
                sigs.append([])
                continue
            tcs = []
            sigs.append([])
            for (c1, c2, c3, c4, s) in groupCases(pp, ll, s0, ts, C1, C3):
                stats["tuples"] += 1
                e = None
                PAIRS[0] = 0
                if torsionOKL(lims[0], p, q, lam, c1, c2, c3, c4, s):
                    e = ("torsion", lims[0], PAIRS[0])
                    stats["torsion"] += 1
                else:
                    e = next((("modulus", N, l) for (N, l) in tmods
                              if C.tupleOK1(N, l, q, lam, c1, c2, c3, c4, s)), None)
                if e is None:
                    for lim in lims[1:]:
                        PAIRS[0] = 0
                        if torsionOKL(lim, p, q, lam, c1, c2, c3, c4, s):
                            e = ("torsion", lim, PAIRS[0])
                            stats["torsion"] += 1
                            break
                if e is None and Ts:
                    e = trOK(p, q, lam, c1, c2, c3, c4, s, Ts)
                    if e is not None:
                        stats["tr"] = stats.get("tr", 0) + 1
                if e is None:
                    bad.append((lam, c1, c2, c3, c4, s))
                tcs.append(e)
                sigs[-1].append(s)
            gcs.append(("cases", tcs))
        out.append((lam, a0, gcs, sigs))
    return out, keys, bad, stats


# ---------------------------------------------------------------------------------------------
# Lean output


def cost_t(e):
    """Estimated kernel seconds of one case: a torsion family, or the `O(N²)` residue check."""
    if e[0] == "torsion":
        return 0.010 + 0.0005 * e[2]
    if e[0] == "tr":
        return 0.2 + 0.0005 * e[-1]
    return 0.0037 + 0.00012 * (e[1] // 2 + 1) ** 2


def pieces(c, S, budget):
    """`c` restricted to `σlo ≤ σ < σhi`, and the cost of that piece, for the ranges `[σlo, σhi)`
    of about `budget` seconds that cover `[0, S)`."""
    lam, a0, gcs, tups = c
    base = 0.02 + sum(0.003 for gc in gcs if gc[0] == "kill")
    sig = sorted((s, cost_t(e)) for tl, gc in zip(tups, gcs) if gc[0] == "cases"
                 for s, e in zip(tl, gc[1]))
    cuts, lo, t = [], 0, base
    for i, (s, k) in enumerate(sig):
        if t > base and t + k > budget and s != sig[i - 1][0]:
            cuts.append((lo, s, t))
            lo, t = s, base
        t += k
    cuts.append((lo, S, t))
    return cuts


def restrict(c, slo, shi):
    lam, a0, gcs, tups = c
    out = []
    for tl, gc in zip(tups, gcs):
        if gc[0] == "kill":
            out.append(gc)
        else:
            out.append(("cases", [e for s, e in zip(tl, gc[1]) if slo <= s < shi]))
    return (lam, a0, out)


def chunks(cert, pq, S, budget):
    """Rectangles `(λlo, λhi, σlo, σhi, cost, entries)` of about `budget` kernel seconds each,
    with the entries in the order of `divsF`. Consecutive `λ` (by value) are joined while they
    fit; a `λ` too big alone is cut into ranges of `σ`."""
    pos = {c[0]: i for i, c in enumerate(cert)}
    out = chunks_(sorted(cert, key=lambda c: c[0]), pq, S, budget)
    return [(a, b, c, d, t, sorted(es, key=lambda e: pos[e[0]])) for a, b, c, d, t, es in out]


def chunks_(byval, pq, S, budget):
    out, cur, lo, t = [], [], 0, 0.0
    for i, c in enumerate(byval):
        nxt = byval[i + 1][0] if i + 1 < len(byval) else pq + 1
        ps = pieces(c, S, budget)
        if len(ps) > 1:
            if cur:
                out.append((lo, c[0], 0, S, t, cur))
            for slo, shi, k in ps:
                out.append((c[0], nxt, slo, shi, k, [restrict(c, slo, shi)]))
            cur, lo, t = [], nxt, 0.0
            continue
        k = ps[0][2]
        if cur and t + k > budget:
            out.append((lo, c[0], 0, S, t, cur))
            cur, lo, t = [], c[0], 0.0
        cur.append(restrict(c, 0, S))
        t += k
    if cur or not out:
        out.append((lo, pq + 1, 0, S, t, cur))
    return out


def tcert_str(e):
    if e[0] == "tr":
        _, d1, yT, X, Y, N, k, Z, _ = e
        return f".tr {d1} {yT} {X} {Y} {N} {k} [" + ", ".join(map(str, Z)) + "]"
    return f".torsion {e[1]}" if e[0] == "torsion" else f".modulus {e[1]} {e[2]}"


def wrap(items, indent, width=100):
    """`[a, b, …]` wrapped at `width` columns."""
    lines, line = [], indent + "["
    for i, s in enumerate(items):
        s = s + ("," if i + 1 < len(items) else "]")
        if len(line) + 1 + len(s) > width and not line.endswith("["):
            lines.append(line)
            line = indent + " " + s
        else:
            line += ("" if line.endswith("[") else " ") + s
    if not items:
        line += "]"
    lines.append(line)
    return "\n".join(lines)


def gcert_str(gc):
    if gc[0] == "kill":
        return f".kill {gc[1]} {gc[2]}"
    return ".cases [" + ", ".join(tcert_str(e) for e in gc[1]) + "]"


def lam_str(c, indent):
    lam, a0, gcs = c
    return wrap_tree(f"({a0}, [" + ", ".join(gcert_str(gc) for gc in gcs) + "])", indent)


def ktree(keys):
    """The Lean `KTree` of the keys: index `0` at the root, odd indices on the left, even
    ones on the right."""
    def build(ks):
        if not ks:
            return ".leaf"
        N, l, k, A, B = ks[0]
        return f"(.node {build(ks[1::2])} ({N}, {l}, {k}, {A}, {B}) {build(ks[2::2])})"
    return build(keys)


def wrap_tree(s, indent="  ", width=100):
    """`s` broken at spaces into lines of at most `width` columns."""
    out, line = [], indent
    for tok in s.split(" "):
        if len(line) + len(tok) + 1 > width and line.strip():
            out.append(line.rstrip())
            line = indent + "  "
        line += tok + " "
    out.append(line.rstrip())
    return "\n".join(out)


def cases_on(*args):
    """The statement `CasesOn p q D lo hi slo shi [true]`, broken before `slo` if it is too
    long. In the `--sq` mode (`SQMODE`), the last argument `t4 = true` allows family TR."""
    if SQMODE:
        args = args + ("true",)
    line = "    CasesOn " + " ".join(map(str, args)) + " :="
    if len(line) <= 100:
        return line
    return ("    CasesOn " + " ".join(map(str, args[:5])) + "\n      "
            + " ".join(map(str, args[5:])) + " :=")


def chunk_lines(tag, p, q, D, j, r):
    lo, hi, slo, shi, cost, part = r
    nm = f"cert_{tag}_{j}"
    # long nested list literals exceed the default `maxRecDepth` of the elaborator
    out = ["set_option maxRecDepth 100000 in",
           C.wrap_doc(f"The certificate of the {len(part)} values `{lo} ≤ λ < {hi}` with "
                      f"`{slo} ≤ σ < {shi}` (about {cost:.0f}s)."),
           f"def {nm} : List (ℕ × List GCert) := ["]
    out.append(",\n".join(lam_str(c, "  ") for c in part))
    out += ["  ]", "",
            f"theorem casesOn_{tag}_{j} :", cases_on(p, q, D, lo, hi, slo, shi),
            f"  casesOn_of_classCert (cert := {nm}) (by norm_num) ps_{tag}_prime",
            f"    keys_{tag}_ok (by decide +kernel)", ""]
    if len(out[-3]) > 100:
        out[-3:-1] = [f"  casesOn_of_classCert (cert := {nm}) (by norm_num)",
                      f"    ps_{tag}_prime keys_{tag}_ok (by decide +kernel)"]
    return out


def combine_lines(tag, p, q, D, rngs, S):
    """`casesOK_tag`, from the rectangles: the `σ` pieces of one `λ` range by `transσ`, then the
    `λ` ranges by `trans`, one theorem per step."""
    out, blocks, j = [], [], 0
    while j < len(rngs):
        k = j
        while k + 1 < len(rngs) and rngs[k + 1][:2] == rngs[j][:2]:
            k += 1
        lo, hi = rngs[j][:2]
        if k == j:
            blocks.append((f"casesOn_{tag}_{j + 1}", lo, hi))
        else:
            name = f"casesOn_{tag}_{j + 1}"
            for i in range(j + 1, k + 1):
                new = f"casesOnσ_{tag}_{i + 1}"
                out += [f"theorem {new} :", cases_on(p, q, D, lo, hi, 0, rngs[i][3]),
                        f"  {name}.transσ casesOn_{tag}_{i + 1}", ""]
                name = new
            blocks.append((name, lo, hi))
        j = k + 1
    name = blocks[0][0]
    for i, (b, lo, hi) in enumerate(blocks[1:], 2):
        new = f"casesUpTo_{tag}_{i}"
        out += [f"theorem {new} :", cases_on(p, q, D, 0, hi, 0, S),
                f"  {name}.trans {b}", ""]
        name = new
    if SQMODE:
        out += [f"theorem casesOK_{tag} : CasesOKT true {p} {q} {D} :=",
                f"  {name}.casesOKT (by norm_num) (by norm_num) (by norm_num)", ""]
    else:
        out += [f"theorem casesOK_{tag} : CasesOK {p} {q} {D} :=",
                f"  {name}.casesOK (by norm_num) (by norm_num) (by norm_num)", ""]
    return out


SQMODE = False


def emit(m, n, args, budget, parts):
    """The Lean files of the fiber: `{name: text}`."""
    U, V, W = m * m - n * n, 2 * m * n, m * m + n * n
    p, q = (min(U, V) ** 2, max(U, V) ** 2) if SQMODE else (2 * U * V, W * W)
    assert p < q and math.gcd(p, q) == 1
    D = q * q - p * p
    from sympy import factorint
    Ps = sorted(set(factorint(p * q * D)) | {2})
    assert all(primeB(l) for l in Ps)
    t0 = time.time()
    cert, keys, bad, stats = certify(p, q, D, Ps, Ts=tr_points(U, V, W) if SQMODE else None)
    print(f"({m},{n}) p={p} q={q}: {stats}, keys {len(keys)}, bad {len(bad)}, "
          f"{time.time() - t0:.0f}s", file=sys.stderr)
    if bad:
        print(f"  uncertified: {bad[:10]}", file=sys.stderr)
        return None
    tag = f"{C.name(m)}_{C.name(n)}"
    base = f"F_{p}_{q}" + ("_sq" if SQMODE else "")
    lo_, hi_ = sorted((U, V))
    ratio = f"{C.name(lo_)}_{C.name(hi_)}"
    S = (p * q) ** 2 * D + 1
    rngs = chunks(cert, p * q, S, budget)
    total = sum(r[4] for r in rngs)
    print(f"  {len(rngs)} declarations, about {total:.0f} kernel seconds", file=sys.stderr)
    doc = DOC.format(args=args, m=m, n=n, U=U, V=V, W=W, p=p, q=q, D=D, lo=lo_, hi=hi_,
                     ratio=ratio, groups=stats["groups"], killed=stats["killed"],
                     tuples=stats["tuples"], torsion=stats["torsion"], nkeys=len(keys),
                     nlam=len(cert), tag=tag)
    pre = [f"/-- The primes of `p q D` for the fiber `({m}, {n})`. -/",
           f"def ps_{tag} : List ℕ := {Ps}", "",
           f"theorem ps_{tag}_prime : ∀ l ∈ ps_{tag}, l.Prime :=",
           "  primes_of_all (by decide +kernel)", "",
           f"/-- The {len(keys)} class tests of the fiber `({m}, {n})`. -/",
           f"def keys_{tag} : KTree :=", wrap_tree(ktree(keys)), "",
           f"theorem keys_{tag}_ok : keys_{tag}.all (keyOK {p} {q}) = true := by",
           "  decide +kernel", ""]
    if len(pre[-3]) > 100:
        pre[-3:-2] = [f"theorem keys_{tag}_ok :", f"    keys_{tag}.all (keyOK {p} {q}) = true := by"]
    post = [C.wrap_doc(f"The descent for the pair `(2UV, W²) = ({p}, {q})` of the fiber "
                       f"`({m}, {n})`."),
            f"theorem not_isSol_{tag} (M e r s : ℤ) : ¬ IsSol {p} {q} M e r s :=",
            "  not_isSol_of_casesOK (by norm_num) (by norm_num) (by norm_num) (by decide)",
            f"    casesOK_{tag} M e r s", "", "end Descent", "",
            C.wrap_doc(f"**No perfect cuboid has two edges in ratio `{lo_} : {hi_}`.** This is "
                       f"the fiber `(m, n) = ({m}, {n})`, through the `2`-isogeny from `E″` to "
                       f"the pair curve of `({p}, {q})`."),
            f"theorem not_isPerfectCuboid_{ratio} {{X Y Z : ℕ}} (h : IsPerfectCuboid X Y Z) :",
            f"    {U} * X ≠ {V} * Z := by",
            "  intro hXZ",
            f"  refine Kubert.IsPerfectCuboid.not_onFiber_of_isogeny h (U := {U}) (V := {V}) (W := {W})",
            "    (by norm_num) (by norm_num) (by norm_num) (fun M e r s ↦ ?_)",
            "    (by exact_mod_cast hXZ)",
            f"  simpa using Descent.not_isSol_{tag} M e r s", "", "end PerfectCuboid", ""]
    if SQMODE:
        doc = SQ_DOC.format(args=args, m=m, n=n, U=U, V=V, W=W, p=p, q=q, D=D, lo=lo_, hi=hi_,
                            ratio=ratio, groups=stats["groups"], killed=stats["killed"],
                            tuples=stats["tuples"], torsion=stats["torsion"],
                            tr=stats.get("tr", 0), nkeys=len(keys), nlam=len(cert), tag=tag)
        sol = "hs" if U * U == p else "⟨hs.1, hs.2.1, hs.2.2.2, hs.2.2.1⟩"
        post = [C.wrap_doc(f"The descent for the pair `(U², V²)` of the fiber `({m}, {n})`: "
                           f"every solution of `IsSol {p} {q}` has `M² = pq e²`."),
                f"theorem sq_eq_{tag} {{M e r s : ℤ}} (h : IsSol {p} {q} M e r s) :",
                f"    M ^ 2 = {p} * {q} * e ^ 2 :=",
                "  sq_eq_of_isSol_of_casesOKT (by norm_num) (by norm_num) (by norm_num) (by decide)",
                f"    casesOK_{tag} h", "", "end Descent", "",
                C.wrap_doc(f"**No perfect cuboid has two edges in ratio `{lo_} : {hi_}`.** This is "
                           f"the fiber `(m, n) = ({m}, {n})`, through the pair curve "
                           f"`({p}, {q})` of `E″` itself."),
                f"theorem not_isPerfectCuboid_{ratio} {{X Y Z : ℕ}} (h : IsPerfectCuboid X Y Z) :",
                f"    {U} * X ≠ {V} * Z := by",
                "  intro hXZ",
                f"  refine Kubert.IsPerfectCuboid.not_onFiber_of_sq h (U := {U}) (V := {V}) "
                f"(W := {W})",
                "    (by norm_num) (by norm_num) (by norm_num) (fun M e r s hs ↦ ?_)",
                "    (by exact_mod_cast hXZ)",
                "  norm_num at hs",
                f"  linear_combination Descent.sq_eq_{tag} {sol}", "", "end PerfectCuboid", ""]
    body = []
    for j, r in enumerate(rngs, 1):
        body += chunk_lines(tag, p, q, D, j, r)
    comb = combine_lines(tag, p, q, D, rngs, S)
    imports = ["LeanPlayground.PerfectCuboid.DescentClass", "LeanPlayground.PerfectCuboid.Kubert"]
    if parts == 1:
        return {base: head(imports, doc) + "\n".join(pre + body + comb + post)}
    # split the rectangles into `parts` contiguous pieces of about equal cost
    files, bounds, acc, j0 = {}, [], 0.0, 0
    for j, r in enumerate(rngs):
        acc += r[4]
        if acc >= total * (len(bounds) + 1) / parts and len(bounds) < parts - 1:
            bounds.append(j + 1)
    bounds = [0] + bounds + [len(rngs)]
    pkg = "LeanPlayground.PerfectCuboid.Fibers"
    files[f"{base}_0"] = head(["LeanPlayground.PerfectCuboid.DescentClass"],
                              PART_DOC.format(p=p, q=q, what="the primes and the class tests",
                                              base=base)) + "\n".join(pre + ["end Descent", "",
                                                                             "end PerfectCuboid", ""])
    for i in range(parts):
        lines = []
        for j in range(bounds[i], bounds[i + 1]):
            lines += chunk_lines(tag, p, q, D, j + 1, rngs[j])
        files[f"{base}_{i + 1}"] = head([f"{pkg}.{base}_0"], PART_DOC.format(
            p=p, q=q, what=f"the certificates {bounds[i] + 1}–{bounds[i + 1]}", base=base)) + \
            "\n".join(lines + ["end Descent", "", "end PerfectCuboid", ""])
    files[base] = head([f"{pkg}.{base}_{i + 1}" for i in range(parts)] +
                       ["LeanPlayground.PerfectCuboid.Kubert"], doc) + "\n".join(comb + post)
    return files


def head(imports, doc):
    return ("module\n\n" + "".join(f"public import {i}\n" for i in imports) + "\n" + doc +
            "\n@[expose] public section\n\nnamespace PerfectCuboid\n\nnamespace Descent\n\n")


PART_DOC = """/-!
# The fiber `({p}, {q})`: {what}

Part of `LeanPlayground.PerfectCuboid.Fibers.{base}`,
split so that the kernel checks run in separate jobs. Generated by
`scripts/cuboid_class_cert.py` (do not edit by hand).
-/
"""


DOC = """/-!
# No perfect cuboid has two edges in ratio `{lo} : {hi}`

Generated by `scripts/cuboid_class_cert.py` (do not edit by hand):

```
{args}
```

This is the fiber `(m, n) = ({m}, {n})`, with `U = {U}`, `V = {V}`, `W = {W}`. The curve
`E″` of the fiber is `2`-isogenous to the pair curve of `(p, q) = (2UV, W²) = ({p}, {q})`
(`IsPerfectCuboid.not_onFiber_of_isogeny`), with `D = q² − p² = (U² − V²)² = {D}`. The
descent for this pair has {groups} groups `(λ, σ₀)` over {nlam} values of `λ`; {killed} of them
are ruled out by their `2`-descent class (`ClassKill`, with {nkeys} distinct class tests), and
the other {tuples} cases are split out, {torsion} of them torsion translates. The kernel
replays the certificate with `classCert` (`decide +kernel`).

The curve `E″` has rank `0` and its `2`-Selmer group is its torsion modulo `2` (PARI/GP); this is
only the reason to expect the descent to work, and the proofs do not depend on it.

## Main results

* `Descent.not_isSol_{tag}` — the descent for the pair `({p}, {q})`.
* `not_isPerfectCuboid_{ratio}` — no perfect cuboid has `{U} X = {V} Z`.
-/
"""


SQ_DOC = """/-!
# No perfect cuboid has two edges in ratio `{lo} : {hi}`

Generated by `scripts/cuboid_class_cert.py` (do not edit by hand):

```
{args}
```

This is the fiber `(m, n) = ({m}, {n})`, with `U = {U}`, `V = {V}`, `W = {W}`,
through the curve `E″` itself: moving a root to `0` makes it the pair curve of
`(p, q) = (U², V²) = ({p}, {q})` (sorted), with `D = q² − p² = {D}`,
and a cuboid on the fiber gives a solution with `M² ≠ pq e²`
(`IsPerfectCuboid.not_onFiber_of_sq`). Unlike the pair `(2UV, W²)`, this pair has the
solutions `M² = pq e²` of the point `T₄` of order `4`, so the descent shows only that every
solution is of this kind (`sq_eq_of_isSol_of_casesOKT`). It has {groups} groups
`(λ, σ₀)` over {nlam} values of `λ`; {killed} of them are ruled out by their `2`-descent
class (`ClassKill`, with {nkeys} distinct class tests), and the other {tuples} cases are
split out, {torsion} of them torsion translates and {tr} of them by family TR (the
half-points of `±T₄` minus a point of order `8`, `trOK`). The kernel replays the certificate
with `classCert` (`decide +kernel`).

The curve `E″` has rank `0` and its `2`-Selmer group is its torsion modulo `2` (PARI/GP); this is
only the reason to expect the descent to work, and the proofs do not depend on it.

## Main results

* `Descent.sq_eq_{tag}` — the descent for the pair `({p}, {q})`.
* `not_isPerfectCuboid_{ratio}` — no perfect cuboid has `{U} X = {V} Z`.
-/
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("fiber", help="the fiber m,n")
    ap.add_argument("--budget", type=float, default=15.0,
                    help="estimated kernel seconds per declaration (default 15)")
    ap.add_argument("--parts", type=int, default=1,
                    help="split the certificates over this many modules (default 1)")
    ap.add_argument("-d", "--dir", default="LeanPlayground/PerfectCuboid/Fibers",
                    help="output directory (default LeanPlayground/PerfectCuboid/Fibers)")
    ap.add_argument("--sq", action="store_true",
                    help="use the pair (U^2, V^2) of E'' itself, with family TR")
    a = ap.parse_args()
    global SQMODE
    SQMODE = a.sq
    m, n = map(int, a.fiber.split(","))
    args = "python3 scripts/cuboid_class_cert.py " + " ".join(sys.argv[1:])
    files = emit(m, n, args, a.budget, a.parts)
    if files is None:
        sys.exit(1)
    for name, text in files.items():
        with open(os.path.join(a.dir, name + ".lean"), "w") as f:
            f.write(text)


if __name__ == "__main__":
    main()
