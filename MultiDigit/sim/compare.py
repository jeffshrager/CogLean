"""Compare the blind simulator (mdsim.py) with the Lean model's predictions.

Runs the preregistered checks of PREREG.md on the simulator's logs:
random fixed-mode instances, random learning-mode instances, and the
instances in instances/ against Lean's exact distributions
(instances/lean_exact.json, from ../Export.lean). Writes RESULTS.md.

    python3 compare.py [--quick]

The reference computations here (codes, the exact single-digit DOA
distribution, R and G) follow the Lean definitions; the simulator is
independent of them.
"""

import json
import math
import os
import random
import re
import sys
from collections import Counter, defaultdict
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import mdsim  # noqa: E402

PLACES = ["hundreds", "tens", "units"]


# ---------------------------------------------------------------- reference

def prob_of(s):
    a, b = s.split("+")
    return int(a), int(b)


def digit(p, i, j):
    n = p[i]
    return [n // 100 % 10, n // 10 % 10, n % 10][j]


def code(p, enc):
    if enc == "bcd":
        return [digit(p, f // 12, f % 12 // 4) >> (f % 4) & 1 for f in range(24)]
    c = [0] * 360
    for i in range(2):
        for j in range(3):
            d = digit(p, i, j)
            b = (i * 3 + j) * 10
            c[b] = int(d == 0)
            for k in range(9):
                c[b + 1 + k] = int(d > k)
    for j in range(3):
        d, e = digit(p, 0, j), digit(p, 1, j)
        c[60 + j * 100 + min(d, e) * 10 + max(d, e)] = 1
    return c


def digit_features(enc, i, j):
    """The features M1 says determine digit j of addend i."""
    if enc == "bcd":
        return [i * 12 + j * 4 + k for k in range(4)]
    return [(i * 3 + j) * 10 + 1 + k for k in range(9)]


def zero_flag(i, j):
    return (i * 3 + j) * 10


def threshold(i, j, k):
    return (i * 3 + j) * 10 + 1 + k


def fact_features(j):
    return [60 + j * 100 + m for m in range(100)]


def search_dist(answers, s, c, n):
    """Exact retrieval: {('stated', a): p, ('exhausted',): p}."""
    T = sum(s.get(a, F(0)) for a in answers)
    out = {}
    if T == 0:
        return {("exhausted",): F(1)}
    R = sum(s.get(a, F(0)) for a in answers if s.get(a, F(0)) > c) / T
    G = sum((1 - R) ** k for k in range(n))
    for a in answers:
        if s.get(a, F(0)) > c:
            out[("stated", a)] = out.get(("stated", a), F(0)) + s[a] / T * G
    out[("exhausted",)] = (1 - R) ** n
    return out


def count_dist(k, qs, qd):
    d = {0: F(1)}
    for _ in range(k):
        nd = defaultdict(F)
        for r, p in d.items():
            nd[r] += p * qs
            nd[r + 1] += p * (1 - qs - qd)
            nd[r + 2] += p * qd
        d = dict(nd)
    return d


def single_assoc(params, d, e):
    sp = params["single"]
    answers = sp["answers"]
    s = {a: (F(sp["default"]["correct"]) if a == d + e else F(sp["default"]["other"]))
         for a in answers}
    for a, v in sp.get("overrides", {}).get(f"{d}+{e}", {}).items():
        s[int(a)] = F(v)
    return answers, s


def single_dist(params, d, e):
    """Exact single-digit DOA trial: {answer: p} (Lean's SC.trial)."""
    answers, s = single_assoc(params, d, e)
    c1, n1 = F(params["c1"]), params["n1"]
    el, qs, qd = F(params["elab"]), F(params["qs"]), F(params["qd"])
    out = defaultdict(F)
    sd = search_dist(answers, s, c1, n1)
    for k, p in sd.items():
        if k[0] == "stated":
            out[k[1]] += p
    pex = sd[("exhausted",)]
    s2 = {a: (s.get(a, F(0)) + (el if a == d + e else 0)) / (1 + el) for a in answers}
    T2 = sum(s2.values())
    pfail = F(0)
    for a in answers:
        pa = s2[a] / T2
        if s2[a] > c1:
            out[a] += pex * pa
        else:
            pfail += pa
    for r, p in count_dist(d + e, qs, qd).items():
        out[r] += pex * pfail * p
    return dict(out)


def whole_assoc(params, y):
    t = params["whole"].get(y, {})
    return {a: F(t.get(str(a), 0)) for a in params["answers"]}


def R_G(params, y):
    s = whole_assoc(params, y)
    c, n = F(params["c"]), params["n"]
    T = sum(s.values())
    R = sum(v for v in s.values() if v > c) / T
    return s, T, R, sum((1 - R) ** k for k in range(n))


# ---------------------------------------------------------------- checks

class Check:
    def __init__(self, cid, lean, kind):
        self.cid, self.lean, self.kind = cid, lean, kind
        self.applied = 0
        self.failures = []

    def test(self, ok, detail):
        self.applied += 1
        if not ok:
            self.failures.append(detail)

    def status(self):
        if self.applied == 0:
            return "VACUOUS"
        return "PASS" if not self.failures else "FAIL"


CHECKS = {}


def chk(cid, lean, kind):
    if cid not in CHECKS:
        CHECKS[cid] = Check(cid, lean, kind)
    return CHECKS[cid]


def binom_tail(k, n, p):
    """Two-sided normal-approximation tail, for reporting only."""
    if p in (0, 1):
        return 0.0
    z = abs(k - n * p) / math.sqrt(n * p * (1 - p))
    return math.erfc(z / math.sqrt(2))


def prob_test(c, k, n, p, what):
    """PREREG's rule: exact for p in {0,1}, else |k/n - p| <= 4 sigma."""
    p = F(p)
    if p == 0:
        ok = k == 0
    elif p == 1:
        ok = k == n
    else:
        ok = abs(k / n - float(p)) <= 4 * math.sqrt(float(p) * (1 - float(p)) / n)
    c.test(ok, f"{what}: {k}/{n} = {k / n:.5f} vs p = {float(p):.6g} "
               f"(normal tail {binom_tail(k, n, float(p)):.2g})")


def two_sample(c, k1, n1, k2, n2, what):
    p = (k1 + k2) / (n1 + n2)
    if p in (0, 1):
        ok = (k1 / n1) == (k2 / n2)
    else:
        ok = abs(k1 / n1 - k2 / n2) <= 4 * math.sqrt(p * (1 - p) * (1 / n1 + 1 / n2))
    c.test(ok, f"{what}: {k1}/{n1} vs {k2}/{n2}")


def run(params):
    return list(mdsim.simulate(params))


def fixed_checks(params, recs, tag):
    enc = params["encoding"]
    c = F(params["c"])
    n = params["n"]
    by = defaultdict(list)
    for r in recs:
        by[r["problem"]].append(r)
    familiar = set(params["familiar"])
    whole_wrong = {}
    cols_freq = {}
    whole_dist = {}
    for xs, rs in by.items():
        x = prob_of(xs)
        N = len(rs)
        ys = {r["recognized_as"] for r in rs}
        chk("fixed-net", "(fixed mode)", "exact").test(
            len(ys) == 1 and len({tuple(r["path"]) for r in rs}) == 1,
            f"{tag} {xs}: recognized_as/path vary {ys}")
        y_s = rs[0]["recognized_as"]
        path = set(rs[0]["path"])
        ncols = sum(r["route"] == "columns" for r in rs)
        cols_freq[xs] = (ncols, N)
        whole_answers = Counter(r["answer"] for r in rs if r["route"] == "whole")
        nwhole = N - ncols
        nww = sum(v for a, v in whole_answers.items() if a != sum(x))
        whole_wrong[xs] = (nww, N)
        whole_dist[xs] = (whole_answers, N)
        if y_s is None:
            prob_test(chk("P1", "MD.columns_prob", "prob"), ncols, N, 1, f"{tag} {xs} unrecognized")
        else:
            y = prob_of(y_s)
            s, T, R, G = R_G(params, y_s)
            prob_test(chk("P1", "MD.columns_prob", "prob"), ncols, N, (1 - R) ** n,
                      f"{tag} {xs} as {y_s}")
            for a in params["answers"]:
                pa = (s[a] / T * G) if s[a] > c else F(0)
                prob_test(chk("P2", "MD.whole_depends_only_on_route", "prob"),
                          whole_answers.get(a, 0), N, pa, f"{tag} {xs} as {y_s}, answer {a}")
            # answers outside the list
            extra = sum(v for a, v in whole_answers.items() if a not in params["answers"])
            chk("P2", "MD.whole_depends_only_on_route", "prob").test(
                extra == 0, f"{tag} {xs}: {extra} whole answers outside the answer list")
            sharp = all(a == sum(y) for a in params["answers"] if s[a] > c)
            if sharp:
                chk("P3", "MD.confusion_gives_neighbours_answer", "exact").test(
                    all(a == sum(y) for a in whole_answers), f"{tag} {xs} as {y_s}: {dict(whole_answers)}")
                if sum(x) != sum(y):
                    chk("P4", "MD.confident_errors", "exact+prob").test(
                        nww == nwhole, f"{tag} {xs}: wrong {nww} vs whole {nwhole}")
            cx, cy = code(x, enc), code(y, enc)
            if x != y:
                chk("L-A", "Net.confusion_agrees_on_path", "exact").test(
                    all(cx[f] == cy[f] for f in path), f"{tag} {xs} as {y_s}: path {sorted(path)}")
                hund = all(set(digit_features(enc, i, 0)) <= path for i in range(2))
                tens = all(set(digit_features(enc, i, 1)) <= path for i in range(2))
                if hund:
                    chk("P6a", "MD.near_miss_200", "exact").test(
                        abs(sum(y) - sum(x)) < 200, f"{tag} {xs} as {y_s}")
                    if tens:
                        chk("P6b", "MD.near_miss_20", "exact").test(
                            abs(sum(y) - sum(x)) < 20, f"{tag} {xs} as {y_s}")
                if enc == "rich":
                    for i in range(2):
                        for j in range(3):
                            if zero_flag(i, j) in path:
                                chk("P13", "MD.confusion_keeps_zeros", "exact").test(
                                    (digit(x, i, j) == 0) == (digit(y, i, j) == 0),
                                    f"{tag} {xs} as {y_s}, digit {i},{j}")
                            ks = [k for k in range(9) if threshold(i, j, k) in path]
                            for lo in ks:
                                for hi in ks:
                                    if lo < hi and lo < digit(y, i, j) <= hi:
                                        chk("P15", "MD.confusion_within_gap", "exact").test(
                                            lo < digit(x, i, j) <= hi,
                                            f"{tag} {xs} as {y_s}, digit {i},{j}, ({lo},{hi}]")
                    yround = all(digit(y, i, j) == 0 for i in range(2) for j in (1, 2))
                    zeros_on = all(zero_flag(i, j) in path for i in range(2) for j in (1, 2))
                    if yround and zeros_on and hund:
                        chk("P14", "MD.round_confusion_exact", "exact").test(
                            x == y, f"{tag} {xs} as {y_s}")
                    if all(set(fact_features(j)) <= path for j in range(3)):
                        chk("P17", "MD.facts_same_sum", "exact").test(sum(x) == sum(y), f"{tag} {xs}")
                    if all(set(fact_features(j)) <= path for j in (1, 2)):
                        chk("P18", "MD.facts_mod_100", "exact").test(
                            sum(x) % 100 == sum(y) % 100, f"{tag} {xs}")
                    if set(fact_features(2)) <= path:
                        chk("P18", "MD.facts_mod_10", "exact").test(
                            sum(x) % 10 == sum(y) % 10, f"{tag} {xs}")
        # column checks
        for r in rs:
            if r["route"] != "columns":
                continue
            cs = {cc["place"]: cc for cc in r["columns"]}
            r0, r1, r2 = cs["units"]["answer"], cs["tens"]["answer"], cs["hundreds"]["answer"]
            chk("P9", "MD.columns_place_value", "exact").test(
                r["answer"] == r0 + 10 * r1 + 100 * r2, f"{tag} {xs}: {r['columns']} -> {r['answer']}")
            errs = [(j, cs[pl]["answer"] - sum(cs[pl]["digits"]))
                    for j, pl in enumerate(["units", "tens", "hundreds"])
                    if cs[pl]["answer"] != sum(cs[pl]["digits"])]
            if len(errs) == 1:
                j, delta = errs[0]
                chk("P10a", "MD.one_column_errs", "exact").test(
                    r["answer"] != sum(x) and r["answer"] - sum(x) == delta * 10 ** j,
                    f"{tag} {xs}: {r['columns']} -> {r['answer']}")
    # P4 second part and P5: two-sample against the stored problem
    for xs in by:
        y_s = by[xs][0]["recognized_as"]
        if y_s is None or y_s == xs or y_s not in by:
            continue
        x, y = prob_of(xs), prob_of(y_s)
        s, T, R, G = R_G(params, y_s)
        sharp = all(a == sum(y) for a in params["answers"] if s[a] > c)
        if sharp and sum(x) != sum(y):
            two_sample(chk("P4", "MD.confident_errors", "exact+prob"), *cols_freq[xs], *cols_freq[y_s],
                       f"{tag} columns {xs} vs {y_s}")
        if sum(x) == sum(y):
            two_sample(chk("P5", "MD.same_sum_confusion_harmless", "prob"), *whole_wrong[xs],
                       *whole_wrong[y_s], f"{tag} whole-wrong {xs} vs {y_s}")
    # P2': problems routed to the same stored problem
    groups = defaultdict(list)
    for xs in by:
        if by[xs][0]["recognized_as"] is not None:
            groups[by[xs][0]["recognized_as"]].append(xs)
    for y_s, xs_list in groups.items():
        for a, b in zip(xs_list, xs_list[1:]):
            (wa, na), (wb, nb) = whole_dist[a], whole_dist[b]
            for ans in params["answers"]:
                two_sample(chk("P2'", "MD.same_route_same_retrieval", "prob"),
                           wa.get(ans, 0), na, wb.get(ans, 0), nb, f"{tag} {a} vs {b}, answer {ans}")
    # P10b: column additions against exact single-digit DOA
    adds = defaultdict(lambda: [0, 0])
    for r in recs:
        for cc in r["columns"]:
            d, e = cc["digits"]
            adds[(d, e)][1] += 1
            adds[(d, e)][0] += cc["answer"] != d + e
    for (d, e), (k, N) in adds.items():
        pw = sum(p for a, p in single_dist(params, d, e).items() if a != d + e)
        prob_test(chk("P10b", "MD.doaFact_wrong", "prob"), k, N, pw, f"{tag} {d}+{e}")


def learning_checks(params, recs, tag, explore):
    seen_self = set()
    learned = {}
    pending12 = set()
    o2 = params["open_choices"]["O2"]
    o2_zero_ok = o2 == "zero" or (o2 == "correct" and F(params.get("o2_strength", "1/2")) <= F(params["c"]))
    phases = defaultdict(list)
    first_whole_wrong = {}
    for r in recs:
        xs, y = r["problem"], r["recognized_as"]
        if xs in seen_self:
            chk("P7", "MD.learning_preserves_trial", "exact").test(
                y == xs, f"{tag} trial {r['trial']}: {xs} recognized as {y} after being itself")
        if xs in learned:
            chk("P11", "MD.discrimination_removes_confusion", "exact").test(
                y == xs, f"{tag} trial {r['trial']}: {xs} as {y} after discrimination")
        for x2, y2 in learned.items():
            if xs == y2 and y2 != x2:
                chk("P11", "MD.discrimination_removes_confusion", "exact").test(
                    y == xs or y is None and False, f"{tag} trial {r['trial']}: {y2} disturbed ({y})")
        if xs in pending12:
            pending12.discard(xs)
            if o2_zero_ok:
                chk("P12", "MD.discrimination_then_columns", "exact").test(
                    r["route"] == "columns", f"{tag} trial {r['trial']}: {xs} went {r['route']}")
        if y == xs:
            seen_self.add(xs)
        if r["net_learned"]:
            learned[xs] = y
            pending12.add(xs)
        ph = "C" if r["route"] == "columns" else ("W" if r["correct"] else "E")
        phases[xs].append(ph)
    for xs in learned:
        explore.append((tag, o2, xs, "".join(phases[xs])))


def classify(seq):
    """From the first discrimination-triggering error on."""
    i = seq.index("E")
    tail = seq[i:]
    last = tail[-20:]
    if re.fullmatch(r"E+C+W+", tail):
        return "canonical E+ C+ W+"
    if set(last) == {"W"}:
        return "settles on W (not canonical)"
    if set(last) == {"E"}:
        return "trapped on E"
    return "mixed at end"


# ---------------------------------------------------------------- instances

def rand_problem(rng):
    return (rng.randrange(1000), rng.randrange(1000))


def neighbour(rng, p):
    i, j = rng.randrange(2), rng.randrange(3)
    n = p[i]
    ds = [n // 100 % 10, n // 10 % 10, n % 10]
    ds[j] = (ds[j] + rng.choice([1, -1, 2, 3])) % 10
    m = ds[0] * 100 + ds[1] * 10 + ds[2]
    return (m, p[1]) if i == 0 else (p[0], m)


def familiar_set(rng):
    kind = rng.choice(["random", "shared_hundreds", "round", "neighbours", "mixed"])
    k = rng.randint(2, 8)
    out = set()
    while len(out) < k:
        if kind == "random" or (kind == "mixed" and rng.random() < 0.3):
            p = rand_problem(rng)
        elif kind == "shared_hundreds" or kind == "mixed":
            h1, h2 = 100 * rng.randrange(1, 9), 100 * rng.randrange(1, 9)
            p = (h1 + rng.randrange(100), h2 + rng.randrange(100))
        elif kind == "round":
            p = (100 * rng.randrange(1, 9), 100 * rng.randrange(1, 9))
        else:
            d = rng.randrange(1, 9)
            p = (100 * (d + len(out) % 2), 100 * rng.randrange(1, 3))
        out.add(p)
    return [f"{a}+{b}" for a, b in out], kind


def make_instance(rng, learning=False):
    enc = rng.choice(["bcd", "rich"])
    nf = 24 if enc == "bcd" else 360
    if rng.random() < 0.5:
        order = "bcd_hundreds_first" if enc == "bcd" else "rich_default"
    else:
        order = list(range(nf))
        rng.shuffle(order)
    fam, kind = familiar_set(rng)
    fp = [prob_of(s) for s in fam]
    sched = list(fam)
    for p in fp:
        for _ in range(rng.randint(1, 2)):
            sched.append("%d+%d" % neighbour(rng, p))
        if rng.random() < 0.4:
            sched.append(f"{p[1]}+{p[0]}")
    for _ in range(2):
        sched.append("%d+%d" % rand_problem(rng))
    sched = list(dict.fromkeys(sched))[:14]
    sums = sorted({sum(prob_of(s)) for s in sched})
    answers = sorted(set(sums) | {s + d for s in sums[:4] for d in (10, -10, 100)} - {-10, -100})
    answers = [a for a in answers if a >= 0]
    c = rng.choice([F(1, 10), F(1, 4), F(1, 2)])
    whole = {}
    for s in fam:
        y = sum(prob_of(s))
        t = {}
        sharp = rng.random() < 0.5
        for a in answers:
            if a == y:
                v = c + rng.choice([F(1, 20), F(1, 5), F(2, 5)])
            elif sharp:
                v = rng.choice([F(0), F(1, 100), c / 2, c])
            else:
                v = rng.choice([F(0), F(1, 100), F(1, 20), c, c + F(1, 10)])
            if v:
                t[str(a)] = str(v)
        whole[s] = t
    overrides = {}
    for _ in range(rng.randint(0, 6)):
        d, e = rng.randrange(10), rng.randrange(10)
        w = (d + e + rng.choice([1, -1])) % 19
        overrides[f"{d}+{e}"] = {str(w): rng.choice(["3/10", "2/5", "1/2"])}
    p = {
        "encoding": enc, "order": order, "familiar": fam, "answers": answers,
        "whole": whole, "c": str(c), "n": rng.randint(1, 3),
        "single": {"answers": list(range(19)),
                   "default": {"correct": rng.choice(["1/2", "3/5", "7/10"]),
                               "other": rng.choice(["1/50", "1/20"])},
                   "overrides": overrides},
        "c1": rng.choice(["1/4", "2/5"]), "n1": rng.randint(1, 2),
        "elab": "1/20", "qs": rng.choice(["0", "1/20", "1/10"]),
        "qd": rng.choice(["0", "1/20", "1/10"]),
        "learning": learning, "inc": "1/20", "inc1": "1/20",
        "open_choices": {"O1": "true", "O2": rng.choice(["zero", "correct", "copy"]) if learning else "zero",
                         "O3": "stored"},
        "schedule": sched, "repeats": 300 if learning else 1500,
        "seed": rng.randrange(10 ** 9),
    }
    return p, kind


def sharp_table(q, answers):
    y = sum(prob_of(q))
    return {str(a): ("9/10" if a == y else "1/100") for a in answers}


def lean_instances():
    base = {
        "single": {"answers": list(range(19)), "default": {"correct": "3/5", "other": "1/50"},
                   "overrides": {}},
        "c1": "2/5", "n1": 1, "elab": "1/20", "qs": "1/10", "qd": "1/10",
        "learning": False, "inc": "0", "inc1": "0",
        "open_choices": {"O1": "true", "O2": "zero", "O3": "none"},
        "repeats": 20000, "seed": 7,
    }
    a1 = [200, 250, 300]
    i1 = dict(base, encoding="bcd", order="bcd_hundreds_first", familiar=["100+100", "100+200"],
              answers=a1, whole={"100+100": sharp_table("100+100", a1), "100+200": sharp_table("100+200", a1)},
              c="1/2", n=1, schedule=["150+100", "100+100", "100+200", "120+130"])
    i1["single"] = dict(base["single"], overrides={"1+1": {"2": "3/10", "3": "3/10"}})
    a2 = [200, 220, 250]
    i2 = dict(base, encoding="rich", order="rich_default", familiar=["100+100", "120+100"], answers=a2,
              whole={"100+100": sharp_table("100+100", a2), "120+100": sharp_table("120+100", a2)},
              c="1/2", n=2, n1=2, schedule=["150+100", "100+100", "120+100"])
    a3 = [700, 800, 900]
    w3 = {"700+100": {"800": "7/10", "900": "1/10", "700": "1/10"},
          "800+100": {"900": "7/10", "800": "1/10", "700": "1/10"}}
    i3 = dict(base, encoding="rich", order="rich_default", familiar=["700+100", "800+100"], answers=a3,
              whole=w3, c="3/10", n=1, schedule=["600+100"])
    i4 = dict(i3, encoding="bcd", order="bcd_hundreds_first")
    return {"i1_bcd_example": i1, "i2_rich_zeros": i2, "i3_rich_magnitude": i3, "i4_bcd_magnitude": i4}


def lean_exact_checks(name, params, recs, exact):
    by = defaultdict(list)
    for r in recs:
        by[r["problem"]].append(r)
    for xs, rs in by.items():
        ex = exact[name][xs]
        chk("Lean-exact", "#eval MD.trial", "prob").test(
            all(r["recognized_as"] == ex["recognized_as"] for r in rs),
            f"{name} {xs}: recognized_as {rs[0]['recognized_as']} vs Lean {ex['recognized_as']}")
        N = len(rs)
        cnt = Counter((r["route"], r["answer"]) for r in rs)
        lean = {(o["route"], o["answer"]): F(o["p"]) for o in ex["outcomes"]}
        for key in set(cnt) | set(lean):
            prob_test(chk("Lean-exact", "#eval MD.trial", "prob"), cnt.get(key, 0), N,
                      lean.get(key, F(0)), f"{name} {xs} {key}")


# ---------------------------------------------------------------- main

def main():
    quick = "--quick" in sys.argv
    rng = random.Random(20261026)
    nfixed, nlearn = (6, 4) if quick else (30, 20)
    os.makedirs(os.path.join(HERE, "instances"), exist_ok=True)
    exact = json.load(open(os.path.join(HERE, "instances", "lean_exact.json")))
    for name, p in lean_instances().items():
        json.dump(p, open(os.path.join(HERE, "instances", name + ".json"), "w"), indent=1)
        if quick:
            p = dict(p, repeats=3000)
        recs = run(p)
        lean_exact_checks(name, p, recs, exact)
        fixed_checks(p, recs, name)
    kinds = Counter()
    for k in range(nfixed):
        p, kind = make_instance(rng)
        kinds[(p["encoding"], kind)] += 1
        fixed_checks(p, run(p), f"fixed{k}")
    explore = []
    o2s = Counter()
    for k in range(nlearn):
        p, _ = make_instance(rng, learning=True)
        o2s[p["open_choices"]["O2"]] += 1
        learning_checks(p, run(p), f"learn{k}({p['open_choices']['O2']})", explore)
    write_results(nfixed, nlearn, kinds, o2s, explore)


ORDER = ["Lean-exact", "fixed-net", "L-A", "P1", "P2", "P2'", "P3", "P4", "P5", "P6a", "P6b", "P9",
         "P10a", "P10b", "P13", "P14", "P15", "P17", "P18", "P7", "P11", "P12"]


def write_results(nfixed, nlearn, kinds, o2s, explore):
    lines = ["# Results: the blind simulator against the Lean model", "",
             "Generated by `compare.py`. Checks and tolerances are those of `PREREG.md`.", "",
             f"- Lean exact instances: 4 (`instances/`), 20000 repeats per schedule.",
             f"- Random fixed-mode instances: {nfixed} "
             f"({', '.join(f'{e}/{k}: {v}' for (e, k), v in sorted(kinds.items()))}), 1500 repeats.",
             f"- Random learning-mode instances: {nlearn} (O2: "
             f"{', '.join(f'{k} {v}' for k, v in sorted(o2s.items()))}), 300 repeats.", "",
             "| Check | Lean | Kind | Tests | Failures | Status |", "|---|---|---|---|---|---|"]
    for cid in ORDER + [c for c in CHECKS if c not in ORDER]:
        c = CHECKS.get(cid)
        if c is None:
            lines.append(f"| {cid} | | | 0 | 0 | VACUOUS |")
            continue
        lines.append(f"| {c.cid} | `{c.lean}` | {c.kind} | {c.applied} | {len(c.failures)} | {c.status()} |")
    lines += ["", "## Failures", ""]
    anyf = False
    for cid in ORDER:
        c = CHECKS.get(cid)
        if c and c.failures:
            anyf = True
            lines.append(f"### {cid} ({len(c.failures)})")
            lines += [f"- {f}" for f in c.failures[:10]]
            lines.append("")
    if not anyf:
        lines.append("None.")
    lines += ["", "## Exploratory: learning sequences", "",
              "Each problem that was discriminated (a wrong whole-route answer that changed the net), "
              "from its first trial, as E (whole, wrong), C (columns), W (whole, correct). "
              "Classified from its first E on; the end is its last 20 trials.", ""]
    table = defaultdict(Counter)
    lens = defaultdict(list)
    for tag, o2, xs, seq in explore:
        k = classify(seq)
        table[o2][k] += 1
        if k.startswith("canonical"):
            m = re.fullmatch(r"(C*)(E+)(C+)(W+)", seq)
            lens[o2].append((len(m.group(2)), len(m.group(3))))
    cats = ["canonical E+ C+ W+", "settles on W (not canonical)", "mixed at end", "trapped on E"]
    lines += ["| O2 | discriminated | " + " | ".join(cats) + " | mean E-run, C-run (canonical) |",
              "|---" * (len(cats) + 3) + "|"]
    for o2 in sorted(table):
        tot = sum(table[o2].values())
        ml = (f"{sum(a for a, _ in lens[o2]) / len(lens[o2]):.1f}, {sum(b for _, b in lens[o2]) / len(lens[o2]):.1f}"
              if lens[o2] else "")
        lines.append(f"| {o2} | {tot} | " + " | ".join(str(table[o2][c]) for c in cats) + f" | {ml} |")
    lines += ["", "Examples (run lengths):", ""]
    shown = Counter()
    for tag, o2, xs, seq in explore:
        k = classify(seq)
        if shown[(o2, k)] < 1:
            shown[(o2, k)] += 1
            runs = re.findall(r"(E+|C+|W+)", seq)
            lines.append(f"- {o2}, {k}: {tag} {xs}: " + " ".join(f"{r[0]}{len(r)}" for r in runs[:30])
                         + (" ..." if len(runs) > 30 else ""))
    open(os.path.join(HERE, "RESULTS.md"), "w").write("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
