#!/usr/bin/env python3
"""Stochastic simulation of 3-digit addition (EPAM net + strategy choice).

Blind implementation from the written specification.  Standard library only.
All strengths and probabilities are fractions.Fraction; floats are used only
to compare against random draws.

Usage:
    python3 mdsim.py PARAMS.json --out LOG.jsonl
Library:
    simulate(params) -> iterator of trial records (dicts)
"""

import argparse
import json
import os
import random
import sys
from fractions import Fraction

PLACES = ("hundreds", "tens", "units")  # place index 0, 1, 2

# --------------------------------------------------------------------------
# Defaults for the open choices (see IMPLEMENTATION_NOTES.md)
# --------------------------------------------------------------------------
DEFAULT_OPEN_CHOICES = {
    # O1: "true"   -> correct means answer == a+b of the presented problem x
    #     "stored" -> correct means answer == sum of recognized problem y
    "O1": "true",
    # O2: initial whole associations of a newly discriminated problem x
    #     "copy"  -> a copy of y's associations (after this trial's step 2)
    #     "table" -> x's entry in params["whole"] (missing answers 0) over
    #                params["answers"]
    #     "zero"  -> params["answers"], all strengths 0
    #     "correct" -> params["answers"] (plus x's true sum), all 0 except
    #                  x's true sum which gets params["o2_strength"]
    "O2": "zero",
    # O3: effect of a columns-route answer on x's whole associations
    #     "none"   -> no effect
    #     "stored" -> if x is stored in the net (has associations), its
    #                 whole associations get +inc for the columns answer
    #                 (+2*inc if correct w.r.t. x's true sum)
    "O3": "stored",
    # O4 sub-choices
    # single_commutative: if true, d+e and e+d share one association table
    "single_commutative": False,
}


# --------------------------------------------------------------------------
# Utilities
# --------------------------------------------------------------------------
def frac(v):
    """Parse a fraction given as string ("9/10", "0.5") or number."""
    if isinstance(v, Fraction):
        return v
    if isinstance(v, bool):
        raise ValueError("boolean is not a fraction")
    if isinstance(v, int):
        return Fraction(v)
    if isinstance(v, float):
        return Fraction(repr(v))
    return Fraction(str(v).strip())


def parse_problem(s):
    a, b = s.replace(" ", "").split("+")
    a, b = int(a), int(b)
    if not (0 <= a <= 999 and 0 <= b <= 999):
        raise ValueError("addend out of range: %r" % s)
    return a, b


def digits3(n):
    """(hundreds, tens, units)."""
    return (n // 100) % 10, (n // 10) % 10, n % 10


# --------------------------------------------------------------------------
# Codes (section 2)
# --------------------------------------------------------------------------
def encode(problem, encoding):
    """Return the code of a problem string as a tuple of 0/1 bits."""
    a, b = parse_problem(problem)
    dig = (digits3(a), digits3(b))  # dig[addend][place]
    if encoding == "bcd":
        code = [0] * 24
        for addend in (0, 1):
            for place in (0, 1, 2):
                d = dig[addend][place]
                for k in range(4):
                    code[addend * 12 + place * 4 + k] = (d >> k) & 1
        return tuple(code)
    if encoding == "rich":
        code = [0] * 360
        for addend in (0, 1):
            for place in (0, 1, 2):
                d = dig[addend][place]
                base = (addend * 3 + place) * 10
                code[base] = 1 if d == 0 else 0
                for k in range(9):
                    code[base + 1 + k] = 1 if d > k else 0
        for place in (0, 1, 2):
            x, y = dig[0][place], dig[1][place]
            lo, hi = min(x, y), max(x, y)
            code[60 + place * 100 + lo * 10 + hi] = 1
        return tuple(code)
    raise ValueError("unknown encoding %r" % encoding)


def feature(code, f):
    """Value of feature f; features beyond the end read as 0."""
    return code[f] if 0 <= f < len(code) else 0


def noticing_order(spec):
    if isinstance(spec, list):
        return [int(f) for f in spec]
    if spec == "bcd_hundreds_first":
        out = []
        for place in (0, 1, 2):
            for addend in (0, 1):
                for k in range(4):
                    out.append(addend * 12 + place * 4 + k)
        return out
    if spec == "rich_default":
        out = []
        for place in (0, 1, 2):
            for addend in (0, 1):
                out.append((addend * 3 + place) * 10)
        for place in (0, 1, 2):
            for addend in (0, 1):
                for k in range(9):
                    out.append((addend * 3 + place) * 10 + 1 + k)
        for place in (0, 1, 2):
            for off in range(100):
                out.append(60 + place * 100 + off)
        return out
    raise ValueError("unknown noticing order %r" % (spec,))


# --------------------------------------------------------------------------
# Discrimination net (section 3)
# --------------------------------------------------------------------------
class Net:
    """Binary discrimination net.

    Nodes are dicts.  Terminal: {"image": code|None, "problem": str|None}.
    Test: {"test": f, 0: node, 1: node}.
    """

    def __init__(self, order):
        self.order = list(order)
        self.root = {"image": None, "problem": None}

    def sort(self, code):
        node, path = self.root, []
        while "test" in node:
            f = node["test"]
            path.append(f)
            node = node[feature(code, f)]
        return node, path

    def recognize(self, code):
        """Return (problem name or None, path)."""
        node, path = self.sort(code)
        return node["problem"], path

    def learn(self, code, problem):
        """Learn code (of problem) into the net. Return True if net changed."""
        node, _ = self.sort(code)
        if node["image"] is None:
            node["image"], node["problem"] = code, problem
            return True
        z = node["image"]
        if z == code:
            return False
        for f in self.order:
            vx, vz = feature(code, f), feature(z, f)
            if vx != vz:
                zprob = node["problem"]
                node.clear()
                node["test"] = f
                node[vx] = {"image": code, "problem": problem}
                node[vz] = {"image": z, "problem": zprob}
                return True
        return False

    def stored_problems(self):
        out, stack = [], [self.root]
        while stack:
            n = stack.pop()
            if "test" in n:
                stack.append(n[0])
                stack.append(n[1])
            elif n["problem"] is not None:
                out.append(n["problem"])
        return out


# --------------------------------------------------------------------------
# Retrieval (section 4)
# --------------------------------------------------------------------------
def draw(assoc, rng):
    """One search: draw an answer with probability strength/T.

    assoc is a dict answer -> Fraction, iterated in insertion order.
    Returns None if T == 0.
    """
    total = sum(assoc.values(), Fraction(0))
    if total <= 0:
        return None
    u = rng.random()
    cum = Fraction(0)
    last = None
    for ans, s in assoc.items():
        if s <= 0:
            continue
        cum += s
        last = ans
        if u < float(cum / total):
            return ans
    return last  # guards against float rounding at the top end


def retrieve(assoc, c, n, rng):
    """Return (stated answer or None, number of searches made)."""
    if sum(assoc.values(), Fraction(0)) <= 0:
        return None, 0  # O4: T == 0 -> exhausted with no searches
    for i in range(1, n + 1):
        a = draw(assoc, rng)
        if assoc[a] > c:
            return a, i
    return None, n


# --------------------------------------------------------------------------
# Single-digit addition (section 5)
# --------------------------------------------------------------------------
def fingers_strengths(assoc, correct, elab):
    """Temporary strengths used by the fingers strategy."""
    new = dict(assoc)
    new[correct] = new.get(correct, Fraction(0)) + elab
    return {k: v / (1 + elab) for k, v in new.items()}


def count_fingers(n_objects, qs, qd, rng):
    total = 0
    fqs, fqsd = float(qs), float(qs + qd)
    for _ in range(n_objects):
        u = rng.random()
        if u < fqs:
            pass                 # skipped
        elif u < fqsd:
            total += 2           # counted twice
        else:
            total += 1
    return total


def add_digits(d, e, assoc, c1, n1, elab, qs, qd, rng):
    """Return (answer, strategy)."""
    ans, _ = retrieve(assoc, c1, n1, rng)
    if ans is not None:
        return ans, "retrieval"
    temp = fingers_strengths(assoc, d + e, elab)
    a = draw(temp, rng)
    if a is not None and temp[a] > c1:
        return a, "fingers"
    return count_fingers(d + e, qs, qd, rng), "counting"


def combine_columns(r_units, r_tens, r_hundreds):
    """Carry rule of section 6."""
    carry0 = r_units // 10
    s1 = r_tens + carry0
    carry1 = s1 // 10
    return (r_hundreds + carry1) * 100 + (s1 % 10) * 10 + (r_units % 10)


# --------------------------------------------------------------------------
# Model state
# --------------------------------------------------------------------------
class Model:
    def __init__(self, params):
        p = params
        self.encoding = p["encoding"]
        self.order = noticing_order(p["order"])
        self.answers = [int(a) for a in p.get("answers", [])]
        self.whole_table = {}
        for prob, tab in p.get("whole", {}).items():
            self.whole_table[prob] = {int(k): frac(v) for k, v in tab.items()}
        self.c = frac(p["c"])
        self.n = int(p["n"])
        self.c1 = frac(p["c1"])
        self.n1 = int(p["n1"])
        self.elab = frac(p["elab"])
        self.qs = frac(p["qs"])
        self.qd = frac(p["qd"])
        self.learning = bool(p.get("learning", False))
        self.inc = frac(p.get("inc", 0))
        self.inc1 = frac(p.get("inc1", 0))
        oc = dict(DEFAULT_OPEN_CHOICES)
        oc.update(p.get("open_choices", {}) or {})
        self.oc = oc
        if oc["O1"] not in ("true", "stored"):
            raise ValueError("unknown O1 choice %r" % oc["O1"])
        if oc["O2"] not in ("copy", "table", "zero", "correct"):
            raise ValueError("unknown O2 choice %r" % oc["O2"])
        if oc["O3"] not in ("none", "stored"):
            raise ValueError("unknown O3 choice %r" % oc["O3"])
        self.o2_strength = frac(p.get("o2_strength", "1/2"))
        self.commutative = bool(oc.get("single_commutative", False))

        # single-digit associations
        s = p["single"]
        sans = [int(a) for a in s.get("answers", list(range(19)))]
        dc = frac(s["default"]["correct"])
        do = frac(s["default"]["other"])
        self.single = {}
        for d in range(10):
            for e in range(10):
                key = self.skey(d, e)
                if key in self.single:
                    continue
                self.single[key] = {a: (dc if a == d + e else do) for a in sans}
        for prob, tab in (s.get("overrides") or {}).items():
            d, e = parse_problem(prob)
            assoc = self.single[self.skey(d, e)]
            for k, v in tab.items():
                assoc[int(k)] = frac(v)

        # net and whole-problem associations of stored problems
        self.net = Net(self.order)
        self.whole = {}
        for prob in p.get("familiar", []):
            self.net.learn(encode(prob, self.encoding), prob)
        for prob in self.net.stored_problems():
            self.whole[prob] = self.table_assoc(prob)

    def skey(self, d, e):
        if self.commutative:
            return (min(d, e), max(d, e))
        return (d, e)

    def table_assoc(self, prob):
        tab = self.whole_table.get(prob, {})
        assoc = {a: tab.get(a, Fraction(0)) for a in self.answers}
        for a, v in tab.items():  # answers in the table but not in "answers"
            if a not in assoc:
                assoc[a] = v
        return assoc

    def new_assoc(self, x, y):
        mode = self.oc["O2"]
        if mode == "copy":
            return dict(self.whole[y])
        if mode == "table":
            return self.table_assoc(x)
        if mode == "zero":
            return {a: Fraction(0) for a in self.answers}
        if mode == "correct":
            a, b = parse_problem(x)
            assoc = {ans: Fraction(0) for ans in self.answers}
            assoc[a + b] = self.o2_strength
            return assoc
        raise ValueError("unknown O2 choice %r" % mode)

    # ---------------------------------------------------------------
    def trial(self, x, rng):
        a, b = parse_problem(x)
        true_sum = a + b
        code = encode(x, self.encoding)
        y, path = self.net.recognize(code)
        rec = {"problem": x, "recognized_as": y, "path": path}
        answer, route, searches, columns = None, "columns", 0, []
        if y is not None:
            assoc = self.whole.setdefault(y, self.table_assoc(y))
            answer, searches = retrieve(assoc, self.c, self.n, rng)
            if answer is not None:
                route = "whole"
        if route == "columns":
            da, db = digits3(a), digits3(b)
            results = []
            for place in (2, 1, 0):  # units, tens, hundreds
                d, e = da[place], db[place]
                sa = self.single[self.skey(d, e)]
                r, strat = add_digits(d, e, sa, self.c1, self.n1, self.elab,
                                      self.qs, self.qd, rng)
                results.append(r)
                columns.append({"place": PLACES[place], "digits": [d, e],
                                "strategy": strat, "answer": r})
            answer = combine_columns(*results)
        rec.update({"route": route, "searches": searches, "columns": columns,
                    "answer": answer, "correct": answer == true_sum})
        net_learned = False
        if self.learning:
            net_learned = self.learn(x, code, y, route, answer, true_sum,
                                     columns)
        rec["net_learned"] = net_learned
        return rec

    def learn(self, x, code, y, route, answer, true_sum, columns):
        # 1. single-digit strengthening
        for col in columns:
            d, e = col["digits"]
            sa = self.single[self.skey(d, e)]
            ans = col["answer"]
            sa.setdefault(ans, Fraction(0))
            sa[ans] += 2 * self.inc1 if ans == d + e else self.inc1
        # 2. whole strengthening
        if route == "whole":
            assoc = self.whole[y]
            if self.oc["O1"] == "true":
                target = true_sum
            elif self.oc["O1"] == "stored":
                ya, yb = parse_problem(y)
                target = ya + yb
            else:
                raise ValueError("unknown O1 choice %r" % self.oc["O1"])
            assoc.setdefault(answer, Fraction(0))
            assoc[answer] += 2 * self.inc if answer == target else self.inc
        # 3. discrimination
        changed = False
        if route == "whole" and answer != true_sum:
            changed = self.net.learn(code, x)
            if changed and x not in self.whole:
                self.whole[x] = self.new_assoc(x, y)
        # 4. O3
        if route == "columns" and self.oc["O3"] == "stored":
            if x in self.whole:  # x stored in the net
                assoc = self.whole[x]
                assoc.setdefault(answer, Fraction(0))
                assoc[answer] += 2 * self.inc if answer == true_sum else self.inc
        return changed


# --------------------------------------------------------------------------
def simulate(params):
    """Yield one log record per trial."""
    model = Model(params)
    rng = random.Random(params.get("seed", 0))
    schedule = list(params["schedule"])
    repeats = int(params.get("repeats", 1))
    t = 0
    for ps in range(repeats):
        for x in schedule:
            rec = model.trial(x, rng)
            out = {"trial": t, "pass": ps}
            out.update(rec)
            yield out
            t += 1


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("params")
    ap.add_argument("--out", default="-")
    args = ap.parse_args(argv)
    with open(args.params) as fh:
        params = json.load(fh)
    fh = sys.stdout if args.out in ("-", "/dev/stdout") else open(args.out, "w")
    try:
        for rec in simulate(params):
            fh.write(json.dumps(rec) + "\n")
        fh.flush()
    except BrokenPipeError:
        # downstream closed (e.g. "| head"): silence further flush errors
        devnull = os.open(os.devnull, os.O_WRONLY)
        os.dup2(devnull, sys.stdout.fileno())
    finally:
        if fh is not sys.stdout:
            fh.close()
    return 0

if __name__ == "__main__":
    sys.exit(main())
