#!/usr/bin/env python3
"""Hand-checked tests for mdsim.py."""
import json
import random
from fractions import Fraction as F

import mdsim as M

fails = 0


def check(name, got, want):
    global fails
    ok = got == want
    if not ok:
        fails += 1
    print("%-48s %s  got=%r want=%r" % (name, "ok  " if ok else "FAIL", got, want))


# ---- codes -------------------------------------------------------------
c = M.encode("106+000", "bcd")
# first addend units digit 6 = 0110 -> features 8..11 = 0,1,1,0
check("bcd 6 bits", c[8:12], (0, 1, 1, 0))
check("bcd hundreds 1", c[0:4], (1, 0, 0, 0))
check("bcd length", len(c), 24)
r = M.encode("340+400", "rich")
check("rich length", len(r), 360)
check("rich zero flag a0 units(0)", r[(0 * 3 + 2) * 10], 1)
check("rich thresholds a0 hundreds(3)", r[0:10], (0, 1, 1, 1, 0, 0, 0, 0, 0, 0))
check("rich col fact hundreds 3,4", r[60 + 0 * 100 + 34], 1)
check("rich col fact commutative", M.encode("430+300", "rich")[60 + 34], 1)
check("rich col facts one per place", sum(r[60:360]), 3)
check("beyond end reads 0", M.feature(c, 500), 0)
o = M.noticing_order("bcd_hundreds_first")
check("bcd order prefix", o[:10], [0, 1, 2, 3, 12, 13, 14, 15, 4, 5])
ro = M.noticing_order("rich_default")
check("rich order zero flags", ro[:6], [0, 30, 10, 40, 20, 50])
check("rich order thresholds start", ro[6:16], [1, 2, 3, 4, 5, 6, 7, 8, 9, 31])
check("rich order col facts start", ro[60:62], [60, 61])
check("rich order length", len(ro), 6 + 54 + 300)

# ---- net learning ---------------------------------------------------------
net = M.Net(o)
check("empty net recog", net.recognize(M.encode("1+1", "bcd")), (None, []))
check("learn into empty", net.learn(M.encode("100+100", "bcd"), "100+100"), True)
check("recognize anything as 100+100", net.recognize(M.encode("999+999", "bcd")),
      ("100+100", []))
check("relearn same -> no change", net.learn(M.encode("100+100", "bcd"), "100+100"), False)
# 100+100 vs 100+200: first diff in order is feature 12 (bit0 of 2nd hundreds: 1 vs 0)
check("learn 100+200", net.learn(M.encode("100+200", "bcd"), "100+200"), True)
check("root test", net.root["test"], 12)
check("100+100 on branch 1", net.root[1]["problem"], "100+100")
check("150+100 recognized as", net.recognize(M.encode("150+100", "bcd")),
      ("100+100", [12]))
check("123+245 recognized as", net.recognize(M.encode("123+245", "bcd")),
      ("100+200", [12]))
# discriminate 150+100 from 100+100: tens of first addend 5 vs 0 -> feature 4
check("learn 150+100", net.learn(M.encode("150+100", "bcd"), "150+100"), True)
check("150+100 now itself", net.recognize(M.encode("150+100", "bcd")),
      ("150+100", [12, 4]))
check("100+100 path", net.recognize(M.encode("100+100", "bcd")), ("100+100", [12, 4]))
# order lacking the differing feature -> no change
net2 = M.Net([0, 1])
net2.learn(M.encode("100+100", "bcd"), "a")
check("no differing feature in order", net2.learn(M.encode("100+200", "bcd"), "b"), False)
check("stored set", sorted(net.stored_problems()), ["100+100", "100+200", "150+100"])

# ---- retrieval ------------------------------------------------------------
rng = random.Random(3)
check("sure retrieval", M.retrieve({7: F(1), 8: F(0)}, F(1, 2), 1, rng), (7, 1))
check("exhausted (s == c not > c)", M.retrieve({7: F(1, 2)}, F(1, 2), 4, rng), (None, 4))
check("T == 0", M.retrieve({7: F(0)}, F(1, 2), 4, rng), (None, 0))
# Probabilities: 3/4 vs 1/4
rng = random.Random(5)
cnt = sum(M.draw({1: F(3), 2: F(1)}, rng) == 1 for _ in range(20000))
check("draw p~3/4 (within 0.02)", abs(cnt / 20000 - 0.75) < 0.02, True)
# stated with prob 3/4 per search (only answer 1 above c); n=2 -> 1-(1/4)^2
rng = random.Random(6)
st = sum(M.retrieve({1: F(3), 2: F(1)}, F(2), 2, rng)[0] == 1 for _ in range(20000))
check("n=2 statement rate ~15/16", abs(st / 20000 - 15 / 16) < 0.01, True)

# ---- single-digit addition -------------------------------------------------
ans = {a: (F(1, 2) if a == 5 else F(1, 50)) for a in range(19)}
fs = M.fingers_strengths(ans, 5, F(1, 20))
check("fingers correct strength", fs[5], (F(1, 2) + F(1, 20)) / (1 + F(1, 20)))
check("fingers correct = 11/21", fs[5], F(11, 21))
check("fingers other", fs[4], F(1, 50) / F(21, 20))
check("fingers total = 1 when T=1-elab... (T+e)/(1+e)",
      sum(fs.values()), (sum(ans.values()) + F(1, 20)) / F(21, 20))
check("original untouched", ans[5], F(1, 2))
rng = random.Random(1)
check("counting no errors", M.count_fingers(7, F(0), F(0), rng), 7)
check("counting all skipped", M.count_fingers(7, F(1), F(0), rng), 0)
check("counting all doubled", M.count_fingers(7, F(0), F(1), rng), 14)
# retrieval succeeds always when correct strength 1, c1 = 1/2
rng = random.Random(2)
check("add_digits retrieval",
      M.add_digits(2, 3, {5: F(1)}, F(1, 2), 1, F(1, 20), F(0), F(0), rng), (5, "retrieval"))
# retrieval never states (all <= c1); fingers: only answer 5 > c1 after elab
rng = random.Random(2)
res = [M.add_digits(2, 3, {5: F(1, 2), 4: F(1, 2)}, F(1, 2), 1, F(1, 20), F(0), F(0), rng)
       for _ in range(2000)]
check("fingers or counting only", set(s for _, s in res) <= {"fingers", "counting"}, True)
check("all answers 5 (no counting errors)", set(a for a, _ in res), {5})
# all strengths 0 except an answer at 0: fingers temp strength elab/(1+elab) <= c1 -> counting
rng = random.Random(2)
check("falls to counting", M.add_digits(4, 4, {8: F(0)}, F(1, 2), 1, F(1, 20),
                                        F(0), F(0), rng), (8, "counting"))

# ---- columns and carrying -------------------------------------------------
check("999+999 carry", M.combine_columns(18, 18, 18), 1998)
check("no carry 123+245", M.combine_columns(8, 6, 3), 368)
check("units 20 carries 2", M.combine_columns(20, 9, 0), 110)
check("tens 9 + carry 1 -> carry into hundreds", M.combine_columns(10, 9, 0), 100)
check("hundreds may exceed 9", M.combine_columns(0, 0, 25), 2500)
check("big counting error tens 23 + carry 1", M.combine_columns(15, 23, 1), 345)

# ---- full trial: deterministic columns -----------------------------------
params = {
    "encoding": "bcd", "order": "bcd_hundreds_first", "familiar": [],
    "answers": [], "whole": {}, "c": "1/2", "n": 1,
    "single": {"answers": list(range(19)), "default": {"correct": "1", "other": "0"}},
    "c1": "1/2", "n1": 1, "elab": "1/20", "qs": "0", "qd": "0",
    "learning": True, "inc": "1/20", "inc1": "1/20",
    "schedule": ["789+456"], "repeats": 1, "seed": 1,
}
rec = next(M.simulate(params))
check("789+456 answer", rec["answer"], 1245)
check("789+456 columns", [(c["place"], c["digits"], c["answer"], c["strategy"])
                          for c in rec["columns"]],
      [("units", [9, 6], 15, "retrieval"), ("tens", [8, 5], 13, "retrieval"),
       ("hundreds", [7, 4], 11, "retrieval")])
check("789+456 correct, route", (rec["correct"], rec["route"], rec["recognized_as"]),
      (True, "columns", None))
# strengthening check: 2*inc1 for correct answer
m = M.Model(params)
m.trial("789+456", random.Random(0))
check("single strengthened 2*inc1", m.single[(9, 6)][15], F(1) + F(2, 20))
check("single other unchanged", m.single[(6, 9)][15], F(1))

# whole route + discrimination
p2 = dict(params, familiar=["100+100"], answers=[200, 250],
          whole={"100+100": {"200": "1"}}, schedule=["150+100"])
m = M.Model(p2)
rec = m.trial("150+100", random.Random(0))
check("whole-route wrong answer", (rec["route"], rec["answer"], rec["correct"]),
      ("whole", 200, False))
check("discrimination happened", rec["net_learned"], True)
check("O1=true: wrong -> +inc", m.whole["100+100"][200], F(1) + F(1, 20))
check("O2=zero new assoc", m.whole["150+100"], {200: F(0), 250: F(0)})
rec = m.trial("150+100", random.Random(0))
check("2nd trial: recognized, exhausted -> columns",
      (rec["recognized_as"], rec["route"], rec["searches"], rec["answer"]),
      ("150+100", "columns", 0, 250))
check("O3=stored: correct columns answer +2*inc", m.whole["150+100"][250], F(1, 10))
p3 = dict(p2, open_choices={"O1": "stored"})
m = M.Model(p3)
m.trial("150+100", random.Random(0))
check("O1=stored: 200 is y's sum -> +2*inc", m.whole["100+100"][200], F(11, 10))

print("\n%s (%d failures)" % ("ALL OK" if fails == 0 else "FAILURES", fails))
raise SystemExit(1 if fails else 0)
