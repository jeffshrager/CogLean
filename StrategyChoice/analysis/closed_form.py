"""Closed-form predictions of the distributions-of-associations model
(Siegler & Shrager 1984, p. 250) for the six problems whose associative
strengths are reproduced in the ACT-R tutorial (unit 5, siegler.lisp).

Same semantics as StrategyChoice/Data.lean and CogLib's Process/SampledRetrieval:
R = strength above the criterion / total strength; overt use (1-R)^n;
retrieval error share = wrong strength above the criterion / strength above it.
Exact rationals, so Lean's `decide` can certify the same numbers.
"""
from fractions import Fraction as F

OTHER = 99  # the "other" column: never a correct answer
ANSWERS = [0, 1, 2, 3, 4, 5, 6, 7, 8, OTHER]
PROBLEMS = [(1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)]
# Rows of Fig. 9.2A, in hundredths, as in the ACT-R tutorial's *siegler-data*.
STRENGTHS = [
    [0, 5, 86, 0, 2, 0, 2, 0, 0, 6],
    [0, 4, 7, 75, 4, 0, 2, 0, 0, 9],
    [0, 2, 0, 10, 75, 5, 1, 3, 0, 6],
    [2, 0, 4, 5, 80, 4, 0, 5, 0, 0],
    [0, 0, 7, 9, 25, 45, 8, 1, 1, 6],
    [4, 0, 0, 5, 21, 9, 48, 0, 2, 11],
]
CRITERIA = [F(x, 100) for x in (5, 10, 15, 20, 30, 40, 50, 60, 70, 80, 90, 100)]
LENGTHS = range(1, 7)


def strengths(row):
    return {a: F(w, 100) for a, w in zip(ANSWERS, row)}


def reach(s, cc):
    return sum(v for v in s.values() if v > cc) / sum(s.values())


def error_share(s, cc, correct):
    above = sum(v for v in s.values() if v > cc)
    wrong = sum(v for a, v in s.items() if v > cc and a != correct)
    return wrong / above if above else None


def mean_overt(s):
    return sum((1 - reach(s, cc)) ** n for cc in CRITERIA for n in LENGTHS) / (len(CRITERIA) * len(LENGTHS))


def mean_error_share(s, correct):
    xs = [error_share(s, cc, correct) for cc in CRITERIA]
    xs = [x for x in xs if x is not None]
    return sum(xs) / len(xs), len(xs)


if __name__ == "__main__":
    for (a, b), row in zip(PROBLEMS, STRENGTHS):
        s = strengths(row)
        mo = mean_overt(s)
        me, k = mean_error_share(s, a + b)
        print(f"{a}+{b}: total {sum(s.values())}  peak {max(s.values())}  "
              f"mean overt {float(mo):.4f} ({mo})  mean error share {float(me):.4f} over {k} criteria")
