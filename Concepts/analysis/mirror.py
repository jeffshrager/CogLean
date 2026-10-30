"""Python mirror of Concepts (same semantics as the Lean definitions), exact in Fractions.

Selective modification (Smith, Osherson, Rips & Keane 1988) with the contrast
rule, and Hampton's (2007) threshold membership. Prints the paper's Figure 1-4
similarities and the numbers worked case.
"""
from fractions import Fraction as F

def sim(K, schema, proto, inst):
    a, b, c = K
    total = F(0)
    for i, vals in schema:
        d, votes = proto[i]
        s = F(0)
        for v in vals:
            p, q = F(votes.get(v, 0)), F(inst[i].get(v, 0))
            m = min(p, q)
            s += a * m - b * (p - m) - c * (q - m)
        total += d * s
    return total

def modify(schema, boost, i0, v0, proto):
    vals = dict(schema)[i0]
    d, votes = proto[i0]
    new = dict(proto)
    new[i0] = (boost * d, {v0: sum(F(votes.get(v, 0)) for v in vals)})
    return new

def pure(val, n):
    return {i: {val[i]: n[i]} for i in val}

def thresholdM(SL, SH, s):
    if s <= SL: return F(0)
    if s <= (SL + SH) / 2: return 2 * ((s - SL) / (SH - SL)) ** 2
    if s < SH: return 1 - 2 * ((SH - s) / (SH - SL)) ** 2
    return F(1)

K1 = (1, 1, 1)

# The paper's apple (Figs. 1-4). Only totals matter for these instances: shape 20, others 30.
apple_schema = [("color", ["red", "green", "brown"]), ("shape", ["round", "square", "cyl"]),
                ("texture", ["smooth", "rough", "bumpy"])]
apple = {"color": (F(1), {"red": 25, "green": 5}), "shape": (F(1, 2), {"round": 15, "square": 5}),
         "texture": (F(1, 4), {"smooth": 25, "rough": 5})}
n_apple = {"color": 30, "shape": 20, "texture": 30}
I1 = pure({"color": "red", "shape": "round", "texture": "smooth"}, n_apple)
I2 = pure({"color": "brown", "shape": "round", "texture": "smooth"}, n_apple)
I3 = pure({"color": "red", "shape": "round", "texture": "bumpy"}, n_apple)
RA = modify(apple_schema, 2, "color", "red", apple)
BA = modify(apple_schema, 2, "color", "brown", apple)
for name, P, I in [("A,I1", apple, I1), ("A,I2", apple, I2), ("A,I3", apple, I3),
                   ("RA,I1", RA, I1), ("RA,I2", RA, I2), ("BA,I2", BA, I2), ("BA,I1", BA, I1)]:
    print(name, sim(K1, apple_schema, P, I))

# Numbers.
def digits(n): return len(str(n))
def val(n): return {"parity": n % 2, "last": n % 10,
                    "dsum3": (n // 100 + (n // 10) % 10 + n % 10) % 3, "size": digits(n)}
num_schema = [("parity", [0, 1]), ("last", list(range(10))), ("dsum3", [0, 1, 2]), ("size", [1, 2, 3])]
def proto_of(exs):
    P = {}
    for i, vals in num_schema:
        P[i] = (F(1), {v: sum(1 for e in exs if val(e)[i] == v) for v in vals})
    return P
exs = [3 * (k + 1) for k in range(10)]
M3 = proto_of(exs)
EM3 = modify(num_schema, 2, "parity", 0, M3)
def inst(n): return pure(val(n), {i: len(exs) for i, _ in num_schema})
SL, SH = F(-50), F(0)
for n in [14, 12, 9, 15, 20]:
    s0, s1 = sim(K1, num_schema, M3, inst(n)), sim(K1, num_schema, EM3, inst(n))
    print(n, "mult3", s0, thresholdM(SL, SH, s0), " even mult3", s1, thresholdM(SL, SH, s1),
          " true:", n % 3 == 0, n % 6 == 0)
