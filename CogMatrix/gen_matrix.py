"""Generate ../notes/MATRIX.md from the cells in CogMatrix/Matrix/*.lean.

A cell is a theorem about a family and a law, named `<law>`, `not_<law>` or
`never_<law>`. Its verdict is read from its statement, not its name
(`cell_shape.lean`): a law or its negation, and whether the family's
parameters are bound by the theorem (every setting, within the hypotheses
it states) or fixed (one setting).

* **has**: the law holds at every setting.
* **never**: the law fails at every setting.
* **lacks**: the law fails at one setting (a counterexample).
* **can hold**: the law holds at one setting.

The name must agree with the statement: `<law>` for a law, `not_<law>` for
a negation at one setting, `never_<law>` for a negation at every setting.
Every cell is also checked with `#print axioms`. A cell that depends on
`sorryAx` or on any axiom beyond Lean's standard three is marked
**unproved**, and the script exits with an error. Run from CogMatrix/.
"""
import re, pathlib, json, subprocess, sys, tempfile

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

LAWS = ["certainty", "stability", "orderFree", "recency", "storedOnly", "determinate"]
LAW_NAMES = {"certainty": "Certainty", "stability": "Stability",
             "orderFree": "Order-freedom", "recency": "Recency",
             "storedOnly": "Stored-only", "determinate": "Determinate"}
LAW_CONSTS = {l: "Cog.Laws." + l[0].upper() + l[1:] for l in LAWS}
FAMILIES = [("Discrimination", "Discrimination (EPAM)", "Cog.netRetriever"),
            ("Activation", "Activation (ACT-R, d = 1, s = 1)", "Cog.actRetriever"),
            ("Strength", "Strength with a criterion (DOA)", "Cog.strRetriever"),
            ("Minerva", "Global matching (MINERVA 2)", "Cog.minRetriever")]
STRONG = {"has", "never"}            # claims about every setting
POSITIVE = {"has", "can hold"}

# Candidate cells, by name.
cands = []                           # (family, law, prefix, full name)
for fam, _, _ in FAMILIES:
    src = pathlib.Path(f"CogMatrix/Matrix/{fam}.lean").read_text()
    for m in re.finditer(r"^theorem (not_|never_)?(\w+)", src, re.M):
        pre, law = m.group(1) or "", m.group(2)
        if law in LAWS:
            cands.append((fam, law, pre, f"Cog.Matrix.{fam}.{pre}{law}"))

# Build, then read each cell's statement and axioms.
build = subprocess.run(["lake", "build"], capture_output=True, text=True)
if build.returncode:
    sys.exit("lake build failed; fix the build before generating the matrix:\n" + build.stdout[-3000:] + build.stderr[-1000:])
with tempfile.TemporaryDirectory() as d:
    f = pathlib.Path(d, "Cells.lean")
    f.write_text(pathlib.Path("cell_shape.lean").read_text() + "\n" + "".join(
        f"#print axioms {n}\n#eval show MetaM Unit from do IO.println (← cellShape `{n})\n"
        for *_, n in cands))
    res = subprocess.run(["lake", "env", "lean", str(f)], capture_output=True, text=True)
report = res.stdout + res.stderr
if res.returncode:
    sys.exit("checking the cells failed:\n" + report)

errors = []
cells = {}                           # (family, law) -> list of (verdict, name)
unproved = {}
for fam, law, pre, n in cands:
    m = re.search(rf"'{re.escape(n)}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", report)
    sh = re.search(rf"^{re.escape(n)}\|(\w+)\|(\S+)\|(\S+)\|(\w+)$", report, re.M)
    if not m or not sh:
        sys.exit(f"no report for {n}:\n{report}")
    bad = sorted({a.strip() for a in (m.group(2) or "").split(",") if a.strip()} - STANDARD_AXIOMS)
    neg, lawc, famc, general = sh.group(1) == "true", sh.group(2), sh.group(3), sh.group(4) == "true"
    fam_const = next(c for f_, _, c in FAMILIES if f_ == fam)
    if lawc != LAW_CONSTS[law] or famc != fam_const:
        errors.append(f"{n} is about {lawc} for {famc}, not {LAW_CONSTS[law]} for {fam_const}")
        continue
    verdict = {(False, True): "has", (False, False): "can hold",
               (True, True): "never", (True, False): "lacks"}[(neg, general)]
    expected = {"": POSITIVE, "not_": {"lacks"}, "never_": {"never"}}[pre]
    if verdict not in expected:
        errors.append(f"{n}: its statement says **{verdict}**, which its name does not")
    cells.setdefault((fam, law), []).append((verdict, f"`{fam}.{pre}{law}`"))
    if bad:
        unproved[(fam, law)] = unproved.get((fam, law), []) + [(f"`{fam}.{pre}{law}`", bad)]
if errors:
    sys.exit("cells whose statements do not match their names:\n" + "\n".join(errors))

def verdict(fam, law):
    """The cell's verdict and the theorem behind it: the strongest claim proved."""
    vs = cells.get((fam, law), [])
    if not vs:
        return ("open", "")
    pos = [v for v in vs if v[0] in POSITIVE]
    neg = [v for v in vs if v[0] not in POSITIVE]
    if pos and neg:
        if any(v[0] in STRONG for v in pos) and any(v[0] in STRONG for v in neg):
            sys.exit(f"{fam}: both has and never proved for {law}")
        return ("depends", f"{max(pos)[1]}, {max(neg)[1]}")
    best = next((v for v in vs if v[0] in STRONG), vs[0])
    return best

out = ["# The theory matrix", "",
       "Generated by `gen_matrix.py` from `CogMatrix/Matrix/*.lean`; do not edit.", "",
       "Each cell is a theorem, and its verdict is read from the theorem's statement. A family's parameters "
       "are either bound by the theorem, so that it claims something for **every setting** (within the "
       "hypotheses the theorem states), or fixed, so that it claims something for **one setting**:", "",
       "- **has**: the law holds at every setting (a general proof);",
       "- **never**: the law fails at every setting (a general proof);",
       "- **lacks**: the law fails at one setting (a counterexample); other settings may have it;",
       "- **can hold**: the law holds at one setting; other settings may lack it.", "",
       "Only **has** and **never** speak for the whole family, so only they can be refuted by evidence. "
       "Theorem names are in `Cog.Matrix`.", "",
       "| Family | " + " | ".join(LAW_NAMES[l] for l in LAWS) + " |",
       "|---|" + "---|" * len(LAWS)]
for fam, title, _ in FAMILIES:
    row = []
    for l in LAWS:
        v, name = verdict(fam, l)
        if v == "open":
            row.append("open")
        elif (fam, l) in unproved:
            row.append(f"**unproved** ({v}?) {name}, uses " +
                       ", ".join(sorted({a for _, ax in unproved[(fam, l)] for a in ax})))
        else:
            row.append(f"**{v}** {name}")
    out.append(f"| {title} | " + " | ".join(row) + " |")
out += ["", "Every cell is checked with `#print axioms` when this file is generated: "
        + ("each depends only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), "
           "so none uses `sorry`." if not unproved else
           f"{len(unproved)} cell(s) depend on `sorry` or a non-standard axiom and are marked **unproved**."),
        "", "Where a family has both a counterexample (`not_<law>`) and a general negation (`never_<law>`), "
        "the table shows the general one."]
pol = lambda f, l: verdict(f, l)[0] in POSITIVE
missing = [(f, l) for f, _, _ in FAMILIES for l in LAWS if verdict(f, l)[0] == "open"]
out += ["", "Every law holds for some family and fails for another." if not missing
        and all(len({pol(f, l) for f, _, _ in FAMILIES}) == 2 for l in LAWS)
        else "Some laws do not yet discriminate, or have open cells."]
rows = {}
for fam, title, _ in FAMILIES:
    rows.setdefault(tuple(pol(fam, l) for l in LAWS), []).append(title)
same = [ts for ts in rows.values() if len(ts) > 1]
out += ["", "Every family has its own row." if not same else
        "Families the laws do not separate: " + "; ".join(", ".join(ts) for ts in same) + "."]

def judge(v, ev_status):
    """How a cell meets a settled piece of evidence."""
    if v == "depends":
        return "fits"
    if ev_status == "has":
        return {"has": "fits", "can hold": "fits", "never": "refuted", "lacks": "open"}[v]
    return {"never": "fits", "lacks": "fits", "has": "refuted", "can hold": "open"}[v]

ev = json.loads(pathlib.Path("evidence.json").read_text())
out += ["", "## Against the evidence about people", "",
        "This row is different in kind from the theorem cells above. It is a judgment of what experiments "
        "show about people, from `evidence.json`, with sources below; `mixed` evidence counts neither way. "
        "Against a settled judgment, a cell:", "",
        "- **fits** when the family can do what people do: it has the law at every setting or at some setting "
        "(people have it), or lacks it at every setting or at some setting (people lack it);",
        "- is **refuted** when the family can't: it never has the law and people have it, or it has the law "
        "at every setting and people lack it;",
        "- is **open** when the cell is about one setting only and the evidence goes the other way: whether some "
        "other setting does what people do isn't proved either way.", "",
        "| | " + " | ".join(LAW_NAMES[l] for l in LAWS) + " |",
        "|---|" + "---|" * len(LAWS),
        "| People | " + " | ".join(f"*{ev[l]['status']}*" for l in LAWS) + " |", "",
        "| Family | Fits | Refuted on | Open on |", "|---|---|---|---|"]
settled = [l for l in LAWS if ev[l]["status"] in ("has", "lacks")]
judged = {f: {l: judge(verdict(f, l)[0], ev[l]["status"]) for l in settled} for f, _, _ in FAMILIES}
for fam, title, _ in FAMILIES:
    j = judged[fam]
    names = lambda k: ", ".join(LAW_NAMES[l] for l in settled if j[l] == k) or "none"
    out.append(f"| {title} | {sum(v == 'fits' for v in j.values())} of {len(settled)} | "
               f"{names('refuted')} | {names('open')} |")
alive = [t for f, t, _ in FAMILIES if "refuted" not in judged[f].values()]
full = [t for f, t, _ in FAMILIES if all(v == "fits" for v in judged[f].values())]
out += ["", ("Families not refuted by the evidence judged settled: " + "; ".join(alive) + ".") if alive
        else "Every family is refuted by some evidence judged settled.",
        ("Families that fit all of it: " + "; ".join(full) + ".") if full else "No family fits all of it.",
        "", "Each judgment rests on a bridge from what an experiment measures (reports, decisions) to what a law "
        "is about (what memory retrieves). The bridges are stated below and are not formalized, so a fit or a "
        "refutation here is a hypothesis, not a result."]
out += ["", "### Evidence", ""]
for l in LAWS:
    out.append(f"- **{LAW_NAMES[l]}** (*{ev[l]['status']}*). {ev[l]['summary']} *Bridge:* {ev[l]['bridge']}")
    for src in ev[l]["sources"]:
        out.append(f"  - {src}")
pathlib.Path("../notes/MATRIX.md").write_text("\n".join(out) + "\n")
print("\n".join(out))
if unproved:
    sys.exit("unproved cells: " + ", ".join(n for v in unproved.values() for n, _ in v))
