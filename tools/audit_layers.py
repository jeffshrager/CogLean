"""
The mechanical layer audit (see notes/LAYERING_POLICY.md).

    python3 tools/audit_layers.py <tag>            # write notes/audits/<tag>/MECHANICAL.md, metrics.json
    python3 tools/audit_layers.py --merge <tag>     # add REVIEW.md's new findings to notes/audits/FINDINGS.md
    python3 tools/audit_layers.py <tag> --root DIR  # audit another copy of the repo (for testing)
    python3 tools/audit_layers.py <tag> --only CogLib,EPAM   # audit some packages only

Run from the repository root. It builds each package, runs tools/audit_meta.lean in the
package's environment, scans the sources, and reports departures from the policy. It flags;
it decides nothing. The judgment review is a separate step (tools/AUDIT_BRIEF.md).
"""
import json, os, re, subprocess, sys, tempfile, tomllib

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENV = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"])
SEP = "\x1f"

# directory -> import root (the lean_lib name); order is roughly bottom-up
PACKAGES = ["CogLib", "EPAM", "StrategyChoice", "CogMatrix", "MultiDigit", "Experiments",
            "Concepts", "SemanticMemory", "ViewApplication", "DeviceLearning", "Sims", "ACTR"]


def lake_info(root, d):
    with open(os.path.join(root, d, "lakefile.toml"), "rb") as f:
        t = tomllib.load(f)
    libs = [l["name"] for l in t.get("lean_lib", [])]
    reqs = []
    for r in t.get("require", []):
        if "path" in r:
            reqs.append(os.path.basename(os.path.normpath(r["path"])))
        else:
            reqs.append(r["name"])  # external, e.g. mathlib
    return libs, reqs


def run_meta(root, d, lib):
    meta = open(os.path.join(root, "tools", "audit_meta.lean")).read()
    r = subprocess.run(["lake", "build"], cwd=os.path.join(root, d), env=ENV, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"{d}: lake build failed:\n{r.stdout[-2000:]}{r.stderr[-2000:]}")
    src = f"import Lean\nimport {lib}\n{meta}\n#eval show Lean.Meta.MetaM Unit from audLine [`{lib}]\n"
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=os.path.join(root, d)) as f:
        f.write(src)
        path = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", path], cwd=os.path.join(root, d), env=ENV,
                           capture_output=True, text=True)
    finally:
        os.unlink(path)
    if r.returncode != 0:
        sys.exit(f"{d}: audit meta failed:\n{r.stdout[-3000:]}{r.stderr[-3000:]}")
    rows, aux = [], {}
    for line in r.stdout.splitlines():
        p = line.split(SEP)
        if len(p) == 3 and p[0] == "AUX":
            aux.setdefault(p[1], set()).update(u for u in p[2].split(",") if u)
            continue
        if len(p) != 10:
            continue
        name, kind, mod, q, lit, h, head, used, ty, hl = p
        rows.append(dict(name=name, kind=kind, mod=mod, pkg=d, q=q == "true", lit=lit == "true",
                         hash=h, head=head, used=[u for u in used.split(",") if u],
                         ty=[u for u in ty.split(",") if u], headline=hl == "true"))
    for r in rows:  # fold auxiliary proofs into their declarations
        extra = aux.get(r["name"], set()) - set(r["used"]) - {r["name"]}
        r["used"] = sorted(set(r["used"]) | extra)
    return rows


def lean_files(root, d, lib):
    base = os.path.join(root, d)
    out = []
    for dirpath, dirs, files in os.walk(base):
        dirs[:] = [x for x in dirs if x not in (".lake", "paper", "sim", "analysis", "IPL")]
        for fn in files:
            if fn.endswith(".lean") and not fn.startswith("audit"):
                out.append(os.path.join(dirpath, fn))
    return sorted(out)


def imports_of(path):
    out = []
    for line in open(path):
        m = re.match(r"\s*import\s+([A-Za-z0-9_.]+)", line)
        if m:
            out.append(m.group(1))
    return out


def load_vocab(root):
    cats = {}
    cur = None
    for line in open(os.path.join(root, "tools", "audit_vocab.txt")):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[") and line.endswith("]"):
            cur = line[1:-1]
            cats[cur] = []
        else:
            cats[cur] += line.split()
    return cats


def words_of_ident(name):
    out = []
    for comp in name.split("."):
        for part in comp.split("_"):
            out += re.findall(r"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|[0-9]+", part)
    return [w.lower() for w in out]


def comment_lines(path):
    """(line number, text) for lines inside comments or docstrings."""
    out = []
    depth = 0
    for i, line in enumerate(open(path), 1):
        text = ""
        j = 0
        while j < len(line):
            if line.startswith("/-", j):
                depth += 1
                j += 2
                continue
            if depth and line.startswith("-/", j):
                depth -= 1
                j += 2
                continue
            if not depth and line.startswith("--", j):
                text += line[j + 2:]
                break
            if depth:
                text += line[j]
            j += 1
        if text.strip():
            out.append((i, text))
    return out


def used_in_coglib_all(coglib):
    s = set()
    for r in coglib:
        s.update(u for u in r["used"] if u != r["name"])
    return s


def short(n):
    return n.split(".")[-1]


def audit(root, tag, only=None):
    global PACKAGES
    if only:
        PACKAGES = [d for d in PACKAGES if d in only]
    info = {d: lake_info(root, d) for d in PACKAGES}
    lib_of = {d: info[d][0][0] for d in PACKAGES}
    pkg_of_root = {lib_of[d]: d for d in PACKAGES}

    # 1. dependencies
    dep_rows, dep_viol = [], []
    for d in PACKAGES:
        libs, reqs = info[d]
        used_pkgs = set()
        for f in lean_files(root, d, lib_of[d]):
            for imp in imports_of(f):
                r = imp.split(".")[0]
                if r in pkg_of_root and pkg_of_root[r] != d:
                    used_pkgs.add(pkg_of_root[r])
                elif r == "Mathlib":
                    used_pkgs.add("mathlib")
        dep_rows.append((d, sorted(reqs), sorted(used_pkgs)))
        if d == "CogLib" and (reqs or used_pkgs):
            dep_viol.append(f"CogLib requires or imports {sorted(set(reqs) | used_pkgs)}")
        if "mathlib" in reqs + list(used_pkgs) and d != "ACTR":
            dep_viol.append(f"{d} uses Mathlib")
        if "Sims" in reqs or "Sims" in used_pkgs:
            dep_viol.append(f"{d} requires Sims")
    # imports must be within declared requires (transitively)
    def closure(d, seen=None):
        seen = seen or set()
        for r in info.get(d, ([], []))[1]:
            if r not in seen:
                seen.add(r)
                if r in info:
                    closure(r, seen)
        return seen
    dep_unused = []
    for d, reqs, used in dep_rows:
        extra = [u for u in used if u not in closure(d)]
        if extra:
            dep_viol.append(f"{d} imports {extra} without requiring them")
        idle = [r for r in reqs if r in info and r not in used]
        if idle:
            dep_unused.append(f"{d} requires {idle} but imports nothing from them")

    # declarations
    cache = os.environ.get("AUDIT_ROWS")  # reuse a rows.json (for developing the report)
    if cache:
        rows = json.load(open(cache))
    else:
        rows = []
        for d in PACKAGES:
            print(f"{d}...", file=sys.stderr)
            rows += run_meta(root, d, lib_of[d])
    rows.sort(key=lambda r: r["name"])  # Lean's environment order is not deterministic
    by_name = {r["name"]: r for r in rows}
    coglib = [r for r in rows if r["pkg"] == "CogLib"]
    coglib_names = {r["name"] for r in coglib}

    # 2. metrics
    metrics = {}
    for d in PACKAGES:
        rs = [r for r in rows if r["pkg"] == d]
        files = lean_files(root, d, lib_of[d])
        metrics[d] = dict(
            modules=len(files), lines=sum(sum(1 for _ in open(f)) for f in files),
            defs=sum(r["kind"] == "def" for r in rs),
            theorems=sum(r["kind"] == "thm" for r in rs),
            general=sum(r["kind"] == "thm" and r["q"] for r in rs),
            instances=sum(r["kind"] == "thm" and not r["q"] for r in rs),
            axioms=sum(r["kind"] == "axiom" for r in rs))

    # 3. lexical leakage in CogLib
    vocab = load_vocab(root)
    word_cat = {w.lower(): c for c, ws in vocab.items() for w in ws}
    ident_hits = []
    for r in coglib:
        ws = set(words_of_ident(r["name"]))
        hit = sorted(w for w in ws if w in word_cat)
        if hit:
            ident_hits.append((r["name"], r["mod"], ", ".join(f"{w} ({word_cat[w]})" for w in hit)))
    doc_hits = []
    for f in lean_files(root, "CogLib", "CogLib"):
        rel = os.path.relpath(f, root)
        for ln, text in comment_lines(f):
            for w in re.findall(r"[A-Za-z]+", text):
                if w.lower() in word_cat:
                    doc_hits.append((rel, ln, w, word_cat[w.lower()]))
    doc_hits = sorted(set(doc_hits))

    # 4. concrete settings in CogLib
    inst = sorted(r["name"] for r in coglib if r["kind"] == "thm" and not r["q"])
    lits = sorted(r["name"] for r in coglib if r["lit"])

    # 5. duplication
    AUTO = {"ctorElim", "ctorElimType", "elim", "go", "ofNat", "toCtorIdx", "brecOn", "below"}
    names_by_short = {}
    for r in rows:
        s_ = short(r["name"])
        if s_ in AUTO or len(s_) <= 2:
            continue
        # settings (closed defs) are expected to recur across packages; theorems and general defs are not
        if r["kind"] == "thm" or (r["kind"] == "def" and r["q"]):
            names_by_short.setdefault(s_, []).append(r)
    same_name = []
    for s, rs in sorted(names_by_short.items()):
        pk = sorted({r["pkg"] for r in rs})
        if len(pk) > 1:
            same_name.append((s, ", ".join(f"`{r['name']}` ({r['pkg']})" for r in sorted(rs, key=lambda r: (r["pkg"], r["name"])))))
    by_hash = {}
    for r in rows:
        if r["kind"] == "thm":
            by_hash.setdefault(r["hash"], []).append(r)
    same_stmt = []
    for h, rs in sorted(by_hash.items()):
        pk = {r["pkg"] for r in rs}
        if len(pk) > 1:
            same_stmt.append(", ".join(f"`{r['name']}` ({r['pkg']})" for r in sorted(rs, key=lambda r: (r["pkg"], r["name"]))))
    same_stmt.sort()
    relabel = []
    for r in rows:
        if r["pkg"] == "CogLib" or r["kind"] != "thm":
            continue
        cands = [u for u in r["used"] if u in coglib_names and short(u) == short(r["name"])
                 and by_name[u]["kind"] == "thm"]
        if cands or (r["head"] in coglib_names and by_name.get(r["head"], {}).get("kind") == "thm"):
            target = cands[0] if cands else r["head"]
            relabel.append((r["name"], r["pkg"], target))
    relabel.sort()

    # 6. promotion candidates
    promo = []
    for r in rows:
        if r["pkg"] in ("CogLib", "Sims", "ACTR") or r["kind"] not in ("thm", "def"):
            continue
        if not r["q"]:
            continue
        if all(u in coglib_names for u in r["ty"]):
            proof_too = all(u in coglib_names for u in r["used"])
            promo.append((r["name"], r["pkg"], r["kind"] + (", proof too" if proof_too else "")))
    promo.sort()

    # 9. proof trees
    graph = {r["name"]: set(r["used"]) for r in rows}
    pkg_of = {r["name"]: r["pkg"] for r in rows}
    memo = {}
    def closure(n):
        if n in memo:
            return memo[n]
        seen, stack = set(), [n]
        while stack:
            x = stack.pop()
            for y in graph.get(x, ()):
                if y not in seen and y != n:
                    seen.add(y)
                    stack.append(y)
        memo[n] = seen
        return seen
    shares = []
    for r in rows:
        if r["pkg"] in ("CogLib", "Sims") or r["kind"] != "thm" or not r["headline"]:
            continue
        cl = [x for x in closure(r["name"]) if by_name.get(x, {}).get("kind") == "thm"]
        lib = sum(pkg_of.get(x) == "CogLib" for x in cl)
        own = sum(pkg_of.get(x) == r["pkg"] for x in cl)
        oth = len(cl) - lib - own
        shares.append((r["pkg"], r["name"], len(cl), lib, own, oth))
    shares.sort(key=lambda t: (t[0], t[2] == 0, t[3] / t[2] if t[2] else 1, t[1]))
    # own lemmas in headline proof trees that are themselves generic (statement and proof in CogLib terms)
    in_trees = set()
    for _, n, *_ in shares:
        in_trees |= closure(n)
    generic_in_trees = sorted(
        (x, pkg_of[x]) for x in in_trees
        if pkg_of.get(x) not in (None, "CogLib", "ACTR", "Sims") and by_name[x]["kind"] == "thm"
        and by_name[x]["q"] and all(u in coglib_names for u in by_name[x]["ty"])
        and all(u in coglib_names for u in closure(x)))
    # repeated proof shapes: the same set of CogLib theorems used directly, in two packages
    lib_thms = {r["name"] for r in coglib if r["kind"] == "thm"}
    sig = {}
    for r in rows:
        if r["kind"] != "thm" or r["pkg"] in ("CogLib",):
            continue
        k = frozenset(u for u in r["used"] if u in lib_thms)
        if len(k) >= 3:
            sig.setdefault(k, []).append(r)
    shapes = []
    for k, rs in sig.items():
        if len({r["pkg"] for r in rs}) > 1:
            shapes.append((", ".join(f"`{r['name']}` ({r['pkg']})" for r in sorted(rs, key=lambda r: (r["pkg"], r["name"]))),
                           ", ".join(f"`{short(x)}`" for x in sorted(k))))
    shapes.sort()
    near = []
    items = [(r, frozenset(u for u in r["used"] if u in lib_thms)) for r in rows
             if r["kind"] == "thm" and r["pkg"] != "CogLib"]
    items = [(r, k) for r, k in items if len(k) >= 4]
    for i in range(len(items)):
        for j in range(i + 1, len(items)):
            (a, ka), (b, kb) = items[i], items[j]
            if a["pkg"] == b["pkg"] or ka == kb:
                continue
            jac = len(ka & kb) / len(ka | kb)
            if jac >= 0.75:
                if b["name"] < a["name"]:
                    a, b = b, a
                near.append((round(jac, 2), a["name"], a["pkg"], b["name"], b["pkg"], len(ka & kb)))
    near.sort(key=lambda t: (-t[0], t[1], t[3]))
    # CogLib theorems used directly by exactly one package above, and by nothing in CogLib
    thm_users = {n: set() for n in lib_thms}
    for r in rows:
        if r["pkg"] == "CogLib":
            continue
        for u in r["used"]:
            if u in thm_users:
                thm_users[u].add(r["pkg"])
    single_thm = sorted((n, sorted(thm_users[n])[0]) for n in lib_thms
                        if len(thm_users[n]) == 1 and n not in used_in_coglib_all(coglib))

    # 7. fan-out of CogLib defs
    users = {n: set() for n in coglib_names}
    for r in rows:
        for u in r["used"]:
            if u in users and r["pkg"] != "CogLib":
                users[u].add(r["pkg"])
    used_in_coglib = set()
    for r in coglib:
        used_in_coglib.update(u for u in r["used"] if u != r["name"])
    single = sorted((n, sorted(users[n])[0]) for n in coglib_names
                    if by_name[n]["kind"] == "def" and len(users[n]) == 1 and n not in used_in_coglib)
    unused = sorted(n for n in coglib_names
                    if by_name[n]["kind"] == "def" and not users[n] and n not in used_in_coglib)

    counts = dict(dependency_violations=len(dep_viol), unused_requires=len(dep_unused), identifier_hits=len(ident_hits),
                  docstring_hits=len(doc_hits), coglib_instances=len(inst), coglib_literal_defs=len(lits),
                  same_name=len(same_name), same_statement=len(same_stmt), relabellings=len(relabel),
                  promotion_candidates=len(promo), single_user_defs=len(single), unused_defs=len(unused),
                  headline_trees=len(shares), generic_lemmas_in_trees=len(generic_in_trees),
                  repeated_proof_shapes=len(shapes), near_proof_shapes=len(near),
                  single_user_theorems=len(single_thm))

    # 8. trend
    adir = os.path.join(root, "notes", "audits")
    prev = None
    if os.path.isdir(adir):
        olds = sorted(x for x in os.listdir(adir) if x != tag and os.path.isfile(os.path.join(adir, x, "metrics.json")))
        if olds:
            prev = (olds[-1], json.load(open(os.path.join(adir, olds[-1], "metrics.json"))))

    L = [f"# Mechanical layer audit: {tag}", "",
         "Generated by `tools/audit_layers.py`; do not edit by hand. Policy: `notes/LAYERING_POLICY.md`. "
         "Every item is a flag for review, not a verdict.", ""]
    L += ["## Summary", "", "| Check | Count |" + (f" Previous ({prev[0]}) |" if prev else ""),
          "|---|---|" + ("---|" if prev else "")]
    for k, v in counts.items():
        L.append(f"| {k.replace('_', ' ')} | {v} |" + (f" {prev[1]['counts'].get(k, '—')} |" if prev else ""))
    L += ["", "## 1. Dependencies", "", "| Package | Requires (lakefile) | Imports from |", "|---|---|---|"]
    for d, reqs, used in dep_rows:
        L.append(f"| {d} | {', '.join(reqs) or '—'} | {', '.join(used) or '—'} |")
    L += ["", "Violations: " + ("none." if not dep_viol else ""), ""] + [f"- {v}" for v in dep_viol]
    L += ["", "Declared but unused: " + ("none." if not dep_unused else ""), ""] + [f"- {v}" for v in dep_unused]
    L += ["", "## 2. Metrics", "", "| Package | Modules | Lines | Defs | Theorems | General | Instances | Axioms |",
          "|---|---|---|---|---|---|---|---|"]
    for d in PACKAGES:
        m = metrics[d]
        pm = prev[1]["metrics"].get(d) if prev else None
        def cell(k):
            return f"{m[k]}" + (f" ({m[k] - pm[k]:+d})" if pm and k in pm and m[k] != pm[k] else "")
        L.append(f"| {d} | " + " | ".join(cell(k) for k in ("modules", "lines", "defs", "theorems", "general", "instances", "axioms")) + " |")
    L += ["", "## 3. Task and theory vocabulary in CogLib", "",
          "Vocabulary: `tools/audit_vocab.txt`. Identifier hits are the serious kind; docstring hits are often citations or examples.", "",
          "**In identifiers**", ""]
    L += [f"- `{n}` ({m}): {w}" for n, m, w in ident_hits] or ["- none"]
    L += ["", "**In comments and docstrings**", "", "| File | Line | Word | Category |", "|---|---|---|---|"]
    L += [f"| {f} | {ln} | {w} | {c} |" for f, ln, w, c in doc_hits] or ["| — | | | |"]
    L += ["", "## 4. Concrete settings in CogLib", "",
          "Instance theorems (closed statements) and definitions whose values are closed literals. Allowed with a note when they witness a general CogLib claim.", "",
          "**Instance theorems**", ""] + ([f"- `{n}`" for n in inst] or ["- none"])
    L += ["", "**Closed definitions with literals**", ""] + ([f"- `{n}`" for n in lits] or ["- none"])
    L += ["", "## 5. Duplication", "", "**The same name in more than one package**", ""]
    L += [f"- `{s}`: {w}" for s, w in same_name] or ["- none"]
    L += ["", "**The same statement in more than one package**", ""] + ([f"- {w}" for w in same_stmt] or ["- none"])
    L += ["", "**Relabellings**: theorems outside CogLib that restate a CogLib theorem (same name, or a proof that is one application of it)", ""]
    L += [f"- `{n}` ({p}) ← `{t}`" for n, p, t in relabel] or ["- none"]
    L += ["", "## 6. Promotion candidates", "",
          "General theorems and definitions outside CogLib whose statements mention only core and CogLib constants.", ""]
    L += [f"- `{n}` ({p}, {k})" for n, p, k in promo] or ["- none"]
    L += ["", "## 7. Fan-out of CogLib definitions", "",
          "**Used by exactly one package above CogLib, and by nothing in CogLib** (possible leaks)", ""]
    L += [f"- `{n}`: {p}" for n, p in single] or ["- none"]
    L += ["", "**Used by nothing, in CogLib or above** (not yet exercised, or dead)", ""]
    L += [f"- `{n}`" for n in unused] or ["- none"]
    L += ["", "## 8. Proof trees", "",
          "Computed from the proof terms: each declaration's edges are the repo constants its statement and proof use, with Lean's auxiliary proofs folded in.", "",
          "**What each headline theorem's proof rests on** (theorems in the transitive closure of its proof, by package), sorted by CogLib share within each package. A low CogLib share means the proof rests mostly on the package's own lemmas: theory-specific, or poorly factored.", "",
          "| Package | Headline theorem | Theorems in tree | CogLib | Own package | Other packages | CogLib share |",
          "|---|---|---|---|---|---|---|"]
    def disp(n):
        parts = n.split(".")
        return ".".join(parts[1:]) if parts[0] in ("Cog", "MD", "SC", "Epam") and len(parts) > 2 else n
    summ = {}
    for pk, n, tot, lib, own, oth in shares:
        if tot:
            summ.setdefault(pk, []).append(lib / tot)
    L += ["Per package (headline theorems with a lemma tree):", "", "| Package | Headlines | Median CogLib share | Lowest |", "|---|---|---|---|"]
    for pk in sorted(summ):
        v = sorted(summ[pk])
        L.append(f"| {pk} | {len(v)} | {v[len(v) // 2]:.0%} | {v[0]:.0%} |")
    L += ["", "| Package | Headline theorem | Theorems in tree | CogLib | Own package | Other packages | CogLib share |",
          "|---|---|---|---|---|---|---|"]
    for pk, n, tot, lib, own, oth in shares:
        if tot:
            L.append(f"| {pk} | `{disp(n)}` | {tot} | {lib} | {own} | {oth} | {lib / tot:.0%} |")
    computed = [disp(n) for pk, n, tot, *_ in shares if not tot]
    L += ["", f"Headline theorems with no lemma tree (computed by `decide`, or proved from definitions directly): {len(computed)}: " + ", ".join(f"`{c}`" for c in computed) + "."]
    L += ["", "**Generic lemmas in headline proof trees**: lemmas outside CogLib, used by some headline proof, whose statement and whole proof tree use only CogLib (and core): machinery that could move down.", ""]
    L += [f"- `{n}` ({p})" for n, p in generic_in_trees] or ["- none"]
    L += ["", "**Repeated proof shapes**: theorems in different packages whose proofs use exactly the same set of CogLib theorems (at least three). A shared pattern may be a missing general CogLib theorem.", ""]
    L += [f"- {w}: {k}" for w, k in shapes] or ["- none"]
    L += ["", "**Near proof shapes**: pairs in different packages whose direct CogLib dependencies overlap by at least 75% (Jaccard), with at least four each.", ""]
    L += [f"- {j:.2f}: `{a}` ({ap}) ~ `{b}` ({bp}), {c} shared" for j, a, ap, b, bp, c in near[:40]] or ["- none"]
    if len(near) > 40:
        L.append(f"- … and {len(near) - 40} more")
    L += ["", "**CogLib theorems exercised by exactly one package above, and by nothing in CogLib.** Expected for a new general result; worth a look when the theorem's shape fits only that package.", ""]
    L += [f"- `{n}`: {p}" for n, p in single_thm] or ["- none"]
    L.append("")

    out_dir = os.path.join(adir, tag)
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, "MECHANICAL.md"), "w") as f:
        f.write("\n".join(L))
    with open(os.path.join(out_dir, "rows.json"), "w") as f:
        json.dump(sorted(rows, key=lambda r: r["name"]), f, indent=0, sort_keys=True)
    with open(os.path.join(out_dir, "metrics.json"), "w") as f:
        json.dump(dict(tag=tag, counts=counts, metrics=metrics), f, indent=1, sort_keys=True)
    print(json.dumps(counts, indent=1))


def merge(root, tag):
    """Append REVIEW.md's new findings to FINDINGS.md, with fresh IDs."""
    rev = open(os.path.join(root, "notes", "audits", tag, "REVIEW.md")).read()
    led_path = os.path.join(root, "notes", "audits", "FINDINGS.md")
    led = open(led_path).read() if os.path.exists(led_path) else (
        "# Layer-audit findings\n\nOne row per finding, across audits. Statuses: open, accepted, "
        "refactored (commit), won't fix (reason). Edit statuses by hand; the merge only adds rows.\n\n"
        "| ID | Raised | Category | Severity | Finding | Location | Status |\n|---|---|---|---|---|---|---|\n")
    ids = [int(x) for x in re.findall(r"^\| F(\d+) \|", led, re.M)]
    nxt = max(ids, default=0) + 1
    added = 0
    for block in re.split(r"\n(?=### )", rev):
        m = re.match(r"### (.+)", block)
        if not m:
            continue
        title = m.group(1).strip()
        fld = dict(re.findall(r"^- (\w[\w ]*?): (.+)$", block, re.M))
        prior = fld.get("Prior", "new").strip()
        if prior.lower() != "new":
            continue
        led += (f"| F{nxt:03d} | {tag} | {fld.get('Category', '')} | {fld.get('Severity', '')} | "
                f"{title.replace('|', '/')} | {fld.get('Location', '').replace('|', '/')} | open |\n")
        nxt += 1
        added += 1
    with open(led_path, "w") as f:
        f.write(led)
    print(f"added {added} findings")


if __name__ == "__main__":
    args = sys.argv[1:]
    root = HERE
    if "--root" in args:
        i = args.index("--root")
        root = os.path.abspath(args[i + 1])
        del args[i:i + 2]
    only = None
    if "--only" in args:
        i = args.index("--only")
        only = args[i + 1].split(",")
        del args[i:i + 2]
    if args and args[0] == "--merge":
        merge(root, args[1])
    elif args:
        audit(root, args[0], only)
    else:
        sys.exit(__doc__)
