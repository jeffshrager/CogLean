# Specification: a simulation of multi-digit addition

This document specifies a model of how a child adds two 3-digit numbers. Implement it as a stochastic simulation in Python. It is self-contained: everything you need is here, and where the model leaves something open, that is said explicitly (section 8).

## 1. Problems

A problem is a + b, with whole numbers 0 ≤ a, b ≤ 999. Its correct answer is a + b.

- Each addend has three digits: hundreds, tens and units. A number below 100 has hundreds digit 0, and so on.
- A **column** is a place (hundreds, tens or units) together with the two digits of the addends in that place.
- Write problems as strings `"a+b"`, e.g. `"150+100"`.

## 2. Codes

A problem reaches the child as a **code**: a vector of bits, called features, indexed from 0. A feature beyond the end of a code reads as 0. There are two encodings. Addends are numbered first = 0 and second = 1; places are numbered hundreds = 0, tens = 1 and units = 2.

### 2.1 `bcd` (24 features)

- Feature `addend*12 + place*4 + k`, for k = 0..3, is bit k of that digit in binary. Bit 0 is the least significant.
- Example: the digit 6 = 0110 has bit 0 = 0, bit 1 = 1, bit 2 = 1 and bit 3 = 0.

### 2.2 `rich` (360 features)

- **Digit blocks.** For each digit, a block of 10 features starting at `(addend*3 + place)*10`:
  - offset 0: 1 if the digit is 0 (the **zero flag**);
  - offset 1 + k, for k = 0..8: 1 if the digit is greater than k (a **threshold**).
- **Column facts.** For each place, 100 features starting at `60 + place*100`. Exactly one is 1: the one at offset `min*10 + max`, where min and max are the smaller and the larger of the column's two digits. So 3+4 and 4+3 in a column set the same feature.

### 2.3 Noticing orders

A **noticing order** is a list of feature indices: the order in which features are scanned for a difference (section 3). The parameter file gives it as an explicit list, or as one of these names:

- `bcd_hundreds_first`. For place = hundreds, tens, units (in that order); then addend = first, second; then k = 0..3: the bcd feature for (addend, place, k).
- `rich_default`, the concatenation of three lists:
  1. The zero flags. For place = hundreds, tens, units; then addend = first, second.
  2. The thresholds. For place = hundreds, tens, units; then addend = first, second; then k = 0..8.
  3. The column facts. For place = hundreds, tens, units; then offset 0..99.

## 3. Recognition: a discrimination net

The child's memory of familiar problems is a **discrimination net** (EPAM). It is a binary tree:

- A **terminal** holds an image (a stored code) or nothing.
- A **test** names one feature and has two branches, one for 0 and one for 1.

**Recognition** sorts a code down the net: at each test, take the branch given by the code's value on that feature. The result is the image at the terminal reached, which may be nothing. The **path** is the list of features tested on the way down. The problem is **recognized as** the problem whose code that image is. Images are always codes of problems, so keep track of which problem each image came from.

**Learning a code x** into the net:

1. Sort x down the net to a terminal.
2. If the terminal holds nothing, put x there.
3. If it holds x itself, do nothing.
4. If it holds a different image z, scan the noticing order for the first feature f on which x and z differ.
   - If there is one, replace the terminal by a test on f, whose two branches are terminals holding x and z, each on the side of its own value of f.
   - If no feature in the order differs, do nothing.

Nothing else in the net changes. The net starts empty (one terminal holding nothing). The **familiar problems** in the parameter file are learned into it in the order given.

## 4. Retrieval from a distribution of associations

Retrieval works on **associations**: a finite list of possible answers, each with a strength ≥ 0, with total strength T > 0. It also uses a **confidence criterion** c and a **search length** n.

- **A search** draws one answer, each with probability strength/T.
- If the drawn answer's strength is strictly greater than c, it is **stated**, and retrieval ends.
- Otherwise search again, up to n searches in all.
- If no answer is stated after n searches, retrieval is **exhausted**.

## 5. Single-digit addition (used in each column)

Adding two digits d + e uses the associations of the single-digit problem d + e (its answer list and strengths), a criterion c1 and a search length n1. It proceeds in three stages; the **strategy** is the one that produces the answer.

1. **Retrieval**: as in section 4. If an answer is stated, that is the answer.
2. **Fingers**: if retrieval is exhausted, the child puts up d + e fingers.
   - Add strength `elab` to the answer d + e.
   - Then divide every strength (including that one) by 1 + `elab`.
   - Make exactly one search with these new strengths. If the drawn answer's new strength exceeds c1, state it.
   - These new strengths are used for this one search only; nothing is changed permanently.
3. **Counting**: otherwise the child counts the d + e fingers.
   - Each of the d + e objects is skipped with probability `qs`, counted twice with probability `qd`, and counted once otherwise, independently.
   - The answer is the total count.

## 6. A trial on a 3-digit problem x

1. Recognize x's code in the net.
2. If x is recognized as a stored problem y, retrieve (section 4) using **y's** whole-problem associations, with criterion c and search length n. If an answer is stated, that is the trial's answer, by the **whole** route.
3. If nothing is recognized, or retrieval is exhausted, work x out by the **columns** route:
   - Add the units column's digits (section 5); call the result r0. Write r0 mod 10, and carry ⌊r0 / 10⌋.
   - Add the tens column's digits; call the result r1. Add the carry: s1 = r1 + ⌊r0 / 10⌋. Write s1 mod 10, and carry ⌊s1 / 10⌋.
   - Add the hundreds column's digits; call the result r2. Write r2 + ⌊s1 / 10⌋ as the hundreds (it may exceed 9).
   - The answer is the number written. Note that column results can exceed 18 through counting errors; the carry rule handles any size.

Each column uses its own single-digit problem's associations, and the three columns are added independently.

## 7. Learning (between trials)

When learning is on, after each trial:

1. **Strengthening (single-digit).** For each column added in the trial, the stated single-digit answer's strength in that single-digit problem's associations increases by `inc1`, or by `2*inc1` if that answer is correct for the column (d + e). This happens whichever strategy produced it. If the answer isn't yet in the answer list, add it with strength 0 first.
2. **Strengthening (whole problem).** If the answer came by the whole route, the stated answer's strength in the associations that were used increases by `inc`, or `2*inc` if it is correct. "Correct" here is subject to open choice O1.
3. **Discrimination.** If the answer came by the whole route and was wrong (feedback tells the child), learn x's code into the net (section 3), with new associations for x (open choice O2).
4. **Column answers and whole associations** (open choice O3).

## 8. Open choices

The model doesn't settle these. Choose a default, document it in `IMPLEMENTATION_NOTES.md`, and expose each as a parameter.

- **O1.** In whole-route strengthening, is "correct" judged against the true sum of x, or against the sum of the problem y whose associations were used?
- **O2.** What are the initial associations of a newly discriminated problem: its answer list, its strengths?
- **O3.** Does a columns-route answer change the whole-problem associations of x? If so, how, and only when x is stored in the net?
- **O4.** Anything else you find underdetermined. List it.

## 9. Interface

### 9.1 Program

Write `mdsim.py`: Python 3, standard library only, with `fractions.Fraction` for all strengths and probabilities. Floating point may be used only to compare against random draws.

- Command line: `python3 mdsim.py PARAMS.json --out LOG.jsonl`
- Library: `simulate(params: dict) -> Iterator[dict]`, which yields the same records.
- Use `random.Random(seed)` for all randomness.

### 9.2 Parameter file (JSON)

Fractions are strings such as `"9/10"`, or numbers.

```json
{
  "encoding": "bcd" | "rich",
  "order": "bcd_hundreds_first" | "rich_default" | [feature indices],
  "familiar": ["100+100", "100+200"],
  "answers": [200, 250, 300],
  "whole": {"100+100": {"200": "9/10", "250": "1/100", "300": "1/100"}, "...": {}},
  "c": "1/2",
  "n": 1,
  "single": {"answers": [0, 1, ..., 18], "default": {"correct": "1/2", "other": "1/50"},
             "overrides": {"2+3": {"4": "3/10", "5": "1/2"}}},
  "c1": "1/2",
  "n1": 1,
  "elab": "1/20",
  "qs": "1/20",
  "qd": "1/20",
  "learning": false,
  "inc": "1/20",
  "inc1": "1/20",
  "open_choices": {"O1": "...", "O2": "...", "O3": "..."},
  "schedule": ["150+100", "100+100"],
  "repeats": 1000,
  "seed": 1
}
```

- **`whole`**: the whole-problem associations of each familiar problem, over `answers`. An answer missing from a problem's table has strength 0.
- **`single`**: associations for every d + e (d, e = 0..9).
  - Over `answers`, the correct answer d + e has strength `default.correct` and every other answer `default.other`.
  - `overrides` replaces the given entries for a given single-digit problem.
- **`schedule`**: the run is `repeats` passes through the schedule, one trial per problem per pass, in order.
  - With learning off, the net and all strengths stay fixed throughout.
  - With learning on, they change as in section 7.

### 9.3 Log (JSON lines, one record per trial)

```json
{"trial": 0, "pass": 0, "problem": "150+100",
 "recognized_as": "100+100" | null, "path": [features tested],
 "route": "whole" | "columns",
 "searches": number of whole-route searches made,
 "columns": [{"place": "units", "digits": [0, 0], "strategy": "retrieval" | "fingers" | "counting", "answer": 0}, ...] | [],
 "answer": 200, "correct": false,
 "net_learned": true | false}
```

- `columns` lists the units, tens and hundreds entries when the columns route is used, and is empty otherwise.
- `net_learned` says whether discrimination changed the net after this trial.

## 10. Deliverables

- `mdsim.py`.
- `IMPLEMENTATION_NOTES.md`: your choices for O1–O4, anything you found ambiguous, and a list of every file you read while working.
- A smoke test: `python3 mdsim.py example.json --out /dev/stdout | head`, with an `example.json` of your own.
