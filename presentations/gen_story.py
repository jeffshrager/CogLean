"""Generate coglean-story.tex: the key slides of the other five decks, copied
verbatim with their notes, in an order that tells the story in one talk.
Run from presentations/ (the Makefile does)."""
import re

# (deck, frame title, transition note or None). A transition opens each part.
OV, RR, LEAN, BLIND, LAWS = ("coglean-overview.tex", "recognition-retrieval.tex",
                             "recognition-retrieval-lean.tex", "blind-simulation.tex",
                             "laws-matrix-experiments.tex")
PICKS = [
    # 1. Why
    (OV, "The problem", "Part 1, why: what simulation leaves open."),
    (OV, "Three kinds of evidence a theory can give", None),
    (OV, "Why Lean", None),
    # 2. A theory, proved
    (RR, "Two theories, combined", "Part 2, a theory proved: two classic models combined into one of multi-digit addition."),
    (RR, "The multi-digit model", None),
    (RR, "Confident errors", None),
    (RR, "A worked case", None),
    # 3. How it is proved
    (LEAN, "In words: Confident errors: the proof is a composition", "Part 3, how: the proof in words, then the actual Lean."),
    (LEAN, "Confident errors: the proof is a composition", None),
    (LEAN, "What is checked, and what is not", None),
    # 4. Is the formalization faithful?
    (BLIND, "The idea: two independent readings", "Part 4, is it faithful: a blind simulation against preregistered predictions."),
    (BLIND, "The procedure", None),
    (BLIND, "Results: no failures", None),
    (BLIND, "Finding 1: five predictions were never tested", None),
    (BLIND, "Finding 3: a prediction depends on an open choice", None),
    # 5. Generalizing
    (OV, "The generality problem", "Part 5, generalizing: memory as a plug-in, and a composition reused across tasks."),
    (RR, "The same problems, two memories", None),
    (RR, "The composition, extracted", None),
    (RR, "A second task: naming people", None),
    # 6. Laws and the matrix
    (LAWS, "Six laws", "Part 6, laws: compare families of models by the laws they have."),
    (LAWS, "Four families", None),
    (LAWS, "The matrix", None),
    (LAWS, "The laws were tested, and failed once", None),
    (RR, "From laws: which memories give confident errors?", None),
    # 7. Experiments derived from laws
    (LAWS, "Reversing the workflow", "Part 7, experiments from laws: start from a disagreement, derive the design, prove the separation."),
    (LAWS, "Recency against order-freedom", None),
    (LAWS, "From retrieval to report", None),
    (LAWS, "The same design, four memories", None),
    (OV, "A related approach: SFT-GMA", None),
    # 8. What is true
    (OV, "What is true here?", "Part 8, what is true: conditional results, evidence, and limits."),
    (LAWS, "Against the evidence", None),
    (OV, "Where this is weaker than mathematics", None),
    (OV, "Next", None),
    (OV, "Take-home", None),
]

# What to say: a paragraph per slide, used as that slide's notes in place of
# the source deck's reminder bullets.
SCRIPT = {
"TITLE": """Today I want to tell you about CogLean, a project to build a machine-checked library of cognitive theory, in the spirit of Mathlib for mathematics. I'll go in eight parts: why prove things about cognitive theories at all; one theory we've proved things about; what the proofs actually look like; how we check that the formal version says what the theory says; how to generalize beyond one model; laws of memory, and a matrix comparing families of models; experiments derived from those laws; and finally, what can count as true when the theories compete.""",
"The problem": """Most of our theories live in prose, in simulation code, or as equations fitted to data. When we evaluate them, we usually run a model with particular parameters on particular stimuli and compare the output with data. That tells us the theory can produce a result. It doesn't tell us which of the theory's assumptions produced it, whether it would survive a different choice of parameters, or whether a rival theory would produce it just as well. Those are exactly the questions we care about when we compare theories, and they are rarely answered.""",
"Three kinds of evidence a theory can give": """It helps to separate three kinds of evidence. One run: one model, one parameter setting; the theory can do it. Every run: one model in all its executions, by exhaustive search or parameter sweeps; that model always does it. And every model the theory allows: the postulates entail it. That third kind is a proof, and it's what CogLean is built around. A proof tells you which assumptions matter, because it uses some postulates and not others, and it distinguishes what a theory can do from what it must do. Simulation stays essential for exploring and fitting, and experiments with people still decide whether the assumptions are right.""",
"Why Lean": """We use Lean, which is both a programming language and a proof checker. That matters because the same definition, say of a discrimination net, can be run on an experiment's stimuli and proved about for all stimuli, so the simulation and the theory can't drift apart. Every proof step is checked by a small trusted kernel. Theorems can quantify over all parameter values. And the library is cumulative: definitions are made once and reused. One caution, which I'll come back to: Lean checks that theorems follow from the definitions, not that the definitions capture the theory.""",
"Two theories, combined": """Here are two classic theories. EPAM, Feigenbaum's model of verbal learning: stimuli are feature codes, sorted through a discrimination net of feature tests, and the net grows a new test only where two codes get confused. So an unfamiliar code that matches a familiar one on every tested feature gets recognized as that familiar one. And the distributions-of-associations model of strategy choice, which Bob Siegler and I proposed: each problem has associations to answers; you sample an answer in proportion to its strength, state it if it clears a confidence criterion, try a few times, and otherwise fall back on a backup strategy such as counting.""",
"The multi-digit model": """Combine them and you get a model of three-digit addition. A problem like 150 plus 100 is first recognized by an EPAM net, perhaps as the familiar 100 plus 100. Then retrieval searches the recognized problem's associations. If nothing is recognized, or retrieval comes up empty, the child works it out column by column, where each column is itself a single-digit trial of retrieval or backup, with carries. Every postulate here is a parameter: the encoding, the net, the strengths, the criterion, the search length, the backup. The model yields eighteen predictions, each proved for every choice of those parameters.""",
"Confident errors": """Here is the prediction neither theory makes alone. Suppose a familiar problem q has sharp associations, meaning only its correct sum clears the criterion, and a stranger x with a different sum is recognized as q. Then q is never answered wrongly by retrieval; every retrieved answer to x is wrong; and x falls back on the columns exactly as rarely as q does. In the associations model alone, errors and backup use rise and fall together. Confusion breaks that tie: you get a retrieved, wrong answer with no extra backup use. Notice that I don't say fast: the model has no timing, so that would need more.""",
"A worked case": """To see it concretely: encode each digit in four bits. A net that has learned 100 plus 100 and 100 plus 200 only needs to test the second addend's hundreds digit to tell them apart. So 150 plus 100 slips through as 100 plus 100. With these strengths and a single search, it's answered 200 by retrieval with probability 45 over 46, and correctly, by the columns, with probability 1 over 46. These numbers are just an illustration, computed exactly; the structure, confident errors, holds for every choice of parameters.""",
"In words: Confident errors: the proof is a composition": """So how is that proved? Here is the proof in words first. The hypotheses are the ones I described: both problems are recognized for certain, q's associations are sharp, the correct answers differ, and the strengths and backups are well behaved. The proof has three parts, and each is a lemma we had already proved. The first is the neighbour's-answer lemma, applied to q itself. The second says that on sharp associations every stated answer is q's correct answer, which is wrong for x. And the third: both problems search the same associations, so each uses the backup with the same probability, one minus R to the n.""",
"Confident errors: the proof is a composition": """And here is the actual Lean. You don't need to read it in detail. The statement at the top is the theorem I just described, and the proof is the last five lines, which assemble those three lemmas. It's that short because the real work sits in general lemmas underneath: about probability distributions, about the search process, about nets. That's the point I want to make with this slide. In a library, a behavioral theorem is assembled from reusable parts, the way Mathlib assembles algebra.""",
"What is checked, and what is not": """What does all this guarantee? Lean will tell you exactly which axioms a theorem rests on. Here it's only Lean's three standard ones, with no unproved steps anywhere. We use core Lean without Mathlib, so everything also computes. What Lean can't check is whether the definitions say what EPAM, or the associations model, or ACT-R actually say. That is a different kind of question, and the next part is about how we tested it.""",
"The idea: two independent readings": """We borrowed an idea from fault-tolerant software, called N-version programming: build two independent implementations of one specification, and look at where they disagree. Here, one reading of the prose is the Lean formalization, whose theorems give predictions. The other is a Python simulator written without seeing any of the Lean. If they disagree, then either the prose is ambiguous, the formalization drifted, or the simulator has a bug, and in every case we learn something.""",
"The procedure": """Concretely: we wrote a prose specification with no Lean in it, and we listed explicitly the points the prose leaves open. We preregistered the predictions, committing them before the simulator existed. Then a fresh AI agent, given only the prose, wrote the simulator in an empty directory, and we audited its tool use to check that it read nothing else. Lean exported exact probability distributions for some shared cases, and a harness compared everything. The commit timestamps show the order: the specification and preregistration first, the simulator five minutes later, the results ten minutes after that.""",
"Results: no failures": """The result: no failures. 243 outcome frequencies matched Lean's exact values, and every applicable prediction passed, some of them over tens of thousands of trials. So the prose and the formalization agree on recognition, learning, retrieval, both backups and carrying. But look at the bottom row: five predictions were vacuous.""",
"Finding 1: five predictions were never tested": """That is the most interesting finding. Those five predictions needed the net to test every feature of a digit. But EPAM grows only one test per confusion, so in no learned net did that ever happen. The theorems are true, and yet they say almost nothing about the nets EPAM actually produces. That's a general lesson for proving things about cognitive models: the hypotheses that make a proof go through can quietly exclude the cases you care about. Without a rule that reports vacuous checks as vacuous, these would have looked like five passes.""",
"Finding 3: a prediction depends on an open choice": """Another finding concerns learning. The model predicts a sequence: a confident error, then column work after feedback, then fluent, correct retrieval. But the model doesn't say what associations a newly discriminated problem starts with; that was one of the open choices we declared. And the sequence depends on it. Starting with no associations, the predicted sequence appears in 40 of 48 cases. Starting with only the correct answer, the column phase is often skipped. Copying the neighbour's associations perpetuates the error. So a substantive question about the theory has become sharp.""",
"The generality problem": """Part five. Everything so far is about one model. But there are a great many models, such as EPAM, ACT-R, SAM, REM, MINERVA and connectionist networks, and formalizing them one at a time doesn't scale. Worse, a pile of formalized models doesn't tell you what any two of them disagree about. And unlike mathematics, none of them is simply true. So the question is how a general library should be organized.""",
"The same problems, two memories": """The first step was to make memory a parameter. Recognition is now an interface: memory takes a probe and returns a probability distribution over stored items. EPAM's net is one memory. ACT-R's declarative memory is another, and in the case of decay one and temperature one we can compute it exactly. Run the same problems through both, and they diverge where you'd hope: with ACT-R, confusion is graded, even a practiced problem sometimes errs, and new practice interferes with old. EPAM rules out all three.""",
"The composition, extracted": """The second step was to notice that the multi-digit trial is one case of a general composition: recognize with any memory, search the recognized item's associations, else back up. We moved that into the shared library, over any problems and any answers, and proved confident errors there, once. Multi-digit addition is now just an instance: one bridge lemma carries every probability across, and all its theorems keep their names.""",
"A second task: naming people": """To show it isn't about arithmetic, here is a second task through the same composition: naming people. Faces are codes; Ann and Bob are familiar; Carl is a stranger who resembles both. With EPAM's memory, the confident-errors theorem is simply inherited: Carl is confidently misnamed Bob, and he says don't know exactly as rarely as Bob himself does. With ACT-R's memory, the misnaming is graded: Carl can be taken for either familiar person, and he says don't know more often than Bob.""",
"Six laws": """Part six. To compare memories in general, we need a vocabulary that doesn't mention any mechanism. These are laws: small properties a memory may or may not have. Certainty: something just studied is retrieved for certain. Stability: studying one thing doesn't change another's retrieval. Order-freedom; recency; stored-only, meaning nothing unstudied is ever retrieved; and determinacy, a single outcome. Predictions are then proved from laws, not from particular models.""",
"Four families": """And instead of individual models, we formalize families of models, each once, with its parameters free. Discrimination nets, like EPAM. Activation memory, like ACT-R's. Strength memory with a criterion, after the associations model. And global matching, MINERVA 2, where every study leaves a trace and a probe returns a blend of all of them. A published model is then a choice of parameters within its family.""",
"The matrix": """Put them together and you get a matrix. Every cell is a theorem: has means a general proof, for every parameter setting that meets stated conditions; lacks means a counterexample. Every law separates some families, and every family has its own row. I'll be candid: some of these laws are stated too narrowly, all-or-none where they should be graded, and fixing that is the next piece of work. But it's the structure I want you to see.""",
"The laws were tested, and failed once": """We also test the laws themselves. The first four were chosen with three families in mind. When we added global matching as a test, it looked exactly like strength memory on all four. So the laws were missing something, and what's distinctive about global matching is that it returns a blend. Study three variants of a pattern, probe with their prototype, and MINERVA returns the prototype, which it never saw. That forced the stored-only law. The rule now is that a law enters the library only with a family on each side.""",
"From laws: which memories give confident errors?": """Here's where the two halves meet. Confident errors can be derived from three laws: any memory with determinacy, certainty and stability produces them, whenever a stranger can be taken for a studied item. So the matrix answers the question of which memory families produce confident errors: only discrimination. And since the evidence suggests people lack certainty, explaining confident errors in people will need a graded version of this theorem.""",
"Reversing the workflow": """Part seven. Laws let us reverse the usual workflow. Instead of choosing an experiment and computing what each model predicts, we start from two laws that disagree, derive a design on which they make incompatible predictions, prove the separation for every memory with either law, and then state the response model that connects it to what participants actually say.""",
"Recency against order-freedom": """Recency and order-freedom disagree. Take two new items, A and B, and a probe equally similar to both. Study A then B, or B then A, and then probe. Delta measures how much more B is favoured after AB than after BA. From the laws alone: order-freedom gives a delta of zero, and recency gives a delta greater than zero, so no memory can have both laws. These proofs never mention EPAM, or ACT-R, or any parameter.""",
"From retrieval to report": """But participants give reports, not retrievals. So we add a response model: forced choice, guessing B with probability gamma when neither item comes to mind. Then the reported effect is delta plus a bias term. Order-freedom still predicts zero, whatever the bias. But recency's prediction survives only if guessing is unbiased, or if neither item is equally likely to come to mind in both orders. The bridge from theory to data comes with its own condition, and the theorem states it.""",
"The same design, four memories": """Here is the same design run with four memories. ACT-R shows recency, ten seventeenths, and that holds for any guessing bias. Strength memory and MINERVA show no effect, as their order-freedom requires. EPAM has neither law, and it surprises us: with one prior item, it shows the most extreme primacy possible. Whichever item was learned first always wins, because of the shape of the net, not anything about time.""",
"A related approach: SFT-GMA": """We're not alone in wanting this. Fisher, Houpt, Larue and Schmidt, in the Journal of Mathematical Psychology this year, derived critical tests of ACT-R from eight core assumptions they propose, using systems factorial technology with global model analysis. They prove that ACT-R can only process two stimuli in the same modality serially, and published experiments show parallel processing, so some core assumption has to go. Like us, they separate core from auxiliary assumptions and give a verdict per class with its theorem. The differences: they constrain processing structure seen in response times, we constrain what memory retrieves and learns; their model space comes with its own paradigm, diagnostics and data, and ours doesn't yet; they analyze one architecture, we compare families; and their proofs are careful prose, ours are machine-checked. They also suggest that base-level activation should be monotone in uses and recency, just the kind of graded law we need next. In the long run, I think executable, machine-checked, and a library that accumulates will win out, but only if it connects to data as well as SFT does, gets its laws right, and earns each theory's community's trust. So I expect convergence: methods like SFT-GMA becoming parts of a library like this one.""",
"What is true here?": """Finally, part eight, and the question I promised. In mathematics, a proved theorem is true. Here we have competing theories, so what is true? There are three kinds of claim. That a law entails a prediction is proved, and permanent. That a family has a law is proved, and permanent. Whether people have a law is empirical, and revisable. Which theory is right follows from the second and third together, and the first two never expire, even if every model in the library is refuted.""",
"Against the evidence": """So the matrix carries a row for people: a judgment, with sources, kept apart from the theorems. Each entry states its bridge, that is, how a measure, which is always a report, is taken to show something about retrieval. For example, endorsing an unseen prototype as old doesn't show you retrieved the prototype; a memory that retrieves a similar studied item would also call it old. As we've judged it, ACT-R fits every settled entry, but those fits are hypotheses until the bridges are formalized.""",
"Where this is weaker than mathematics": """Let me be clear about where this is weaker than mathematics. The definitions are contestable, which is why we do blind checks. The laws are idealizations, and they assume a representation. The families are flexible, so the most informative facts are about regions of their parameters, not single counterexamples. And the evidence is never final. But when it changes, the matrix tells you immediately what has been refuted.""",
"Next": """Next steps: learning across trials, where memory states themselves become random; graded laws, which will also tell us where in its parameters each family has each law; more families as tests, such as REM, a connectionist memory, and ACT-R with blending; decision and report components, so that laws about retrieval predict responses; and beyond memory, to strategy choice and production systems.""",
"Take-home": """So, the take-home. Cognitive theories can be stated so that their consequences are proved, for every parameter setting. The durable content is conditional: laws entail predictions, and families have or lack laws. A matrix of families against laws tells you which experiments are worth running and what a result refutes. And the real value isn't that each theory can be formalized; it's that results about one component can be combined with results about another into predictions that no single model anticipated. Thank you.""",
}


HEAD = r"""\documentclass[aspectratio=169,11pt]{beamer}
\input{preamble}
\input{leancode}

% Generated by gen_story.py from the other five decks; do not edit. Their key
% slides, copied verbatim, in an order that tells the story in one talk.

\title{CogLean, straight through}
\subtitle{Why prove, a theory proved, how, is it faithful, laws, experiments, and what is true}
\author{Jeff Shrager}
\date{October 2026}

\begin{document}

\begin{frame}
  \titlepage
\end{frame}
\note{
TITLE_SCRIPT
}
"""


def grab(fname, title):
    s = open(fname).read()
    m = re.search(r"\\begin\{frame\}(\[fragile\])?\{" + re.escape(title) + r"\}", s)
    assert m, (fname, title)
    j = s.index("\\end{frame}", m.start()) + len("\\end{frame}")
    frame, rest = s[m.start():j], s[j:]
    note = ""
    if rest.lstrip().startswith("\\note{"):
        start = rest.index("\\note{")
        note = rest[start:rest.index("\n}\n", start) + 3]
    return frame, note


out = [HEAD.replace("TITLE_SCRIPT", SCRIPT["TITLE"])]
for fname, title, trans in PICKS:
    frame, _ = grab(fname, title)
    lead = ("\\textbf{" + trans + "}\n\n") if trans else ""
    out.append("\n" + frame + "\n\\note{\n" + lead + SCRIPT[title] + "\n}\n")
out.append("\n\\end{document}\n")
open("coglean-story.tex", "w").write("".join(out))
