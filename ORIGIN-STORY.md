# How CogLean began

*Jeff Shrager, November 2026*

CogLean started as a side effect of a hobby, and it took me a while to see that the hobby and the
side effect were the same thing.

## Executable archaeology

For the past few years my pastime has been reanimating early AI programs: getting the original
code to run again, as close to the original as possible, usually on a stack of emulators. I call
it *executable archaeology*. The project that got the most attention was ELIZA. I found
Weizenbaum's original code in his archives at MIT, and a small team brought it back: Rupert
Lane, who knows early operating systems; Anthony Hay, who knows ELIZA's algorithm in detail; Art
Schwarz, who knows SLIP, the list-processing package ELIZA was written in; and David Berry, who
brought Rupert in. Together they got *the* ELIZA, not *an* ELIZA, running on an emulated IBM 7094
under MIT's CTSS. For an old computer scientist and hacker it was about the coolest thing I could
imagine. (Team ELIZA's story is told elsewhere, in *Inventing ELIZA* from MIT Press.)

When ELIZA was done I turned to the programs of my own teachers. I was Herb Simon's student at
Carnegie Mellon, and I sat in on Allen Newell's and John Anderson's research groups, and Bob
Siegler's as well. All of that turns out to matter here. But Newell and Simon's programs weren't
just personal history. They were the first AI programs, and the first cognitive models, and the
very first of them was the Logic Theorist. Working with David Moews, I got LT running again in
2025: Stefferud's 1963 IPL-V version runs unmodified and reproduces its published proofs, and the
1956 IPL-I version has been reconstructed as well.

From there I worked forward through the IPL-V models of Newell, Simon and their students. This got
easier quickly. My IPL-V machinery was mature, and the AI coding tools were improving month by
month, until by early 2026 I could hand Claude a found listing and it would make it run. I was
heading for GPS, and digging through the CMU archives for a complete copy. On the way I picked up
EPAM, Feigenbaum and Simon's theory of verbal learning. I had the code; I just hadn't reanimated
it yet.

## What I was really interested in

Under all of this sat the interest I took from Simon: scientific reasoning, and in particular how
scientists reason about their theories. Part of why I went to Anderson's and Newell's group
meetings, honestly, was less their theories of cognition (though those too) than watching how the
groups *thought*. How did they reason about a cognitive model? At CMU the answer went with the
computational theory of mind, and above all with the idea that you validate a theory of cognition
by writing a program that behaves the way people do. I had come to psychology from computer
science, with AI projects for my undergraduate and master's theses at Penn, believing that
understanding cognition would help us build better AI. CMU was where that line between AI and
psychology was thinnest, and it was where I wanted to be.

## Pete, Chris, and an epoophany

Peter Pirolli was my office mate for all of graduate school, and a member of Anderson's ACT group,
which I tagged along to. Decades later, at the Florida Institute for Human and Machine Cognition,
Pete and his colleague Chris Bates were thinking about how to model some aspect of science, and
Pete, knowing my interests, brought me in. Through the late summer of 2026 we talked now and then
about modeling the cognition of science, a problem I've been chewing on since my time with Simon.

Then mathematics changed. Large language models working in Lean, a functional programming language
with a proof checker built in, were announced as having produced proofs of long-open problems
(OpenAI's announcement was on October 6, 2026). I've been calling it the *mathpocalypse*. Whether
you think it saved mathematics or wrecked it, there was no ignoring it.

On October 18 I sent Pete and Chris an email with the subject line "Epoophany." (An *epoophany* is
a word of mine: a brilliant idea that arrives in a flash, which I share with respected colleagues,
and which I recognize as stupid the moment I've sent it. An epiphany that goes *poof*.) The idea
was a Lean-like language for theories of cognition, starting with memory: a way to state memory
mechanisms, learning processes, representations and retrieval precisely enough that their
consequences could be checked. I was careful to separate two things. A proof establishes what
follows from a theory, not whether the theory is true of people. The empirical side, the
experiments, stays where it was. But we could take historical papers, formalize them, and test
them against their own results. And EPAM, a historically important executable theory sitting on my
bench, was the obvious place to start. I ended: "Okay, tell me I'm insane."

Pete didn't. His reply named the stakes better than I had. There is a strong push, he wrote, to
turn cognitive psychology into a black box: people are collections of response functions,
transformers are function approximators, so just predict every response in every experiment, past,
present and future. A formal library of theories "might get us back to theory and explanations."

The next day Chris asked whether I had any specific ideas for how this would work. I sent him a
link: the first EPAM-in-Lean, in my Executable Archaeology repository. It is, as far as I know,
the first time a cognitive model was rendered in Lean.

## The loop

Notice what had happened. The model I chose was EPAM because EPAM was the program I was
reanimating that week. And the program I had reanimated just before it was the Logic Theorist,
which proved theorems from *Principia Mathematica*.

Newell and Simon weren't trying to build AI. They wanted to use programs to state and test
theories of thought, and AI was, in a sense, a side effect. Their first such theory was a theory of
how people prove theorems, and it was itself a prover. What they couldn't do was turn proof on
the theories themselves: in 1956 there was no such thing as reasoning mechanically about a
program. They were inventing mechanical reasoning, in that very code, at that very moment. Seventy
years later, sitting with LT running again on one side and the mathpocalypse on the other, it
seemed obvious to do the next thing: not only run the models, but prove what they entail.

So that is what I did, more or less the way the mathematicians had: I gave the problem to an AI
working in Lean. EPAM went remarkably well. Next I wanted a well-specified model I knew from the
inside, which meant my own with Bob Siegler, the 1984 strategy-choice model of children's
addition, and formalizing it turned up a claim of ours that needs a condition we never stated. The
library grew from there, into what is now CogLean, with CogLib as its shared core.

## Afterward

What happened next is in the repository. Theories were composed into a model of multi-digit
addition; the textbook account of Collins and Quillian was proved unable ever to show typicality;
memory theories were laid out in a matrix of laws, each cell a theorem. John Laird, working
independently, built a Lean replica of ACT-R 7 that matches the Lisp implementation trace for
trace. The circle of people became the authors of the perspective in `papers/2026-perspective/`:
John Laird, John Anderson, Christian Lebiere, Paul Rosenbloom, Andrea Stocco, Peter Lindes, and
Pete and Chris, who were there for the epoophany.

The question that brought me to CMU, how scientists reason about cognitive models, turned out to
have a new answer: they can now reason about them formally, with a machine checking every step.
