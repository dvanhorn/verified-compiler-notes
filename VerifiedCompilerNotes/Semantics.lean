import VersoManual
import VerifiedCompilerNotes.Meta.Lean
import VerifiedCompilerNotes.References

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open VerifiedCompilerNotes


#doc (Manual) "Basics of Operational Semantics" =>

%%%
tag := "chap-semantics"
%%%

{index}[semantics]

# Overview

A programming language is a way of describing computations. Defining a
programming language consists of defining at least two things:

- Syntax
- Semantics

The syntax of a language defines the rules for constructing phrases of
the language. These rules are often expressed grammatically using BNF
notation. From a mathematical point of view, the syntax defines a set:
the set of programs in the language. Syntax is inert:
it simply captures the marks we make to write down program text.

The semantics of a language defines the meaning of programs by assigning
computational behavior to syntactically well-formed programs.

There are many different ways of defining the semantics of a programming
language. In these notes, we focus on operational semantics. An
operational semantics defines the meaning of programs by describing the
actions carried out when a program is run.

Even within operational semantics, there are several different styles.
We will look at several:

- Interpreter semantics
- Natural (big-step) semantics
- Reduction (small-step, or SOS) semantics
- Abstract machine semantics

## What is operational semantics useful for?

There are many reasons to define an operational semantics.

*Specifying a programming language.* You might be building a
programming language and want to provide a formal specification. There
are many widely used languages with formal semantics. WebAssembly is a
prominent example with a
[formal specification](https://webassembly.github.io/spec/core/)
including an operational semantics. Having an operational semantics
helps remove ambiguity about what programs mean. It gives implementers
of engines, validators, and compilers a precise target to test against.
It fosters interoperability, supports the design of extensions, and
provides a basis for tools such as program analyzers, symbolic
execution engines, and model checkers.

Specifying a large industrial language like WebAssembly is a major
undertaking. It can involve standards bodies and years of work by large
teams of experts. But even when designing a small toy language or a
research prototype, it is useful to start with an operational
semantics. Specification-driven development is good engineering
practice.

While standardization is one important use of operational semantics, a
more common use for the working PL researcher is to communicate
research ideas.

*Communicating a research idea.* In the programming-languages
literature, operational semantics are often used to present language
designs concisely. They provide a compact way of conveying the essence
of an idea to other experts. To really understand what a PL research
paper is saying requires learning the notations and conventions the
community uses for presenting formal semantics. If you want to
communicate your own ideas to other experts, you need to learn to read
and write in this style.

If you open a paper from one of the main [SIGPLAN](https://www.sigplan.org/)
venues such as
[POPL](https://www.sigplan.org/Conferences/POPL/),
[PLDI](https://www.sigplan.org/Conferences/PLDI/),
[ICFP](https://www.sigplan.org/Conferences/ICFP/), or
[OOPSLA](https://www.sigplan.org/Conferences/OOPSLA/),
chances are you will see a formal definition of a programming language
including its syntax and semantics. Often the semantics is given for a
core calculus rather than the full surface language, so that only the
essential ideas are included. Unlike the WebAssembly specification,
which aims to cover a full practical language, the semantics in
research papers usually distills a language to its essentials so that
the main ideas come across clearly.

If you have never looked at a PL paper, it is worth browsing the
proceedings of a recent PL conference
just to get a feel for the style. Derek Dreyer, a prominent PL
researcher and author of highly readable papers, has a recommended talk
called
[_How to Write Papers So People Can Read Them_](https://www.youtube.com/watch?v=KfEVdMMY1aQ).
In it, he describes a paper structure that is common in the PL
literature, along with the rough size of the audience for each part:

- Abstract (1-2 paragraphs, 1000 readers)
- Introduction (1-2 pages, 100 readers)
- Main ideas (2-3 pages, 50 readers)
- Technical meat (4-6 pages, 5 readers)
- Related work (1-2 pages, 100 readers)

The "technical meat" is where you will usually find the operational
semantics. Despite being the least read section, it is where the actual
details of an idea are nailed down. If you want to really internalize a
paper's contribution, you need to be one of those five readers.

*Validating claims about languages.* Beyond communicating an idea,
semantics can also be used to validate precise claims about that idea.
Perhaps we have a new language design and want to claim that it has
some desirable property.

*Proving correctness of algorithms.* PL papers often propose not only
new language designs, but also tools and algorithms that operate on
programs. When that happens, an operational semantics can be used to
state and validate correctness claims. For example, suppose we wrote a
compiler from Standard ML to WebAssembly. Both languages have formal
semantics. Proving the compiler correct means showing that the meaning
of every Standard ML source program is preserved by the generated
WebAssembly program.

Proofs are one of the main forms of evidence valued by the PL
community, so papers often include proofs of formal claims. In
practice, those proofs are often moved to appendices and read by even
fewer people than the technical core of the paper.



This chapter develops a tiny arithmetic language and several related semantic
formulations. We start with an interpreter, then build up big-step and
small-step operational models, then show how context machinery and an abstract
machine make control and evaluation order explicit.

# Primer on Semantic Notation


Operational-semantics presentations use a small amount of mathematical
shorthand. This chapter follows standard programming-languages notation, so it
is worth fixing the reading conventions up front.

First, metavariables range over specific sets. When we write a grammar such as:

$$`
e ::= n \mid succ(e) \mid pred(e) \mid plus(e_1, e_2) \mid times(e_1, e_2)
`

the metavariable $`e` thereafter means an element of the inductively defined
set generated by that grammar. Likewise, $`n` ranges over integers, $`K`
ranges over contexts when contexts are introduced, and so on. The letter is not
just a placeholder for an arbitrary mathematical object; it is constrained by
the grammar or judgment where it is declared.

Second, grammars and relations presented this way are inductively defined sets.
The grammar above should be read as giving the least set of expressions closed
under the displayed constructors:

$$`
\begin{gathered}
\text{if } n \in \mathbb{Z}, \text{ then } n \in Expr \\
\text{if } e \in Expr, \text{ then } succ(e) \in Expr \text{ and } pred(e) \in Expr \\
\text{if } e_1, e_2 \in Expr, \text{ then }
  plus(e_1, e_2) \in Expr \text{ and } times(e_1, e_2) \in Expr
\end{gathered}
`

The same idea applies to evaluation relations. For example, a big-step judgment
$`e \Downarrow n` is defined by the displayed rules: an instance of the
judgment holds exactly when it can be derived from those rules.

It is also useful to be explicit about what relation notation means. A symbol
such as $`\Downarrow` denotes a binary relation, here relating expressions to
integers. Writing the judgment infix as $`e \Downarrow n` means exactly that the
pair $`(e, n)` belongs to the relation $`\Downarrow`. In more explicit set-theoretic
language, if we regard $`\Downarrow \subseteq Expr \times Int`, then
$`e \Downarrow n` means $`(e, n) \in \Downarrow`. The infix notation is simply
more readable than constantly writing ordered pairs and set membership.

Finally, inference rules describe how new judgments may be concluded from old
ones. A rule of the form

$$`
\frac{J_1 \qquad \cdots \qquad J_k}{J}
`

is a stylized presentation of an implication: it says that if the premises
$`J_1, \ldots, J_k` hold, then the conclusion $`J` holds. In other words, it
can be read as the formula

$$`
(J_1 \land \cdots \land J_k) \implies J
`

When operational semantics is presented with many such rules, the intent is
that the relation is the least one closed under those implications. A rule with
no premises,

$$`
\frac{\ }{J}
`

is an axiom: it says that $`J` holds directly. Reading rules this way lets us
move smoothly between the mathematical presentation of semantics and the
corresponding inductive definitions in Lean.

Taken together, the rules form a proof system for the judgments they define. To
show that a particular judgment belongs to the inductively defined relation, one
must build a finite derivation tree whose nodes are judgments, whose children
justify their parent according to one of the inference rules, and whose root is
the judgment of interest. For example, to show that a specific big-step
judgment holds, one would construct a tree ending in that judgment and work
backwards by choosing rules whose premises reduce the problem to simpler
judgments. A judgment belongs to the relation exactly when such a derivation
exists. When a rule is displayed with a name such as $`plusInt` or $`timesLeft`,
that name is simply a label for referring to the rule in prose or in a
derivation; in this chapter, those labels are chosen to match the corresponding
Lean constructor names.

# Syntax

In the notation of a programming-languages paper, the grammar is:

$$`
e ::= n \mid succ(e) \mid pred(e) \mid plus(e_1, e_2) \mid times(e_1, e_2)
`

```lean
inductive Expr where
  | int : Int → Expr
  | succ : Expr → Expr
  | pred : Expr → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
```

# Interpreter Semantics

We can write the interpreter as a total meta-level function:

$$`
\llbracket e \rrbracket : Expr \to Int
`

with defining equations:

$$`
\begin{aligned}
\llbracket n \rrbracket &= n \\
\llbracket succ(e) \rrbracket &= \llbracket e \rrbracket + 1 \\
\llbracket pred(e) \rrbracket &= \llbracket e \rrbracket - 1 \\
\llbracket plus(e_1, e_2) \rrbracket
  &= \llbracket e_1 \rrbracket + \llbracket e_2 \rrbracket \\
\llbracket times(e_1, e_2) \rrbracket
  &= \llbracket e_1 \rrbracket * \llbracket e_2 \rrbracket
\end{aligned}
`

The interpreter is a direct recursive function from terms to integers.

```lean
def interp : Expr → Int
  | .int n => n
  | .succ e => interp e + 1
  | .pred e => interp e - 1
  | .plus e₁ e₂ => interp e₁ + interp e₂
  | .times e₁ e₂ => interp e₁ * interp e₂
```

```lean
#eval interp (.plus (.times (.int 3) (.int 4)) (.int 2))
#eval interp (.succ (.pred (.int 5)))
#eval
  interp (.times (.plus (.int 2) (.int 3)) (.int 4))
```

# Big-Step Evaluation Relation

For big-step semantics we use a judgment of the form:

$$`
e \Downarrow n
`

with rules:

$$`
\begin{gathered}
\textsf{int}\; \dfrac{\ }{n \Downarrow n}
\qquad
\textsf{succ}\; \dfrac{e \Downarrow n}{succ(e) \Downarrow n + 1}
\qquad
\textsf{pred}\; \dfrac{e \Downarrow n}{pred(e) \Downarrow n - 1}
\\[1em]
\textsf{plus}\;
  \dfrac{e_1 \Downarrow n_1 \qquad e_2 \Downarrow n_2}
        {plus(e_1, e_2) \Downarrow n_1 + n_2}
\qquad
\textsf{times}\;
  \dfrac{e_1 \Downarrow n_1 \qquad e_2 \Downarrow n_2}
        {times(e_1, e_2) \Downarrow n_1 * n_2}
\end{gathered}
`

```lean
inductive Eval : Expr → Int → Prop where
  | int (n : Int) : Eval (.int n) n
  | succ {e : Expr} {n : Int} : Eval e n →
    Eval (.succ e) (n + 1)
  | pred {e : Expr} {n : Int} : Eval e n →
    Eval (.pred e) (n - 1)
  | plus {e₁ e₂ : Expr} {n₁ n₂ : Int} : Eval e₁ n₁ →
    Eval e₂ n₂ →
    Eval (.plus e₁ e₂) (n₁ + n₂)
  | times {e₁ e₂ : Expr} {n₁ n₂ : Int} : Eval e₁ n₁ →
    Eval e₂ n₂ →
    Eval (.times e₁ e₂) (n₁ * n₂)
```

# Small-Step Operational Semantics with Congruence Rules

For small-step semantics we write:

$$`
e \to e'
`

The computation rules include:

$$`
\begin{gathered}
\textsf{succInt}\; \dfrac{}{succ(n) \to n + 1}
\qquad
\textsf{predInt}\; \dfrac{}{pred(n) \to n - 1}
\\[1em]
\textsf{plusInt}\; \dfrac{}{plus(n_1, n_2) \to n_1 + n_2}
\qquad
\textsf{timesInt}\; \dfrac{}{times(n_1, n_2) \to n_1 * n_2}
\\[1em]
\textsf{succCong}\; \dfrac{e \to e'}{succ(e) \to succ(e')}
\qquad
\textsf{predCong}\; \dfrac{e \to e'}{pred(e) \to pred(e')}
\\[1em]
\textsf{plusLeftCong}\;
  \dfrac{e_1 \to e_1'}{plus(e_1, e_2) \to plus(e_1', e_2)}
\qquad
\textsf{plusRightCong}\;
  \dfrac{e_2 \to e_2'}{plus(n, e_2) \to plus(n, e_2')}
\\[1em]
\textsf{timesLeftCong}\;
  \dfrac{e_1 \to e_1'}{times(e_1, e_2) \to times(e_1', e_2)}
\qquad
\textsf{timesRightCong}\;
  \dfrac{e_2 \to e_2'}{times(n, e_2) \to times(n, e_2')}
\end{gathered}
`

```lean
inductive Step : Expr → Expr → Prop where
  | succInt (n : Int) :
    Step (.succ (.int n)) (.int (n + 1))
  | predInt (n : Int) :
    Step (.pred (.int n)) (.int (n - 1))
  | plusInt (n₁ n₂ : Int) :
    Step (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | timesInt (n₁ n₂ : Int) :
    Step (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))
  | succCong {e e'} : Step e e' →
    Step (.succ e) (.succ e')
  | predCong {e e'} : Step e e' →
    Step (.pred e) (.pred e')
  | plusLeftCong {e₁ e₂ e₁'} : Step e₁ e₁' →
    Step (.plus e₁ e₂) (.plus e₁' e₂)
  | plusRightCong {n e₂ e₂'} : Step e₂ e₂' →
    Step (.plus (.int n) e₂) (.plus (.int n) e₂')
  | timesLeftCong {e₁ e₂ e₁'} : Step e₁ e₁' →
    Step (.times e₁ e₂) (.times e₁' e₂)
  | timesRightCong {n e₂ e₂'} : Step e₂ e₂' →
    Step (.times (.int n) e₂) (.times (.int n) e₂')
```

```lean
inductive StepStar : Expr → Expr → Prop where
  | refl (e : Expr) : StepStar e e
  | trans {e₁ e₂ e₃ : Expr} : Step e₁ e₂ →
    StepStar e₂ e₃ → StepStar e₁ e₃
```

# Context-Based Semantics: Core Axioms + Context Closure

An alternative presentation factors the relation into core redex rules:

$$`
\begin{gathered}
e \to_0 e'
\\[1em]
\textsf{lift}\; \dfrac{e \to_0 e'}{K[e] \to K[e']}
\\[1em]
K ::= \square \mid succ(K) \mid pred(K) \mid plus(K, e) \mid plus(n, K)
      \mid times(K, e) \mid times(n, K)
\end{gathered}
`

```lean
inductive CoreStep : Expr → Expr → Prop where
  | succInt (n : Int) :
    CoreStep (.succ (.int n)) (.int (n + 1))
  | predInt (n : Int) :
    CoreStep (.pred (.int n)) (.int (n - 1))
  | plusInt (n₁ n₂ : Int) :
    CoreStep (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | timesInt (n₁ n₂ : Int) :
    CoreStep (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))

inductive Ctx where
  | hole
  | succC : Ctx → Ctx
  | predC : Ctx → Ctx
  | plusC₁ : Ctx → Expr → Ctx
  | plusC₂ : Int → Ctx → Ctx
  | timesC₁ : Ctx → Expr → Ctx
  | timesC₂ : Int → Ctx → Ctx

def plug : Ctx → Expr → Expr
  | .hole, e => e
  | .succC K, e => .succ (plug K e)
  | .predC K, e => .pred (plug K e)
  | .plusC₁ K e₂, e => .plus (plug K e) e₂
  | .plusC₂ n K, e => .plus (.int n) (plug K e)
  | .timesC₁ K e₂, e => .times (plug K e) e₂
  | .timesC₂ n K, e => .times (.int n) (plug K e)

inductive CtxStep : Expr → Expr → Prop where
  | lift {K : Ctx} {e₁ e₂} : CoreStep e₁ e₂ →
    CtxStep (plug K e₁) (plug K e₂)
```

# Small-Step Operational Semantics with Left-to-Right Evaluation Order

To enforce a fixed evaluation order, we refine the step relation so that
addition and multiplication evaluate their left operand before their right:

$$`
\begin{gathered}
\textsf{plusLeft}\;
  \dfrac{e_1 \to e_1'}{plus(e_1, e_2) \to plus(e_1', e_2)}
\qquad
\textsf{plusRight}\;
  \dfrac{e_2 \to e_2'}{plus(n, e_2) \to plus(n, e_2')}
\\[1em]
\textsf{timesLeft}\;
  \dfrac{e_1 \to e_1'}{times(e_1, e_2) \to times(e_1', e_2)}
\qquad
\textsf{timesRight}\;
  \dfrac{e_2 \to e_2'}{times(n, e_2) \to times(n, e_2')}
\end{gathered}
`

The arithmetic redex rules retain the same constructor names as before:

$$`
\begin{gathered}
\textsf{succInt}\; \dfrac{}{succ(n) \to n + 1}
\qquad
\textsf{predInt}\; \dfrac{}{pred(n) \to n - 1}
\qquad
\textsf{plusInt}\; \dfrac{}{plus(n_1, n_2) \to n_1 + n_2}
\\[1em]
\textsf{timesInt}\; \dfrac{}{times(n_1, n_2) \to n_1 * n_2}
\end{gathered}
`

and similarly for multiplication, with the same arithmetic redex rules for
fully evaluated operands.

```lean
inductive StepLR : Expr → Expr → Prop where
  | succInt (n : Int) :
    StepLR (.succ (.int n)) (.int (n + 1))
  | predInt (n : Int) :
    StepLR (.pred (.int n)) (.int (n - 1))
  | plusLeft (e₁ e₂ e₁') : StepLR e₁ e₁' →
    StepLR (.plus e₁ e₂) (.plus e₁' e₂)
  | plusRight {n : Int} {e₂ e₂'} : StepLR e₂ e₂' →
    StepLR (.plus (.int n) e₂) (.plus (.int n) e₂')
  | timesLeft (e₁ e₂ e₁') : StepLR e₁ e₁' →
    StepLR (.times e₁ e₂) (.times e₁' e₂)
  | timesRight {n : Int} {e₂ e₂'} : StepLR e₂ e₂' →
    StepLR (.times (.int n) e₂) (.times (.int n) e₂')
  | plusInt (n₁ n₂ : Int) :
    StepLR (.plus (.int n₁) (.int n₂)) (.int (n₁ + n₂))
  | timesInt (n₁ n₂ : Int) :
    StepLR (.times (.int n₁) (.int n₂)) (.int (n₁ * n₂))
```

# Evaluation Contexts that Enforce Left-to-Right Order

The same left-to-right strategy can be described with a restricted class of
evaluation contexts:

$$`
\begin{gathered}
K ::= \square \mid succ(K) \mid pred(K) \mid plus(K, e) \mid plus(n, K)
      \mid times(K, e) \mid times(n, K)
\end{gathered}
`

where the intended reading is now specifically as left-to-right evaluation
contexts rather than arbitrary congruence contexts.

```lean
inductive ECtx where
  | hole
  | succE : ECtx → ECtx
  | predE : ECtx → ECtx
  | plusE₁ : ECtx → Expr → ECtx
  | plusE₂ : Int → ECtx → ECtx
  | timesE₁ : ECtx → Expr → ECtx
  | timesE₂ : Int → ECtx → ECtx

def fill : ECtx → Expr → Expr
  | .hole, e => e
  | .succE K, e => .succ (fill K e)
  | .predE K, e => .pred (fill K e)
  | .plusE₁ K e₂, e => .plus (fill K e) e₂
  | .plusE₂ n K, e => .plus (.int n) (fill K e)
  | .timesE₁ K e₂, e => .times (fill K e) e₂
  | .timesE₂ n K, e => .times (.int n) (fill K e)

inductive EStep : Expr → Expr → Prop where
  | viaCore {K : ECtx} {e₁ e₂} : CoreStep e₁ e₂ →
    EStep (fill K e₁) (fill K e₂)
```

# Abstract Machine Semantics

The abstract machine uses states of the form $`\langle e, k \rangle`, where
$`e` is the current control expression and $`k` is a stack of frames.

$$`
\begin{gathered}
f ::= succF \mid predF \mid plusF_1(e) \mid plusF_2(n)
      \mid timesF_1(e) \mid timesF_2(n)
\\[1em]
\langle e, k \rangle \mapsto \langle e', k' \rangle
\\[1em]
\begin{aligned}
\textsf{pushSucc}\quad
  \langle succ(e), k \rangle
  &\mapsto \langle e, succF :: k \rangle \\
\textsf{pushPred}\quad
  \langle pred(e), k \rangle
  &\mapsto \langle e, predF :: k \rangle \\
\textsf{pushPlusLeft}\quad
  \langle plus(e_1, e_2), k \rangle
  &\mapsto \langle e_1, plusF_1(e_2) :: k \rangle \\
\textsf{pushTimesLeft}\quad
  \langle times(e_1, e_2), k \rangle
  &\mapsto \langle e_1, timesF_1(e_2) :: k \rangle \\
\textsf{popSucc}\quad
  \langle n, succF :: k \rangle
  &\mapsto \langle n + 1, k \rangle \\
\textsf{popPred}\quad
  \langle n, predF :: k \rangle
  &\mapsto \langle n - 1, k \rangle \\
\textsf{popPlusLeft}\quad
  \langle n_1, plusF_1(e_2) :: k \rangle
  &\mapsto \langle e_2, plusF_2(n_1) :: k \rangle \\
\textsf{popPlusRight}\quad
  \langle n_2, plusF_2(n_1) :: k \rangle
  &\mapsto \langle n_1 + n_2, k \rangle \\
\textsf{popTimesLeft}\quad
  \langle n_1, timesF_1(e_2) :: k \rangle
  &\mapsto \langle e_2, timesF_2(n_1) :: k \rangle \\
\textsf{popTimesRight}\quad
  \langle n_2, timesF_2(n_1) :: k \rangle
  &\mapsto \langle n_1 * n_2, k \rangle
\end{aligned}
\end{gathered}
`

```lean
inductive Frame where
  | succF
  | predF
  | plusF₁ : Expr → Frame
  | plusF₂ : Int → Frame
  | timesF₁ : Expr → Frame
  | timesF₂ : Int → Frame

abbrev FrameStack := List Frame
abbrev MachineState := Expr × FrameStack
inductive MachineStep : MachineState → MachineState → Prop
  where
  -- descend into the redex to evaluate the next subterm
  | pushSucc (e : Expr) (k : FrameStack) :
    MachineStep (.succ e, k) (e, .succF :: k)
  | pushPred (e : Expr) (k : FrameStack) :
    MachineStep (.pred e, k) (e, .predF :: k)
  | pushPlusLeft (e₁ e₂ : Expr) (k : FrameStack) :
    MachineStep (.plus e₁ e₂, k)
    (e₁, .plusF₁ e₂ :: k)
  | pushTimesLeft (e₁ e₂ : Expr) (k : FrameStack) :
    MachineStep (.times e₁ e₂, k)
    (e₁, .timesF₁ e₂ :: k)
  -- return to continuation frames
  | popSucc (n : Int) (k : FrameStack) :
    MachineStep (.int n, .succF :: k) (.int (n + 1), k)
  | popPred (n : Int) (k : FrameStack) :
    MachineStep (.int n, .predF :: k) (.int (n - 1), k)
  | popPlusLeft (n₁ : Int) (e₂ : Expr) (k : FrameStack) :
    MachineStep (.int n₁, .plusF₁ e₂ :: k)
    (e₂, .plusF₂ n₁ :: k)
  | popPlusRight (n₁ n₂ : Int) (k : FrameStack) :
    MachineStep
      (.int n₂, .plusF₂ n₁ :: k)
      (.int (n₁ + n₂), k)
  | popTimesLeft (n₁ : Int) (e₂ : Expr) (k : FrameStack) :
    MachineStep (.int n₁, .timesF₁ e₂ :: k)
    (e₂, .timesF₂ n₁ :: k)
  | popTimesRight (n₁ n₂ : Int) (k : FrameStack) :
    MachineStep
      (.int n₂, .timesF₂ n₁ :: k)
      (.int (n₁ * n₂), k)
```

# Abstract Machine Interpreter

The interpreter induced by the machine can be presented mathematically as a
total function:

$$`
\begin{gathered}
run(\langle e, k \rangle) : Int
\\[1em]
run(\langle n, \cdot \rangle) = n
\\[1em]
s \mapsto s' \implies run(s) = run(s')
\\[1em]
\mu(\langle e, k \rangle)
\end{gathered}
`

This counts both the current expression and the pending work stored in frames.

```sharedLean (snippet := "machineMeasureDefs")
def exprMeasure : Expr → Nat
  | .int _ => 1
  | .succ e => exprMeasure e + 2
  | .pred e => exprMeasure e + 2
  | .plus e₁ e₂ => exprMeasure e₁ + exprMeasure e₂ + 3
  | .times e₁ e₂ => exprMeasure e₁ + exprMeasure e₂ + 3

def frameMeasure : Frame → Nat
  | .succF => 1
  | .predF => 1
  | .plusF₁ e => exprMeasure e + 2
  | .plusF₂ _ => 1
  | .timesF₁ e => exprMeasure e + 2
  | .timesF₂ _ => 1

def stackMeasure : FrameStack → Nat
  | [] => 0
  | f :: k => frameMeasure f + stackMeasure k

def machineMeasure : MachineState → Nat
  | (e, k) => exprMeasure e + stackMeasure k
```

```lean
-- Deterministic one-step transition on machine states.
def machineStep : MachineState → Option MachineState
  | (.succ e, k) => some (e, .succF :: k)
  | (.pred e, k) => some (e, .predF :: k)
  | (.plus e₁ e₂, k) => some (e₁, .plusF₁ e₂ :: k)
  | (.times e₁ e₂, k) => some (e₁, .timesF₁ e₂ :: k)
  | (.int n, .succF :: k) => some (.int (n + 1), k)
  | (.int n, .predF :: k) => some (.int (n - 1), k)
  | (.int n₁, .plusF₁ e₂ :: k) =>
    some (e₂, .plusF₂ n₁ :: k)
  | (.int n₂, .plusF₂ n₁ :: k) =>
    some (.int (n₁ + n₂), k)
  | (.int n₁, .timesF₁ e₂ :: k) =>
    some (e₂, .timesF₂ n₁ :: k)
  | (.int n₂, .timesF₂ n₁ :: k) =>
    some (.int (n₁ * n₂), k)
  | _ => none

-- The measure decreases because stack frames
-- record pending work.
def runMachine : MachineState → Int
  | (.succ e, k) => runMachine (e, .succF :: k)
  | (.pred e, k) => runMachine (e, .predF :: k)
  | (.plus e₁ e₂, k) => runMachine (e₁, .plusF₁ e₂ :: k)
  | (.times e₁ e₂, k) => runMachine (e₁, .timesF₁ e₂ :: k)
  | (.int n, .succF :: k) => runMachine (.int (n + 1), k)
  | (.int n, .predF :: k) => runMachine (.int (n - 1), k)
  | (.int n₁, .plusF₁ e₂ :: k) =>
    runMachine (e₂, .plusF₂ n₁ :: k)
  | (.int n₂, .plusF₂ n₁ :: k) =>
    runMachine (.int (n₁ + n₂), k)
  | (.int n₁, .timesF₁ e₂ :: k) =>
    runMachine (e₂, .timesF₂ n₁ :: k)
  | (.int n₂, .timesF₂ n₁ :: k) =>
    runMachine (.int (n₁ * n₂), k)
  | (.int n, []) => n
termination_by s => machineMeasure s
decreasing_by
  all_goals
    simp [
      machineMeasure,
      stackMeasure,
      frameMeasure,
      exprMeasure
    ]
    try omega

-- Public interpreter API over expressions
def interpMachine (e : Expr) : Int :=
  runMachine (e, [])
```

```lean
#eval
  interpMachine (.plus (.times (.int 3) (.int 4)) (.int 2))
#eval interpMachine (.succ (.pred (.int 5)))
#eval
  interpMachine (.times (.plus (.int 2) (.int 3)) (.int 4))
```

The recursive definition of `runMachine` is total, but Lean needs a
well-founded measure that decreases across each machine transition. The key
observation is that pending computation lives partly in the current expression
and partly in the frame stack, so the measure has to account for both.

```replayLean (snippet := "machineMeasureDefs")
```

# Historical Notes

The styles of operational semantics surveyed in this chapter come from several
different threads in the history of programming-language semantics.

Plotkin's retrospective {citet plotkinOriginsSOS}[] points in particular to
three pieces of background that matter for the later rule-based tradition.
McCarthy's work introduced *abstract syntax* as a central semantic tool
{citet mccarthyMathematicalScience}[]; Smullyan's work on formal systems gave a
clear and flexible inference-rule notation {citet smullyanFirstOrderLogic}[];
and Barendregt's thesis showed how reduction relations for the λ-calculus could
be presented elegantly by rules rather than by more cumbersome definitions
{citet barendregtThesis}[]. These ingredients are visible in much later
operational-semantics practice.

*Interpreter semantics.* The most direct ancestor of the interpreter-style
presentation is the tradition of *definitional interpreters*: defining a
language by writing an interpreter for it in some meta-language. A standard
reference is {citet reynoldsDefinitionalInterpreters}[].

*Natural semantics.* Big-step operational semantics is closely associated with
the work {citet kahnNaturalSemantics}[], which popularized this style under
the name "natural semantics." The basic idea is to define evaluation directly
as a relation between phrases and their final results.

*Structural operational semantics.* Small-step SOS is most closely associated
with {citet plotkinSOS}[]. Plotkin's treatment made inference-rule
presentations of one-step reduction a central method for defining programming
languages, and it strongly shaped later PL practice.

*Reduction semantics.* A closely related later presentation is *reduction
semantics*, in which one separates basic redex-contraction rules from a grammar
of evaluation contexts and then defines reduction by plugging a redex into an
allowed context. This style is strongly associated with {citet felleisenHiebRevisedReport}[].
For a modern tutorial treatment that pairs well
with these notes, see also {citet huttonSemantics123}[].

*Abstract machines.* Abstract machine semantics has older roots. A foundational
example is {citet landinMechanicalEvaluation}[], which introduced the SECD
machine. Plotkin later identified abstract machines such as SECD, together
with the Vienna school's abstract interpreting machines, as important
influences on the development of SOS; see {citet plotkinOriginsSOS}[].

These styles are not competitors so much as complementary views of the same
phenomenon. An interpreter emphasizes direct execution, natural semantics
emphasizes whole-program evaluation, SOS emphasizes individual computation
steps, and abstract machines make control state explicit.
