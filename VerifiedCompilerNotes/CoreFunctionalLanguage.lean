import VersoManual
import VerifiedCompilerNotes.Meta.Lean
import VerifiedCompilerNotes.References

open Verso.Genre Manual

open Verso.Genre.Manual
open VerifiedCompilerNotes

namespace VerifiedCompilerNotes

#doc (Manual) "A Core Functional Language" =>

# Core Functional Language

This chapter develops the syntax and semantics of a small core functional
language. The language extends the arithmetic fragment from the previous
chapter with booleans, conditionals, pairs, sums, and first-class functions.
The goal is to make the semantic role of environments explicit. Rather than
explaining function application by substitution, we evaluate expressions
relative to an environment that records the meanings of free variables.

The resulting semantics is still big-step, but it now evaluates expressions to
structured values rather than just integers. Function values are closures:
they pair a lambda abstraction with the environment in which it was created.
This makes lexical scope visible in both the mathematical presentation and the
Lean code.

# Primer on Semantic Notation

As in the previous chapter, metavariables range over specific syntactic or
semantic classes. Once we define a grammar for expressions using the
metavariable $`e`, an occurrence of $`e` later in the chapter means an
element of that grammar. Likewise, $`v` ranges over values, $`x` ranges
over variables, and $`ρ` ranges over environments.

The semantic objects in this chapter are defined inductively. This means that
we specify a collection of constructors or inference rules, and then take the
least set closed under those clauses. For expressions, the constructors form
the abstract syntax tree of the language. For the evaluation relation, the
rules specify exactly which judgments count as valid evaluations.

We write the evaluation judgment as $`ρ ⊢ e ⇓ v`. In this chapter,
$`⇓` is a ternary relation between environments, expressions, and values.
Read $`ρ ⊢ e ⇓ v` as saying that expression $`e` evaluates to value $`v`
in environment $`ρ`. Set-theoretically, this means that the triple
$`(ρ, e, v)` belongs to the evaluation relation.

The displayed rule names in this chapter are chosen to match the Lean
constructor names for the corresponding inductive relation whenever that is
practical.

# Syntax

The abstract syntax of expressions is:

$$`
\begin{aligned}
e ::= {} & n \mid b \mid x \mid \mathsf{if}(e, e, e) \\
  \mid {} & \mathsf{pair}(e, e) \mid \mathsf{fst}(e) \mid \mathsf{snd}(e) \\
  \mid {} & \mathsf{inl}(e) \mid \mathsf{inr}(e) \\
  \mid {} & \mathsf{case}(e, x.e, y.e) \\
  \mid {} & \lambda x. e \mid \mathsf{app}(e, e)
\end{aligned}
`

Here $`n` ranges over integers, $`b` ranges over booleans, and $`x`
ranges over variables. The forms $`\mathsf{inl}(e)` and
$`\mathsf{inr}(e)` inject values into the left and right sides of a binary
sum, while $`\mathsf{case}(e, x.e_1, y.e_2)` performs case analysis by
binding the payload of the selected branch.

```savedLean (name := coreFunSyntax)
abbrev Var := String

inductive Expr where
  | int (n : Int)
  | bool (b : Bool)
  | var (x : Var)
  | ite (e₁ e₂ e₃ : Expr)
  | pair (e₁ e₂ : Expr)
  | fst (e : Expr)
  | snd (e : Expr)
  | inl (e : Expr)
  | inr (e : Expr)
  | case
      (e : Expr)
      (x₁ : Var)
      (e₁ : Expr)
      (x₂ : Var)
      (e₂ : Expr)
  | lam (x : Var) (e : Expr)
  | app (e₁ e₂ : Expr)
deriving Repr, DecidableEq
```

The syntax is represented in Lean by an inductive datatype. Variables are
named by strings, which keeps the chapter readable and lines up directly with
the environment-based semantics.

# Values and Environments

To describe evaluation, we also need a semantic domain of values. Integers and
booleans are values directly. Pairs evaluate to pair values, sum injections
evaluate to tagged sum values, and function expressions evaluate to closures.
A closure stores both the code of the function and the environment in which it
was created.

The mathematical presentation is:

$$`
\begin{aligned}
v ::= {} & n \mid b \mid \mathsf{pair}(v, v) \\
  \mid {} & \mathsf{inl}(v) \mid \mathsf{inr}(v) \\
  \mid {} & \langle \lambda x. e, \rho \rangle
\end{aligned}
`

An environment $`ρ` is a finite mapping from variables to values. We write
$`ρ[x \mapsto v]` for the environment obtained by extending $`ρ` with a
binding for $`x`.

```savedLean (name := coreFunValues)
inductive Value where
  | int (n : Int)
  | bool (b : Bool)
  | pair (v₁ v₂ : Value)
  | inl (v : Value)
  | inr (v : Value)
  | closure (x : Var) (e : Expr)
      (ρ : List (Var × Value))
deriving Repr

abbrev Env := List (Var × Value)

def lookupEnv : Env → Var → Option Value
  | [], _ => none
  | (y, v) :: ρ, x =>
      if x = y then some v else lookupEnv ρ x
```

The Lean code uses an association list for environments. This is enough for a
small definitional development, and it keeps the lookup and extension
operations transparent.

# Big-Step Semantics

The semantics evaluates expressions relative to an environment. Constants
evaluate to themselves, variables are looked up in the environment, pairs and
sums evaluate their subexpressions recursively, and functions evaluate to
closures. Application is the key rule: first evaluate the function position to
a closure, then evaluate the argument, and finally evaluate the function body
in the closure's saved environment extended with the parameter binding.

Some representative rules are:

$$`
\begin{gathered}
\textsf{int}\; \dfrac{}{ρ ⊢ n ⇓ n}
\\[0.8em]
\textsf{bool}\; \dfrac{}{ρ ⊢ b ⇓ b}
\\[0.8em]
\textsf{var}\; \dfrac{ρ(x) = v}{ρ ⊢ x ⇓ v}
\\[0.8em]
\textsf{ifT}\;
  \dfrac{ρ ⊢ e_1 ⇓ \mathsf{true} \qquad ρ ⊢ e_2 ⇓ v}
        {ρ ⊢ \mathsf{if}(e_1, e_2, e_3) ⇓ v}
\\[0.8em]
\textsf{ifF}\;
  \dfrac{ρ ⊢ e_1 ⇓ \mathsf{false} \qquad ρ ⊢ e_3 ⇓ v}
        {ρ ⊢ \mathsf{if}(e_1, e_2, e_3) ⇓ v}
\\[0.8em]
\textsf{pair}\;
  \dfrac{ρ ⊢ e_1 ⇓ v_1 \qquad ρ ⊢ e_2 ⇓ v_2}
        {ρ ⊢ \mathsf{pair}(e_1, e_2) ⇓ \mathsf{pair}(v_1, v_2)}
\\[0.8em]
\textsf{fst}\;
  \dfrac{ρ ⊢ e ⇓ \mathsf{pair}(v_1, v_2)}
        {ρ ⊢ \mathsf{fst}(e) ⇓ v_1}
\\[0.8em]
\textsf{snd}\;
  \dfrac{ρ ⊢ e ⇓ \mathsf{pair}(v_1, v_2)}
        {ρ ⊢ \mathsf{snd}(e) ⇓ v_2}
\\[0.8em]
\textsf{inl}\;
  \dfrac{ρ ⊢ e ⇓ v}
        {ρ ⊢ \mathsf{inl}(e) ⇓ \mathsf{inl}(v)}
\\[0.8em]
\textsf{inr}\;
  \dfrac{ρ ⊢ e ⇓ v}
        {ρ ⊢ \mathsf{inr}(e) ⇓ \mathsf{inr}(v)}
\\[0.8em]
\textsf{caseL}\;
  \dfrac{ρ ⊢ e ⇓ \mathsf{inl}(v) \qquad ρ[x_1 \mapsto v] ⊢ e_1 ⇓ w}
        {ρ ⊢ \mathsf{case}(e, x_1.e_1, x_2.e_2) ⇓ w}
\\[0.8em]
\textsf{caseR}\;
  \dfrac{ρ ⊢ e ⇓ \mathsf{inr}(v) \qquad ρ[x_2 \mapsto v] ⊢ e_2 ⇓ w}
        {ρ ⊢ \mathsf{case}(e, x_1.e_1, x_2.e_2) ⇓ w}
\\[0.8em]
\textsf{lam}\;
  \dfrac{}{ρ ⊢ \lambda x. e ⇓ \langle \lambda x. e, ρ \rangle}
\\[0.8em]
\textsf{app}\;
  \dfrac{ρ ⊢ e_1 ⇓ \langle \lambda x. e, ρ' \rangle
         \qquad ρ ⊢ e_2 ⇓ v_2
         \qquad ρ'[x \mapsto v_2] ⊢ e ⇓ v}
        {ρ ⊢ \mathsf{app}(e_1, e_2) ⇓ v}
\end{gathered}
`

The closure rule is the semantic heart of the chapter. A lambda abstraction
does not evaluate by rewriting its body. Instead, it becomes a value that
packages the body together with the current environment. Application later
uses that saved environment, not the caller's environment, and this is what
implements lexical scope.

```savedLean (name := coreFunEval)
inductive Eval : Env → Expr → Value → Prop where
  | int ρ n :
    Eval ρ (.int n) (.int n)
  | bool ρ b :
    Eval ρ (.bool b) (.bool b)
  | var {ρ x v} :
    lookupEnv ρ x = some v →
    Eval ρ (.var x) v
  | ifT {ρ e₁ e₂ e₃ v} :
    Eval ρ e₁ (.bool true) →
    Eval ρ e₂ v →
    Eval ρ (.ite e₁ e₂ e₃) v
  | ifF {ρ e₁ e₂ e₃ v} :
    Eval ρ e₁ (.bool false) →
    Eval ρ e₃ v →
    Eval ρ (.ite e₁ e₂ e₃) v
  | pair {ρ e₁ e₂ v₁ v₂} :
    Eval ρ e₁ v₁ →
    Eval ρ e₂ v₂ →
    Eval ρ (.pair e₁ e₂) (.pair v₁ v₂)
  | fst {ρ e v₁ v₂} :
    Eval ρ e (.pair v₁ v₂) →
    Eval ρ (.fst e) v₁
  | snd {ρ e v₁ v₂} :
    Eval ρ e (.pair v₁ v₂) →
    Eval ρ (.snd e) v₂
  | inl {ρ e v} :
    Eval ρ e v →
    Eval ρ (.inl e) (.inl v)
  | inr {ρ e v} :
    Eval ρ e v →
    Eval ρ (.inr e) (.inr v)
  | caseL {ρ e e₁ e₂ x₁ x₂ v w} :
    Eval ρ e (.inl v) →
    Eval ((x₁, v) :: ρ) e₁ w →
    Eval ρ (.case e x₁ e₁ x₂ e₂) w
  | caseR {ρ e e₁ e₂ x₁ x₂ v w} :
    Eval ρ e (.inr v) →
    Eval ((x₂, v) :: ρ) e₂ w →
    Eval ρ (.case e x₁ e₁ x₂ e₂) w
  | lam ρ x e :
    Eval ρ (.lam x e) (.closure x e ρ)
  | app {ρ ρ' e₁ e₂ e x v₂ v} :
    Eval ρ e₁ (.closure x e ρ') →
    Eval ρ e₂ v₂ →
    Eval ((x, v₂) :: ρ') e v →
    Eval ρ (.app e₁ e₂) v
```

This Lean inductive relation follows the mathematical rules directly. The rule
names line up with the names used in the displayed inference rules.

# An Executable Interpreter

The inductive relation gives the clearest mathematical account of evaluation,
but it is also useful to have an executable interpreter for experiments. The
interpreter below follows the same environment-based structure, returning
$`none` when evaluation gets stuck because a lookup fails or an eliminator is
applied to the wrong kind of value.

```savedLean (name := coreFunInterp)
partial def eval : Env → Expr → Option Value
  | ρ, .int n => some (.int n)
  | ρ, .bool b => some (.bool b)
  | ρ, .var x => lookupEnv ρ x
  | ρ, .ite e₁ e₂ e₃ => do
      match ← eval ρ e₁ with
      | .bool true => eval ρ e₂
      | .bool false => eval ρ e₃
      | _ => none
  | ρ, .pair e₁ e₂ => do
      let v₁ ← eval ρ e₁
      let v₂ ← eval ρ e₂
      pure (.pair v₁ v₂)
  | ρ, .fst e => do
      match ← eval ρ e with
      | .pair v₁ _ => pure v₁
      | _ => none
  | ρ, .snd e => do
      match ← eval ρ e with
      | .pair _ v₂ => pure v₂
      | _ => none
  | ρ, .inl e => do
      let v ← eval ρ e
      pure (.inl v)
  | ρ, .inr e => do
      let v ← eval ρ e
      pure (.inr v)
  | ρ, .case e x₁ e₁ x₂ e₂ => do
      match ← eval ρ e with
      | .inl v => eval ((x₁, v) :: ρ) e₁
      | .inr v => eval ((x₂, v) :: ρ) e₂
      | _ => none
  | ρ, .lam x e => some (.closure x e ρ)
  | ρ, .app e₁ e₂ => do
      match ← eval ρ e₁ with
      | .closure x e ρ' => do
          let v₂ ← eval ρ e₂
          eval ((x, v₂) :: ρ') e
      | _ => none
```

The interesting clause is again function application. Evaluating a lambda does
not substitute into the function body. Instead, it produces a closure. Later,
when that closure is applied, the body is evaluated in the closure's saved
environment extended with the argument value.

# Examples

The following examples illustrate the behavior of the interpreter.

```savedLean (name := coreFunExamples)
#eval
  eval []
    (.ite (.bool true) (.int 7) (.int 9))
#eval
  eval []
    (.fst (.pair (.int 4) (.bool false)))
#eval
  eval []
    (.case
      (.inl (.int 5))
      "x"
      (.var "x")
      "y"
      (.int 0))
```

The next example demonstrates lexical scope. The function closes over the
binding of $`x` present when the lambda is created, not any later binding at
the call site.

```savedLean (name := coreFunClosureExample)
def captureExample : Expr :=
  .app
    (.lam "f" (.app (.var "f") (.int 0)))
    (.lam "y" (.var "x"))

#eval eval [("x", .int 42)] captureExample
```

This example is still small enough to inspect by hand. The outer lambda
receives a function argument, but the argument function itself was created in
an environment where $`x` is already bound to $`42`. When that function is
applied, it therefore returns $`42`.

# Static Semantics

The same language also admits a simple compositional type system. The base
types are integers and booleans. We then close these under products, sums, and
function types.

The grammar of types is:

$$`
\begin{aligned}
\tau ::= {} & \mathsf{int} \mid \mathsf{bool} \\
  \mid {} & \tau \times \tau \\
  \mid {} & \tau + \tau \\
  \mid {} & \tau \to \tau
\end{aligned}
`

A type environment maps variables to types. We write $`\Gamma` for type
environments and read the judgment $`\Gamma \vdash e : \tau` as saying that
expression $`e` has type $`\tau` under the assumptions recorded in
$`\Gamma`.

```savedLean (name := coreFunTypes)
inductive Ty where
  | int
  | bool
  | pair (τ₁ τ₂ : Ty)
  | sum (τ₁ τ₂ : Ty)
  | fn (τ₁ τ₂ : Ty)
deriving Repr, DecidableEq

abbrev TyEnv := List (Var × Ty)

def lookupTyEnv : TyEnv → Var → Option Ty
  | [], _ => none
  | (y, τ) :: Γ, x =>
      if x = y then some τ else lookupTyEnv Γ x
```

The typing rules are syntax-directed:

$$`
\begin{gathered}
\textsf{int}\; \dfrac{}{\Gamma \vdash n : \mathsf{int}}
\\[0.8em]
\textsf{bool}\; \dfrac{}{\Gamma \vdash b : \mathsf{bool}}
\\[0.8em]
\textsf{var}\; \dfrac{\Gamma(x) = \tau}{\Gamma \vdash x : \tau}
\\[0.8em]
\textsf{if}\;
  \dfrac{\Gamma \vdash e_1 : \mathsf{bool}
        \qquad \Gamma \vdash e_2 : \tau
        \qquad \Gamma \vdash e_3 : \tau}
        {\Gamma \vdash \mathsf{if}(e_1, e_2, e_3) : \tau}
\\[0.8em]
\textsf{pair}\;
  \dfrac{\Gamma \vdash e_1 : \tau_1 \qquad \Gamma \vdash e_2 : \tau_2}
        {\Gamma \vdash \mathsf{pair}(e_1, e_2) :
          \tau_1 \times \tau_2}
\\[0.8em]
\textsf{fst}\;
  \dfrac{\Gamma \vdash e : \tau_1 \times \tau_2}
        {\Gamma \vdash \mathsf{fst}(e) : \tau_1}
\\[0.8em]
\textsf{snd}\;
  \dfrac{\Gamma \vdash e : \tau_1 \times \tau_2}
        {\Gamma \vdash \mathsf{snd}(e) : \tau_2}
\\[0.8em]
\textsf{inl}\;
  \dfrac{\Gamma \vdash e : \tau_1}
        {\Gamma \vdash \mathsf{inl}(e) : \tau_1 + \tau_2}
\\[0.8em]
\textsf{inr}\;
  \dfrac{\Gamma \vdash e : \tau_2}
        {\Gamma \vdash \mathsf{inr}(e) : \tau_1 + \tau_2}
\\[0.8em]
\textsf{case}\;
  \dfrac{\Gamma \vdash e : \tau_1 + \tau_2
        \qquad (\Gamma, x_1 : \tau_1) \vdash e_1 : \tau
        \qquad (\Gamma, x_2 : \tau_2) \vdash e_2 : \tau}
        {\Gamma \vdash \mathsf{case}(e, x_1.e_1, x_2.e_2) : \tau}
\\[0.8em]
\textsf{lam}\;
  \dfrac{(\Gamma, x : \tau_1) \vdash e : \tau_2}
        {\Gamma \vdash \lambda x. e : \tau_1 \to \tau_2}
\\[0.8em]
\textsf{app}\;
  \dfrac{\Gamma \vdash e_1 : \tau_1 \to \tau_2
        \qquad \Gamma \vdash e_2 : \tau_1}
        {\Gamma \vdash \mathsf{app}(e_1, e_2) : \tau_2}
\end{gathered}
`

```savedLean (name := coreFunTyping)
inductive HasType : TyEnv → Expr → Ty → Prop where
  | int Γ n :
    HasType Γ (.int n) .int
  | bool Γ b :
    HasType Γ (.bool b) .bool
  | var {Γ x τ} :
    lookupTyEnv Γ x = some τ →
    HasType Γ (.var x) τ
  | ite {Γ e₁ e₂ e₃ τ} :
    HasType Γ e₁ .bool →
    HasType Γ e₂ τ →
    HasType Γ e₃ τ →
    HasType Γ (.ite e₁ e₂ e₃) τ
  | pair {Γ e₁ e₂ τ₁ τ₂} :
    HasType Γ e₁ τ₁ →
    HasType Γ e₂ τ₂ →
    HasType Γ (.pair e₁ e₂) (.pair τ₁ τ₂)
  | fst {Γ e τ₁ τ₂} :
    HasType Γ e (.pair τ₁ τ₂) →
    HasType Γ (.fst e) τ₁
  | snd {Γ e τ₁ τ₂} :
    HasType Γ e (.pair τ₁ τ₂) →
    HasType Γ (.snd e) τ₂
  | inl {Γ e τ₁ τ₂} :
    HasType Γ e τ₁ →
    HasType Γ (.inl e) (.sum τ₁ τ₂)
  | inr {Γ e τ₁ τ₂} :
    HasType Γ e τ₂ →
    HasType Γ (.inr e) (.sum τ₁ τ₂)
  | case {Γ e e₁ e₂ x₁ x₂ τ τ₁ τ₂} :
    HasType Γ e (.sum τ₁ τ₂) →
    HasType ((x₁, τ₁) :: Γ) e₁ τ →
    HasType ((x₂, τ₂) :: Γ) e₂ τ →
    HasType Γ (.case e x₁ e₁ x₂ e₂) τ
  | lam {Γ x e τ₁ τ₂} :
    HasType ((x, τ₁) :: Γ) e τ₂ →
    HasType Γ (.lam x e) (.fn τ₁ τ₂)
  | app {Γ e₁ e₂ τ₁ τ₂} :
    HasType Γ e₁ (.fn τ₁ τ₂) →
    HasType Γ e₂ τ₁ →
    HasType Γ (.app e₁ e₂) τ₂
```

The typing relation is separate from evaluation. The semantic rules explain
how closed programs run, while the typing rules explain which expressions are
well-formed. Together they set up the usual metatheoretic questions of
preservation and progress, but those proofs lie beyond the scope of this
chapter.

# Semantic Typing and Termination

The syntactic typing judgment classifies expressions by shape, but it does not
by itself explain why well-typed programs terminate. A standard next step is
to define a semantic typing relation, or logical relation, that characterizes
terminating programs of each type. This style of argument goes back to
{citet taitIntensionalInterpretations}[] and aligns with more recent
presentations of logical type safety such as
{citet timanyLogicalTypeSoundness}[].

We define this in two layers. First, a value relation $`v \in V\llbracket\tau
\rrbracket` classifies values of type $`\tau`. Then an expression relation
$`e \in E\llbracket\tau\rrbracket` says that evaluating the closed expression
$`e` terminates with a value in the corresponding value relation.

Mathematically, the relation is given by:

$$`
\begin{aligned}
n \in V\llbracket \mathsf{int} \rrbracket
\\[0.8em]
b \in V\llbracket \mathsf{bool} \rrbracket
\\[0.8em]
\mathsf{pair}(v_1, v_2) \in V\llbracket \tau_1 \times \tau_2 \rrbracket
  &\iff v_1 \in V\llbracket \tau_1 \rrbracket
    \land v_2 \in V\llbracket \tau_2 \rrbracket
\\[0.8em]
\mathsf{inl}(v_1) \in V\llbracket \tau_1 + \tau_2 \rrbracket
  &\iff v_1 \in V\llbracket \tau_1 \rrbracket
\\
\mathsf{inr}(v_2) \in V\llbracket \tau_1 + \tau_2 \rrbracket
  &\iff v_2 \in V\llbracket \tau_2 \rrbracket
\\[0.8em]
\langle \lambda x. e, \rho \rangle \in V\llbracket \tau_1 \to \tau_2 \rrbracket
  &\iff
\\
  &\quad \forall v_1 \in V\llbracket \tau_1 \rrbracket,
    \exists v_2 \in V\llbracket \tau_2 \rrbracket,
\\
  &\qquad \rho[x \mapsto v_1] \vdash e \Downarrow v_2
\\[0.8em]
e \in E\llbracket \tau \rrbracket
  &\iff \exists v \in V\llbracket \tau \rrbracket,
    [] \vdash e \Downarrow v
\end{aligned}
`

This is a unary relation on closed expressions, indexed by type. The function
case is what makes it a logical relation rather than just a classification of
run-time shapes: a function value belongs to the relation only if it maps
related arguments to related results.

```savedLean (name := coreFunSemanticTyping)
mutual
  def ValueInTy : Ty → Value → Prop
    | .int, .int _ => True
    | .bool, .bool _ => True
    | .pair τ₁ τ₂, .pair v₁ v₂ =>
        ValueInTy τ₁ v₁ ∧ ValueInTy τ₂ v₂
    | .sum τ₁ τ₂, .inl v =>
        ValueInTy τ₁ v
    | .sum τ₁ τ₂, .inr v =>
        ValueInTy τ₂ v
    | .fn τ₁ τ₂, .closure x e ρ =>
        ∀ v₁,
          ValueInTy τ₁ v₁ →
          ∃ v₂, eval ((x, v₁) :: ρ) e = some v₂ ∧ ValueInTy τ₂ v₂
    | _, _ => False

  def ExprInTy (τ : Ty) (e : Expr) : Prop :=
    ∃ v, eval [] e = some v ∧ ValueInTy τ v
end

theorem fundamental {e : Expr} {τ : Ty} :
    HasType [] e τ → ExprInTy τ e := by
  sorry

theorem typeSoundness {e : Expr} {τ : Ty} :
    HasType [] e τ →
    ∃ v, eval [] e = some v ∧ ValueInTy τ v := by
  intro h
  simpa [ExprInTy] using fundamental h
```

The theorem `fundamental` states that every closed, syntactically well-typed
expression belongs to the semantic typing relation at the same type. Since the
semantic typing relation is defined in terms of terminating evaluation, this
immediately yields type soundness in the form stated by `typeSoundness`.

# Type Inference

The static semantics above is declarative: it says what it means for an
expression to have a type, but it does not yet explain how to compute one. A
standard algorithmic presentation separates inference into two phases. First,
a syntax-directed relation generates a type together with a set of equality
constraints. Second, a unification algorithm either solves those constraints or
fails.

To make this precise, we introduce inference types with type variables:

$$`
\hat{\tau} ::= \mathsf{int}
  \mid \mathsf{bool}
  \mid \hat{\tau} \times \hat{\tau}
  \mid \hat{\tau} + \hat{\tau}
  \mid \hat{\tau} \to \hat{\tau}
  \mid \alpha
`

A constraint is an equation $`\hat{\tau}_1 \doteq \hat{\tau}_2`, and a
substitution $`\sigma` maps type variables to inference types. We write
$`\sigma(\hat{\tau})` for the result of applying a substitution to an
inference type.

Constraint generation uses a judgment of the form
$`\Gamma \vdash e \rightsquigarrow \hat{\tau} \mid C`, read as saying that
expression $`e` generates inferred type $`\hat{\tau}` together with constraint
set $`C` under environment $`\Gamma`. Representative rules are:

$$`
\begin{gathered}
\textsf{int}\; \dfrac{}{\Gamma \vdash n \rightsquigarrow \mathsf{int} \mid \varnothing}
\\[0.8em]
\textsf{bool}\;
  \dfrac{}{\Gamma \vdash b \rightsquigarrow \mathsf{bool} \mid \varnothing}
\\[0.8em]
\textsf{var}\;
  \dfrac{\Gamma(x) = \hat{\tau}}
        {\Gamma \vdash x \rightsquigarrow \hat{\tau} \mid \varnothing}
\\[0.8em]
\textsf{if}\;
  \dfrac{\Gamma \vdash e_1 \rightsquigarrow \hat{\tau}_1 \mid C_1
        \qquad \Gamma \vdash e_2 \rightsquigarrow \hat{\tau}_2 \mid C_2
        \qquad \Gamma \vdash e_3 \rightsquigarrow \hat{\tau}_3 \mid C_3}
        {\Gamma \vdash \mathsf{if}(e_1, e_2, e_3)
          \rightsquigarrow \hat{\tau}_2 \mid
          C_1 \cup C_2 \cup C_3 \cup
          \{\hat{\tau}_1 \doteq \mathsf{bool}, \hat{\tau}_2 \doteq \hat{\tau}_3\}}
\\[0.8em]
\textsf{lam}\;
  \dfrac{(\Gamma, x : \alpha) \vdash e \rightsquigarrow \hat{\tau} \mid C}
        {\Gamma \vdash \lambda x. e \rightsquigarrow \alpha \to \hat{\tau} \mid C}
\\[0.8em]
\textsf{app}\;
  \dfrac{\Gamma \vdash e_1 \rightsquigarrow \hat{\tau}_1 \mid C_1
        \qquad \Gamma \vdash e_2 \rightsquigarrow \hat{\tau}_2 \mid C_2}
        {\Gamma \vdash \mathsf{app}(e_1, e_2) \rightsquigarrow \alpha \mid
          C_1 \cup C_2 \cup \{\hat{\tau}_1 \doteq \hat{\tau}_2 \to \alpha\}}
\end{gathered}
`

The other forms are treated similarly: products, sums, and projections each
generate only equality constraints.

Unification consumes a list of such constraints. It repeatedly decomposes
matching type constructors, binds type variables when the occurs check
succeeds, and fails when the constructors disagree or a variable would be made
equal to a type containing itself.

$$`
\begin{aligned}
\mathsf{unify}(\varnothing)
  &= \mathsf{some}(\mathsf{id})
\\[0.8em]
\mathsf{unify}((\mathsf{int} \doteq \mathsf{int}) :: C)
  &= \mathsf{unify}(C)
\\[0.8em]
\mathsf{unify}((\mathsf{bool} \doteq \mathsf{bool}) :: C)
  &= \mathsf{unify}(C)
\\[0.8em]
\mathsf{unify}((\hat{\tau}_1 \times \hat{\tau}_2
    \doteq \hat{\tau}_1' \times \hat{\tau}_2') :: C)
  &= \mathsf{unify}((\hat{\tau}_1 \doteq \hat{\tau}_1')
      :: (\hat{\tau}_2 \doteq \hat{\tau}_2') :: C)
\\[0.8em]
\mathsf{unify}((\hat{\tau}_1 + \hat{\tau}_2
    \doteq \hat{\tau}_1' + \hat{\tau}_2') :: C)
  &= \mathsf{unify}((\hat{\tau}_1 \doteq \hat{\tau}_1')
      :: (\hat{\tau}_2 \doteq \hat{\tau}_2') :: C)
\\[0.8em]
\mathsf{unify}((\hat{\tau}_1 \to \hat{\tau}_2
    \doteq \hat{\tau}_1' \to \hat{\tau}_2') :: C)
  &= \mathsf{unify}((\hat{\tau}_1 \doteq \hat{\tau}_1')
      :: (\hat{\tau}_2 \doteq \hat{\tau}_2') :: C)
\\[0.8em]
\mathsf{unify}((\alpha \doteq \hat{\tau}) :: C)
  &= \begin{cases}
      \mathsf{fail} & \text{if } \alpha \in \mathsf{fv}(\hat{\tau}) \\
      \sigma \circ [\alpha \mapsto \hat{\tau}]
        & \text{if } \mathsf{unify}([\alpha \mapsto \hat{\tau}](C)) = \sigma
    \end{cases}
\\[0.8em]
\mathsf{unify}((\hat{\tau} \doteq \alpha) :: C)
  &= \mathsf{unify}((\alpha \doteq \hat{\tau}) :: C)
\\[0.8em]
\mathsf{unify}((\hat{\tau}_1 \doteq \hat{\tau}_2) :: C)
  &= \mathsf{fail}
\end{aligned}
`

```savedLean (name := coreFunInference)
abbrev TVar := Nat

inductive InferTy where
  | int
  | bool
  | pair (τ₁ τ₂ : InferTy)
  | sum (τ₁ τ₂ : InferTy)
  | fn (τ₁ τ₂ : InferTy)
  | var (α : TVar)
deriving Repr, DecidableEq

abbrev Constraint := InferTy × InferTy
abbrev Constraints := List Constraint
abbrev Subst := List (TVar × InferTy)
abbrev InferTyEnv := List (Var × InferTy)

def lookupInferTyEnv : InferTyEnv → Var → Option InferTy
  | [], _ => none
  | (y, τ) :: Γ, x =>
      if x = y then some τ else lookupInferTyEnv Γ x

def occurs (α : TVar) : InferTy → Bool
  | .int | .bool => false
  | .pair τ₁ τ₂ | .sum τ₁ τ₂ | .fn τ₁ τ₂ =>
      occurs α τ₁ || occurs α τ₂
  | .var β => α = β

partial def substInferTy (σ : Subst) : InferTy → InferTy
  | .int => .int
  | .bool => .bool
  | .pair τ₁ τ₂ =>
      .pair (substInferTy σ τ₁) (substInferTy σ τ₂)
  | .sum τ₁ τ₂ =>
      .sum (substInferTy σ τ₁) (substInferTy σ τ₂)
  | .fn τ₁ τ₂ =>
      .fn (substInferTy σ τ₁) (substInferTy σ τ₂)
  | .var α =>
      match σ.find? (fun p => p.1 = α) with
      | none => .var α
      | some (_, τ) => substInferTy σ τ

def substConstraint (σ : Subst) : Constraint → Constraint
  | (τ₁, τ₂) => (substInferTy σ τ₁, substInferTy σ τ₂)

def substConstraints (σ : Subst) (C : Constraints) : Constraints :=
  C.map (substConstraint σ)

def composeSubst (σ₁ σ₂ : Subst) : Subst :=
  σ₂.map (fun (α, τ) => (α, substInferTy σ₁ τ)) ++ σ₁

def toTy? : InferTy → Option Ty
  | .int => some .int
  | .bool => some .bool
  | .pair τ₁ τ₂ => do
      let τ₁' ← toTy? τ₁
      let τ₂' ← toTy? τ₂
      pure (.pair τ₁' τ₂')
  | .sum τ₁ τ₂ => do
      let τ₁' ← toTy? τ₁
      let τ₂' ← toTy? τ₂
      pure (.sum τ₁' τ₂')
  | .fn τ₁ τ₂ => do
      let τ₁' ← toTy? τ₁
      let τ₂' ← toTy? τ₂
      pure (.fn τ₁' τ₂')
  | .var _ => none

inductive Generate : InferTyEnv → Expr → InferTy → Constraints → Prop where
  | int Γ n :
    Generate Γ (.int n) .int []
  | bool Γ b :
    Generate Γ (.bool b) .bool []
  | var {Γ x τ} :
    lookupInferTyEnv Γ x = some τ →
    Generate Γ (.var x) τ []
  | ite {Γ e₁ e₂ e₃ τ₁ τ₂ τ₃ C₁ C₂ C₃} :
    Generate Γ e₁ τ₁ C₁ →
    Generate Γ e₂ τ₂ C₂ →
    Generate Γ e₃ τ₃ C₃ →
    Generate Γ (.ite e₁ e₂ e₃) τ₂
      (C₁ ++ C₂ ++ C₃ ++ [(τ₁, .bool), (τ₂, τ₃)])
  | pair {Γ e₁ e₂ τ₁ τ₂ C₁ C₂} :
    Generate Γ e₁ τ₁ C₁ →
    Generate Γ e₂ τ₂ C₂ →
    Generate Γ (.pair e₁ e₂) (.pair τ₁ τ₂) (C₁ ++ C₂)
  | fst {Γ e τ₁ τ₂ C} :
    Generate Γ e (.pair τ₁ τ₂) C →
    Generate Γ (.fst e) τ₁ C
  | snd {Γ e τ₁ τ₂ C} :
    Generate Γ e (.pair τ₁ τ₂) C →
    Generate Γ (.snd e) τ₂ C
  | inl {Γ e τ₁ τ₂ C} :
    Generate Γ e τ₁ C →
    Generate Γ (.inl e) (.sum τ₁ τ₂) C
  | inr {Γ e τ₁ τ₂ C} :
    Generate Γ e τ₂ C →
    Generate Γ (.inr e) (.sum τ₁ τ₂) C
  | case {Γ e e₁ e₂ x₁ x₂ τ τ₁ τ₂ τ₃ C C₁ C₂} :
    Generate Γ e τ C →
    Generate ((x₁, τ₁) :: Γ) e₁ τ₃ C₁ →
    Generate ((x₂, τ₂) :: Γ) e₂ τ₃ C₂ →
    Generate Γ (.case e x₁ e₁ x₂ e₂) τ₃
      (C ++ C₁ ++ C₂ ++ [(τ, .sum τ₁ τ₂)])
  | lam {Γ x e α τ C} :
    Generate ((x, .var α) :: Γ) e τ C →
    Generate Γ (.lam x e) (.fn (.var α) τ) C
  | app {Γ e₁ e₂ α τ₁ τ₂ C₁ C₂} :
    Generate Γ e₁ τ₁ C₁ →
    Generate Γ e₂ τ₂ C₂ →
    Generate Γ (.app e₁ e₂) (.var α)
      (C₁ ++ C₂ ++ [(τ₁, .fn τ₂ (.var α))])

def IsUnifier (σ : Subst) (C : Constraints) : Prop :=
  ∀ {τ₁ τ₂}, (τ₁, τ₂) ∈ C →
    substInferTy σ τ₁ = substInferTy σ τ₂

def MoreGeneral (σ₁ σ₂ : Subst) : Prop :=
  ∃ θ : Subst, ∀ τ, substInferTy σ₂ τ = substInferTy θ (substInferTy σ₁ τ)

def IsMGU (σ : Subst) (C : Constraints) : Prop :=
  IsUnifier σ C ∧ ∀ σ' : Subst, IsUnifier σ' C → MoreGeneral σ σ'

partial def unify : Constraints → Option Subst
  | [] => some []
  | (.int, .int) :: C => unify C
  | (.bool, .bool) :: C => unify C
  | (.pair τ₁ τ₂, .pair τ₁' τ₂') :: C =>
      unify ((τ₁, τ₁') :: (τ₂, τ₂') :: C)
  | (.sum τ₁ τ₂, .sum τ₁' τ₂') :: C =>
      unify ((τ₁, τ₁') :: (τ₂, τ₂') :: C)
  | (.fn τ₁ τ₂, .fn τ₁' τ₂') :: C =>
      unify ((τ₁, τ₁') :: (τ₂, τ₂') :: C)
  | (.var α, .var β) :: C =>
      if α = β then unify C
      else
        let s := [(α, .var β)]
        match unify (substConstraints s C) with
        | some σ => some (composeSubst σ s)
        | none => none
  | (.var α, τ) :: C =>
      if occurs α τ then none
      else
        let s := [(α, τ)]
        match unify (substConstraints s C) with
        | some σ => some (composeSubst σ s)
        | none => none
  | (τ, .var α) :: C =>
      unify ((.var α, τ) :: C)
  | _ => none

def Infers (e : Expr) (τ : Ty) : Prop :=
  ∃ τ' C σ,
    Generate [] e τ' C ∧
    unify C = some σ ∧
    toTy? (substInferTy σ τ') = some τ

theorem unify_sound {C σ} :
    unify C = some σ → IsMGU σ C := by
  sorry

theorem unify_complete {C} :
    (∃ σ, IsUnifier σ C) → ∃ σ, unify C = some σ := by
  sorry

theorem inference_sound {e : Expr} {τ : Ty} :
    Infers e τ → HasType [] e τ := by
  sorry

theorem inference_complete {e : Expr} {τ : Ty} :
    HasType [] e τ → Infers e τ := by
  sorry

theorem inference_typeSafety {e : Expr} {τ : Ty} :
    Infers e τ → ExprInTy τ e := by
  intro h
  exact fundamental (inference_sound h)
```

The theorem `inference_sound` says that a successful inference result can be
read back as a derivation in the declarative typing relation. The converse
theorem `inference_complete` says that every declaratively well-typed closed
term can be obtained from constraint generation followed by successful
unification. Since `fundamental` already connects syntactic typing to semantic
typing, `inference_typeSafety` gives the desired logical type-safety corollary
for successful inference.

end VerifiedCompilerNotes
