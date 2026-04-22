/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Van Horn
-/

import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "Modeling Semantics and a Correctness Theorem" =>

%%%
tag := "chap-semantics"
%%%

{index}[semantics]
This chapter defines a tiny expression language, a stack-machine target, and a
compiler from expressions to machine instructions.

# Abstract Syntax and Denotation

```lean
inductive Expr where
  | num : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
```

```lean
inductive Instr
  | push : Nat → Instr
  | add : Instr
  | mul : Instr
```

```lean
def eval : Expr → Nat
  | .num n => n
  | .add e₁ e₂ => eval e₁ + eval e₂
  | .mul e₁ e₂ => eval e₁ * eval e₂


def compile : Expr → List Instr
  | .num n => [.push n]
  | .add e₁ e₂ => compile e₁ ++ compile e₂ ++ [.add]
  | .mul e₁ e₂ => compile e₁ ++ compile e₂ ++ [.mul]
```

# Stack Machine Semantics

```lean
def step : Instr → List Nat → Option (List Nat)
  | .push n, s => some (n :: s)
  | .add, b :: a :: s => some ((a + b) :: s)
  | .mul, b :: a :: s => some ((a * b) :: s)
  | _, _ => none


def exec : List Instr → List Nat → Option (List Nat)
  | [], s => some s
  | i :: is, s => do
    let s' ← step i s
    exec is s'


def run : List Instr → Option Nat
  | is => do
    let s ← exec is []
    match s with
    | [n] => some n
    | _ => none


def runExpr : Expr → Option Nat
  | e => run (compile e)
```

# A Correctness Statement

```lean
@[simp] theorem exec_append (is₁ is₂ : List Instr) (s : List Nat) :
    exec (is₁ ++ is₂) s = Option.bind (exec is₁ s) (fun s' => exec is₂ s') := by
  induction is₁ generalizing s with
  | nil =>
    simp [exec]
  | cons i is ih =>
    simp [exec, ih, Option.bind_assoc]

theorem execCompile : ∀ e s, exec (compile e) s = some (eval e :: s)
  | .num n, s => by
      simp [compile, exec, step, eval]
  | .add e₁ e₂, s => by
      have h₁ : exec (compile e₁) s = some (eval e₁ :: s) := execCompile e₁ s
      have h₂ : exec (compile e₂) (eval e₁ :: s) = some (eval e₂ :: eval e₁ :: s) :=
        execCompile e₂ (eval e₁ :: s)
      have hEval : eval (Expr.add e₁ e₂) = eval e₁ + eval e₂ := rfl
      simpa [compile, exec_append, h₁, h₂, exec, step, hEval]
  | .mul e₁ e₂, s => by
      have h₁ : exec (compile e₁) s = some (eval e₁ :: s) := execCompile e₁ s
      have h₂ : exec (compile e₂) (eval e₁ :: s) = some (eval e₂ :: eval e₁ :: s) :=
        execCompile e₂ (eval e₁ :: s)
      have hEval : eval (Expr.mul e₁ e₂) = eval e₁ * eval e₂ := rfl
      simpa [compile, exec_append, h₁, h₂, exec, step, hEval]

theorem runExpr_eq_eval : ∀ e, run (compile e) = some (eval e)
  | e => by
    simpa [run, execCompile]
```

```lean
#eval eval (.add (.mul (.num 3) (.num 4)) (.num 2))
```

```lean
#eval run (compile (.add (.mul (.num 3) (.num 4)) (.num 2)))
```
