/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.
Authors: Wojciech Różowski
-/

import LeroyCompilerVerificationCourse.Sequences

/-
  1. The source language: IMP
    1.1 Arithmetic expressions
-/
def ident := String deriving BEq, Repr, Hashable

/-
  The abstract syntax: an arithmetic expression is either...
-/
inductive aexp : Type where
  | CONST (n : Int)               -- a constant, or
  | VAR (x : ident)               -- a variable, or
  | PLUS (a1 : aexp) (a2 : aexp)  -- a sum of two expressions, or
  | MINUS (a1 : aexp) (s2 : aexp) -- a difference of two expressions

/-
  The denotational semantics: an evaluation function that computes the integer value denoted by an expression.  It is parameterized by a store [s] that associates values to variables.
-/

def store : Type := ident → Int

@[grind] def aeval (s : store) (a : aexp) : Int :=
  match a with
  | .CONST n => n
  | .VAR x => s x
  | .PLUS a1 a2 => aeval s a1 + aeval s a2
  | .MINUS a1 a2 => aeval s a1 - aeval s a2

/-
Such evaluation functions / denotational semantics have many uses. First, we can use [aeval] to evaluate a given expression in a given store.
-/
/-- info: 3 -/
#guard_msgs in
#eval aeval (λ _ => 2) (.PLUS (.VAR "x") (.MINUS (.VAR "x") (.CONST 1)))

/-
  We can prove properties of a given expression.
-/
theorem aeval_xplus1 : ∀ s x, aeval s (.PLUS (.VAR x) (.CONST 1)) > aeval s (.VAR x) := by
  grind

/-
  Finally, we can prove "meta-properties" that hold for all expressions.
  For example: the value of an expression depends only on the values of its free variables.

  Free variables are defined by this recursive predicate:
-/
@[grind] def free_in_aexp (x : ident) (a : aexp) : Prop :=
  match a with
  | .CONST _ => False
  | .VAR y => y = x
  | .PLUS a1 a2
  | .MINUS a1 a2 => free_in_aexp x a1 ∨ free_in_aexp x a2

theorem aeval_free (s1 s2 a) (h : ∀ x, free_in_aexp x a → s1 x = s2 x) :
    aeval s1 a = aeval s2 a := by
  fun_induction aeval s1 a with grind

/-
  1.3 Boolean expressions

  The IMP language has conditional statements (if/then/else) and loops.  They are controlled by expressions that evaluate to Boolean values.  Here is the abstract syntax of Boolean expressions.
-/

inductive bexp : Type where
  | TRUE                              -- always true
  | FALSE                             -- always false
  | EQUAL (a1 : aexp) (a2 : aexp)     -- whether [a1=a]
  | LESSEQUAL (a1 : aexp) (a2 : aexp) -- whether [a1≤a]
  | NOT (b1 : bexp)                   -- Boolean negation
  | AND (b1 : bexp) (b2 : bexp)       -- Boolean conjunction

/-
  There are many useful derived forms.
-/
def NOTEQUAL (a1 a2 : aexp) : bexp := .NOT (.EQUAL a1 a2)

def GREATEREQUAL (a1 a2 : aexp) : bexp := .LESSEQUAL a2 a1

def GREATER (a1 a2 : aexp) : bexp := .NOT (.LESSEQUAL a1 a2)

def LESS (a1 a2 : aexp) : bexp := GREATER a2 a1

@[grind] def OR (b1 b2 : bexp) : bexp := .NOT (.AND (.NOT b1) (.NOT b2))

/-
Just like arithmetic expressions evaluate to integers, Boolean expressions evaluate to Boolean values `true` or `false`.
-/
@[grind] def beval (s : store) (b : bexp) : Bool :=
  match b with
  | .TRUE => true
  | .FALSE => false
  | .EQUAL a1 a2 => aeval s a1 = aeval s a2
  | .LESSEQUAL a1 a2 => aeval s a1 <= aeval s a2
  | .NOT b1 =>  !(beval s b1)
  | .AND b1 b2 => beval s b1 && beval s b2

/-
  We show the expected semantics for the `OR` derived form:
-/
theorem beval_OR : beval s (OR b1 b2) = beval s b1 ∨ beval s b2 := by grind

/-
  1.4 Commands

  To complete the definition of the IMP language, here is the abstract syntax of commands, also known as statements.
-/
inductive com : Type where
  | SKIP                                        -- do nothing
  | ASSIGN (x : ident) (a : aexp)               -- assignment: [v := a]
  | SEQ (c1 : com) (c2 : com)                   -- sequence: [c1; c2]
  | IFTHENELSE (b : bexp) (c1 : com) (c2 : com) -- conditional: [if b then c1 else c2]
  | WHILE (b : bexp) (c1 : com)                 -- loop: [while b do c1 done]

--  We can write `c1 ;; c2` instead of `.SEQ c1 c2`, it is easier on the eyes.
notation:10 l:10 " ;; " r:11 => com.SEQ l r

/-
  Here is an IMP program that performs Euclidean division by repeated subtraction.  At the end of the program, "q" contains the quotient of "a" by "b", and "r" contains the remainder.
  In pseudocode:
    r := a;
    q := 0;
    while b <= r do
      r := r - b;
      q := q + 1
    done

  In abstract syntax:
-/
def Euclidean_division :=
  .ASSIGN "r" (.VAR "a") ;;
  .ASSIGN "q" (.CONST 0) ;;
  .WHILE (.LESSEQUAL (.VAR "b") (.VAR "r"))
    (.ASSIGN "r" (.MINUS (.VAR "r") (.VAR "b")) ;;
     .ASSIGN "q" (.PLUS (.VAR "q") (.CONST 1)))

/-
  A useful operation over stores: `update x v s` is the store that maps `x` to `v` and is equal to `s` for all variables other than `x`.
-/
@[grind] def update (x : ident) (v : Int) (s : store) : store :=
  fun y => if x == y then v else s y

/-
  A naive approach to giving semantics to commands is to write an evaluation function `cexec s c` that runs the command `c` in initial store `s` and returns the final store when `c` terminates.

  def cexec_fail (s: store) (c: com) : store :=
  match c with
  | .SKIP => s
  | .ASSIGN x a => update x (aeval s a) s
  | .SEQ c1 c2 => cexec_fail (cexec_fail s c1) c2
  | .IFTHENELSE b c1 c2 => if beval s b then cexec_fail s c1 else cexec_fail s c2
  | .WHILE b c1 =>
      if beval s b
      then (cexec_fail (cexec_fail s c1) (.WHILE b c1))
      else s

  The definition above is rejected by Lean, and rightly so, because all Lean functions must terminate, yet the `.WHILE` case may not terminate.  Consider for example the infinite loop `.WHILE .TRUE .SKIP`.

  Worse, IMP is Turing-complete, since it has unbounded iteration (`.WHILE`) plus arbitrary-precision integers.  Hence, there is no computable function `cexec s c` that would return `.Some s'` if `c` terminates with store `s'`, and `.none` if `c` does not terminate.

  However, instead of computable functions, we can use a relation `cexec s c s'` that holds iff command `c`, started in state `s`, terminates with state `s'`.  This relation can easily be defined as a Lean inductive predicate:
-/

@[grind] inductive cexec : store → com → store → Prop where
  | cexec_skip :
      cexec s .SKIP s
  | cexec_assign :
      cexec s (.ASSIGN x a) (update x (aeval s a) s)
  | cexec_seq :
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (.SEQ c1 c2) s''
  | cexec_ifthenelse :
      cexec s (if beval s b then c1 else c2) s' ->
      cexec s (.IFTHENELSE b c1 c2) s'
  | cexec_while_done :
      beval s b = false ->
      cexec s (.WHILE b c) s
  | cexec_while_loop :
      beval s b = true -> cexec s c s' -> cexec s' (.WHILE b c) s'' ->
      cexec s (.WHILE b c) s''

attribute [grind] cexec.cexec_skip
attribute [grind <=] cexec.cexec_seq

/-
  This style of semantics is known as natural semantics or big-step operational semantics.  The predicate `cexec s c s'` holds iff there exists a finite derivation of this conclusion, using the axioms and inference rules above.
  The structure of the derivation represents the computations performed by `c` in a tree-like manner.  The finiteness of the derivation guarantees that only terminating
  executions satisfy `cexec`.

  Indeed, `.WHILE .TRUE .SKIP` does not satisfy `cexec`:
-/
theorem cexec_infinite_loop (s : store) : ¬ ∃ s', cexec s (.WHILE .TRUE .SKIP) s' := by
  rintro ⟨s', h₂⟩
  generalize heq : com.WHILE .TRUE .SKIP = c at h₂
  induction h₂ with grind

/-
  Our naive idea of an execution function for commands was not completely off.  We can define an approximation of such a function by bounding a priori the recursion depth, using a `fuel` parameter of type `Nat`.  When the fuel drops to `0`, `.none` is returned, meaning that the final store could not be computed.
-/
@[grind] def cexec_bounded (fuel : Nat) (s : store) (c : com) : Option store :=
  match fuel with
  | .zero => .none
  | .succ fuel' =>
    match c with
    | .SKIP => .some s
    | .ASSIGN x a => .some (update x (aeval s a) s)
    | .SEQ c1 c2 =>
      match cexec_bounded fuel' s c1 with
      | .none => .none
      | .some s' => cexec_bounded fuel' s' c2
    | .IFTHENELSE b c1 c2 =>
      if beval s b then cexec_bounded fuel' s c1 else cexec_bounded fuel' s c2
    | .WHILE b c1 =>
      if beval s b then
        match cexec_bounded fuel' s c1 with
        | .none => .none
        | .some s' => cexec_bounded fuel' s' (.WHILE b c1)
      else
        .some s
/-
  We relate the `cexec` relation with the `cexec_bounded` function by proving the following two lemmas.
-/
theorem cexec_bounded_sound {fuel s c s'} :
    cexec_bounded fuel s c = .some s' → cexec s c s' := by
  induction fuel generalizing s c s' with grind [cases com]

theorem cexec_bounded_complete (s s' : store) (c : com) :
  cexec s c s' →
  ∃ fuel1, ∀ fuel, (fuel ≥ fuel1) → cexec_bounded fuel s c = .some s' := by
    intro h
    induction h
    case cexec_skip =>
      exists 1
      intro fuel' fgt
      induction fgt with grind
    case cexec_assign =>
      exists 1
      intro fuel' fgt
      induction fgt with grind
    case cexec_seq a_ih1 a_ih2 =>
      apply Exists.elim a_ih1
      intro fuel1 a_ih1
      apply Exists.elim a_ih2
      intro fuel2 a_ih2
      exists (fuel1 + fuel2)
      intro fuel' fgt
      have t1 : fuel1 > 0 := by
        specialize a_ih1 0
        grind
      have t2 : fuel2 > 0 := by
        specialize a_ih2 0
        grind
      induction fuel' with grind
    case cexec_ifthenelse s b c1 c2 s' a a_ih =>
      apply Exists.elim a_ih
      intro fuel
      intro a_ih
      exists (fuel + 1)
      unfold cexec_bounded
      grind
    case cexec_while_done =>
      exists 1
      intro fuel fgt
      induction fgt with grind
    case cexec_while_loop a_ih1 a_ih2 =>
      apply Exists.elim a_ih1
      intro fuel1 a_ih1
      apply Exists.elim a_ih2
      intro fuel2 a_ih2
      have t1 : fuel1 > 0 := by
        specialize a_ih1 0
        grind
      have t2 : fuel2 > 0 := by
        specialize a_ih2 0
        grind
      exists (fuel1 + fuel2)
      unfold cexec_bounded
      intro fuel' fgt
      induction fgt with grind

/-
  6. Small-step semantics for IMP
    6.1 Reduction semantics

  In small-step style, the semantics is presented as a one-step reduction relation ` red (c, s) (c', s') `, meaning that the command `c`, executed in initial state `s`, performs one elementary step of computation.  `s'` is the updated state after this step.

  `c'` is the residual command, capturing all the computations that remain to be done.
-/
@[grind] inductive red : com × store → com × store → Prop where
  | red_assign : ∀ x a s,
      red (.ASSIGN x a, s) (.SKIP, update x (aeval s a) s)
  | red_seq_done : ∀ c s,
      red (.SEQ .SKIP c, s) (c, s)
  | red_seq_step : ∀ c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) →
      red (.SEQ c1 c, s1) (.SEQ c2 c, s2)
  | red_ifthenelse : ∀ b c1 c2 s,
      red (.IFTHENELSE b c1 c2, s) ((if beval s b then c1 else c2), s)
  | red_while_done : ∀ b c s,
      beval s b = false →
      red (.WHILE b c, s) (.SKIP, s)
  | red_while_loop : ∀ b c s,
      beval s b = true →
      red (.WHILE b c, s) (.SEQ c (.WHILE b c), s)

/-
  We prove the following "progress" result for non-`SKIP` commands.
-/
theorem red_progress :
  ∀ c s, c = .SKIP ∨ ∃ c', ∃ s', red (c, s) (c', s') := by
    intro c
    induction c
    any_goals grind
    case SEQ c1 c2 c1_ih c2_ih =>
      intro s
      apply Or.intro_right
      apply Or.elim (c1_ih s)
      case h.left => grind
      case h.right =>
        intro h
        apply Exists.elim h
        intro c1' h
        apply Exists.elim h
        intro s' h
        exists .SEQ c1' c2
        exists s'
        grind

def goes_wrong (c : com) (s : store) : Prop := ∃ c', ∃ s', star red (c, s) (c', s') ∧ irred red (c', s') ∧ c' ≠ .SKIP

/-
  Sequences of reductions can go under a sequence context, generalizing rule `.red_seq_step`.
-/
@[grind] theorem red_seq_steps (c2 c c' : com) (s s' : store) : star red (c, s) (c', s') → star red ((c;;c2), s) ((c';;c2), s') := by
  intro H
  generalize h₁ : (c, s) = v₁
  generalize h₂ : (c', s') = v₂
  rw [h₁, h₂] at H
  induction H generalizing c s
  case star_refl =>
    grind
  case star_step x y _ a₁ a₂ a_ih =>
    apply star.star_step
    · apply red.red_seq_step (c2 := y.1)  (s2 := y.2)
      grind
    · grind

/-
  We now recall the equivalence result between
  - termination according to the big-step semantics
  - existence of a finite sequence of reductions to `SKIP` according to the small-step semantics.

  We start with the implication big-step ==> small-step, which is a straightforward induction on the big-step evaluation derivation.
-/
theorem cexec_to_reds (s s' : store) (c : com) : cexec s c s' → star red (c, s) (.SKIP, s') := by
  intro h
  induction h
  any_goals grind
  case cexec_seq ih1 ih2  =>
    apply star_trans
    · apply red_seq_steps
      exact ih1
    · apply star.star_step
      apply red.red_seq_done
      grind
  case cexec_while_loop ih1 ih2 =>
    apply star_trans
    · apply star_one
      · apply red.red_while_loop
        · grind
    · apply star_trans
      · apply red_seq_steps
        · exact ih1
      · apply star_trans
        rotate_left
        · apply ih2
        · grind

/-
  The reverse implication, from small-step to big-step, is more subtle. The key lemma is the following, showing that one step of reduction followed by a big-step evaluation to a final state can be collapsed into a single big-step evaluation to that final state.
-/
@[grind] theorem red_append_cexec (c1 c2 : com) (s1 s2 : store) (h : red (c1, s1) (c2, s2)) (h₂ : cexec s2 c2 s) :
    cexec s1 c1 s := by
  generalize heq1 : (c1, s1) = h1 at h
  generalize heq2 : (c2, s2) = h2 at h
  induction h generalizing c1 c2 s with grind

/-
  As a consequence, a term that reduces to `SKIP` evaluates in big-step with the same final state.
-/
theorem reds_to_cexec (s s' : store) (c : com) (h : star red (c, s) (.SKIP, s')) :
    cexec s c s' := by
  generalize heq1 : (c, s) = h1 at h
  generalize heq2 : (com.SKIP, s') = h2 at h
  induction h generalizing s c s' with grind

/-
  6.2 Transition semantics with continuations

  We now introduce an alternate form of small-step semantics where the command to be executed is explicitly decomposed into:
  - a sub-command under focus, where computation takes place;
  - a continuation (or context) describing the position of this sub-command
  in the whole command, or, equivalently, describing the parts of the whole command that remain to be reduced once the sub-command is done.

  As a consequence, the small-step semantics is presented as a transition relation betwee triples (subcommand-under-focus, continuation, state).  Previously, we had transition between pairs (whole-command, state).

  The syntax of continuations is as follows:
-/
@[grind] inductive cont where
| Kstop
| Kseq (c : com) (k : cont)
| Kwhile (b : bexp) (c : com) (k : cont)

/-
  Intuitive meaning of these constructors:
  - `.Kstop` means that, after the sub-command under focus terminates, nothing remains to be done, and execution can stop.  In other words, the sub-command under focus is the whole command.
  - `.Kseq c k` means that, after the sub-command terminates, we still need to execute command `c` in sequence, then continue as described by `k`.
  - `.Kwhile b c k` means that, after the sub-command terminates, we still need to execute a loop [WHILE b DO c END], then continue as described by `k`.

  Another way to forge intuitions about continuations is to ponder the following `apply_cont k c` function, which takes a sub-command `c` under focus and a continuation `k`, and rebuilds the whole command.  It simply puts `c` in lefmost position in a nest of sequences as described by `k`.
-/
@[grind] def apply_cont (k : cont) (c : com) : com :=
  match k with
  | .Kstop => c
  | .Kseq c1 k1 => apply_cont k1 (.SEQ c c1)
  | .Kwhile b1 c1 k1 => apply_cont k1 (.SEQ c (.WHILE b1 c1))

/-
  Transitions between (subcommand-under-focus, continuation, state) triples perform conceptually different kinds of actions:
  - Computation: evaluate an arithmetic expression or boolean expression and modify the triple according to the result of the evaluation.
  - Focusing: replace the sub-command by a sub-sub-command that is to be evaluated next, possibly enriching the continuation as a consequence.
  - Resumption: when the sub-command is `.SKIP` and therefore fully executed, look at the head of the continuation to see what to do next.

  Here are the transition rules, classified by the kinds of actions they implement.
-/
inductive step : com × cont × store -> com × cont × store -> Prop where
  | step_assign : ∀ x a k s,
      step (.ASSIGN x a, k, s) (.SKIP, k, update x (aeval s a) s)
    -- computation for assignments
  | step_seq : ∀ c1 c2 s k,
      step (.SEQ c1 c2, k, s) (c1, .Kseq c2 k, s)
      -- focusing for sequence
  | step_ifthenelse : ∀ b c1 c2 k s,
      step (.IFTHENELSE b c1 c2, k, s) ((if beval s b then c1 else c2), k, s)
      -- computation for conditionals
  | step_while_done : ∀ b c k s,
      beval s b = false ->
      step (.WHILE b c, k, s) (.SKIP, k, s)
      -- computation for loops
  | step_while_true : ∀ b c k s,
      beval s b = true ->
      step (.WHILE b c, k, s) (c, .Kwhile b c k, s)
      -- computation and focusing for loops
  | step_skip_seq : ∀ c k s,
      step (.SKIP, .Kseq c k, s) (c, k, s)
      -- resumption
  | step_skip_while : ∀ b c k s,
      step (.SKIP, .Kwhile b c k, s) (.WHILE b c, k, s)
      -- resumption
