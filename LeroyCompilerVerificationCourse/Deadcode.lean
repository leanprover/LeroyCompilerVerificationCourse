/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under LGPL 2.1 license as described in the file LICENSE.md.
Authors: Wojciech Różowski
-/

import LeroyCompilerVerificationCourse.Imp
import Std.Data.HashSet

/-
  10.  Liveness analysis and dead code elimination
-/
abbrev IdentSet := Std.HashSet ident

instance : HasSubset IdentSet where
  Subset (a b : IdentSet) := ∀ x ∈ a, x ∈ b

noncomputable instance (a b : IdentSet) : Decidable (a ⊆ b) := Classical.propDecidable (a ⊆ b)

instance : EmptyCollection IdentSet where
  emptyCollection := Std.HashSet.emptyWithCapacity

@[grind =] theorem subset_def (a b : IdentSet) : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := Iff.rfl

@[grind] axiom union_characterisation (a b : IdentSet) (x : ident) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b

@[grind] theorem union_characterisation2 (a b c : IdentSet) : a ⊆ b ∧ a ⊆ c → a ⊆ (b ∪ c) := by
  intro ⟨m1, m2⟩
  intro y
  specialize m1 y
  grind

@[grind] theorem insert_characterisation (a : IdentSet) (x : ident) : x ∈ a.insert x := by
  grind

/-
  10.1 Liveness analysis

  Computation of the set of variables appearing in an expression or command.
-/
@[grind] def fv_aexp (a : aexp) : IdentSet :=
  match a with
  | .CONST _ => ∅
  | .VAR v => Std.HashSet.instSingleton.singleton v
  | .PLUS a1 a2 =>  (fv_aexp a1) ∪ (fv_aexp a2)
  | .MINUS a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)

@[grind] def fv_bexp (b : bexp) : IdentSet :=
  match b with
  | .TRUE => ∅
  | .FALSE => ∅
  | .EQUAL a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)
  | .LESSEQUAL a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)
  | .NOT b1 => fv_bexp b1
  | .AND b1 b2 => (fv_bexp b1) ∪ (fv_bexp b2)

@[grind] def fv_com (c : com) : IdentSet :=
  match c with
  | .SKIP => ∅
  | .ASSIGN _ a => fv_aexp a
  | .SEQ c1 c2 => (fv_com c1) ∪ (fv_com c2)
  | .IFTHENELSE b c1 c2 => (fv_bexp b) ∪ ((fv_com c1) ∪ (fv_com c2))
  | .WHILE b c => (fv_bexp b) ∪ (fv_com c)

/-
  To analyze loops, we will need, again!, to compute post-fixpoints
  of a function from sets of variables to sets of variables.
  We reuse the ``engineer's approach'' from file `Constprop.lean`.
-/
@[grind] noncomputable def deadcode_fixpoint_rec (F : IdentSet → IdentSet) (default : IdentSet) (fuel : Nat) (x : IdentSet) : IdentSet :=
  match fuel with
  | 0 => default
  | fuel + 1 =>
      let x' := F x
      if x' ⊆ x then x else deadcode_fixpoint_rec F default fuel x'

@[grind] noncomputable def deadcode_fixpoint (F : IdentSet → IdentSet) (default : IdentSet) : IdentSet :=
  deadcode_fixpoint_rec F default 20 ∅

@[grind] theorem  fixpoint_charact' (n : Nat) (x : IdentSet)  (F : IdentSet → IdentSet) (default : IdentSet) :
  ((F (deadcode_fixpoint_rec F default n x)) ⊆ (deadcode_fixpoint_rec F default n x)) ∨ (deadcode_fixpoint_rec F default n x = default) := by
    induction n generalizing x with grind

theorem fixpoint_charact (F : IdentSet → IdentSet) (default : IdentSet) :
    ((F (deadcode_fixpoint F default)) ⊆ (deadcode_fixpoint F default)) ∨ (deadcode_fixpoint F default = default) := by grind

@[grind]
theorem fixpoint_upper_bound (F : IdentSet → IdentSet) (default : IdentSet) (F_stable : ∀ x , x ⊆ default -> (F x) ⊆ default) : deadcode_fixpoint F default ⊆ default := by
  have : ∀ n : Nat, ∀ x : IdentSet, x ⊆ default → (deadcode_fixpoint_rec F default n x) ⊆ default := by
    intro n
    induction n with grind
  grind

/-
  Liveness analysis.

  `L` is the set of variables live "after" command `c`.
  The result of `live c L` is the set of variables live "before" `c`.
-/
@[grind] noncomputable def live (c : com) (L : IdentSet) : IdentSet :=
  match c with
  | .SKIP => L
  | .ASSIGN x a =>
      if x ∈ L
      then (L.erase x) ∪ (fv_aexp a)
      else L
  | .SEQ c1 c2 =>
      live c1 (live c2 L)
  | .IFTHENELSE b c1 c2 =>
       (fv_bexp b) ∪ ((live c1 L) ∪ (live c2 L))
  | .WHILE b c =>
      let L' := (fv_bexp b) ∪  L
      let default := (fv_com (.WHILE b c)) ∪ L
      deadcode_fixpoint (fun x => L' ∪ (live c x)) default

@[grind]
theorem live_upper_bound :
  ∀ c L,
   (live c L) ⊆ ((fv_com c) ∪ L) := by
    intro c
    induction c with grind

theorem live_while_charact (b : bexp) (c : com) (L L' : IdentSet)
  (eq : L' = live (.WHILE b c) L) :
  (fv_bexp b) ⊆ L' ∧ L ⊆ L' ∧ (live c L') ⊆ L' := by grind

/-
  10.2 The optimization: dead code elimination

  Dead code elimination turns assignments `.ASSIGN x a` to dead variables `x`
  into `.SKIP` statements.
-/
@[grind] noncomputable def dce (c : com) (L : IdentSet) : com :=
  match c with
  | .SKIP => .SKIP
  | .ASSIGN x a => if x ∈ L then .ASSIGN x a else .SKIP
  | .SEQ c1 c2 => .SEQ (dce c1 (live c2 L)) (dce c2 L)
  | .IFTHENELSE b c1 c2 => .IFTHENELSE b (dce c1 L) (dce c2 L)
  | .WHILE b c => .WHILE b (dce c (live (.WHILE b c) L))

/-
  10.3  Correctness of the optimization

  Two stores agree on a set `L` of live variables if they assign
  the same values to each live variable.
-/
@[grind] def agree (L : IdentSet) (s1 s2 : store) : Prop :=
  ∀ x, x  ∈ L -> s1 x = s2 x

/-
  Monotonicity property.
-/
@[grind] theorem agree_mon :
  ∀ L L' s1 s2,
  agree L' s1 s2 -> L ⊆ L' -> agree L s1 s2 := by grind

/-
  Agreement on the free variables of an expression implies that this
  expression evaluates identically in both stores.
-/
@[grind] theorem aeval_agree :
  ∀ L s1 s2, agree L s1 s2 ->
  ∀ a, (fv_aexp a) ⊆ L -> aeval s1 a = aeval s2 a := by
    intro L s1 s2 AG a
    induction a
    any_goals grind
    case VAR x =>
      simp [fv_aexp]
      grind

theorem beval_agree :
  ∀ L s1 s2, agree L s1 s2 ->
  ∀ b, (fv_bexp b) ⊆ L -> beval s1 b = beval s2 b := by
    intro L s1 s2 AG b
    induction b with grind

/-
  Agreement is preserved by simultaneous assignment to a live variable.
-/
theorem agree_update_live :
  ∀ s1 s2 L x v,
  agree (L.erase x) s1 s2 ->
  agree L (update x v s1) (update x v s2) := by grind

/-
  Agreement is also preserved by unilateral assignment to a dead variable.
-/
theorem agree_update_dead :
  ∀ s1 s2 L x v,
  agree L s1 s2 -> ¬x ∈ L ->
  agree L (update x v s1) s2 := by grind

/-
  We now show that dead code elimination preserves semantics for terminating
  source program.  We use big-step semantics to show the following diagram:

                agree (live c L) s s1
     c / s ----------------------------- dce C L / s1
       |                                          |
       |                                          |
       |                                          |
       v                                          v
      s' -------------------------------------- s1'ß
                    agree L s' s1'

  The proof is a simple induction on the big-step evaluation derivation on the left.
-/
theorem dce_correct_terminating :
  ∀ s c s', cexec s c s' ->
  ∀ L s1, agree (live c L) s s1 ->
  ∃ s1', cexec s1 (dce c L) s1' /\ agree L s' s1' := by
    intro s c s' EXEC
    induction EXEC
    any_goals grind
    case cexec_while_loop s1 b c1 s2 s3 isTrue EX1 EX2 a_ih a_ih2 =>
      intro L s4 hyp
      have ⟨t1, ht1, ht2⟩ :=  a_ih (live (.WHILE b c1) L) s4 (by grind)
      have ⟨u1, hu1, hu2⟩ :=  a_ih2 L t1 ht2
      exists u1
      constructor
      rotate_right
      · exact hu2
      · apply cexec.cexec_while_loop
        · have := beval_agree (live (com.WHILE b c1) L) s1 s4
          grind
        · exact ht1
        · grind
    case cexec_assign s2 x a=>
      intro L s3 AG
      simp [live] at AG
      by_cases x ∈ L
      case neg notIn =>
        exists s3
        grind
      case pos isIn =>
        exists (update x (aeval s3 a) s3)
        grind
    case cexec_ifthenelse s2 b c1 c2 s3 EXEC ih =>
      intro L s4 AG
      simp [dce]
      have EQ : beval s2 b = beval s4 b := by
        apply beval_agree
        · apply AG
        · grind
      by_cases beval s2 b = true
      case pos isTrue =>
        specialize ih L s4
        grind
      case neg isFalse =>
        specialize ih L s4
        grind
    case cexec_while_done s2 b c isFalse =>
      intro L s1 AG
      have ⟨h1, h2, h3⟩ := live_while_charact b c L (live (com.WHILE b c) L) (by grind)
      have EQ : beval s2 b = beval s1 b := by
        apply beval_agree
        · apply AG
        · grind
      exists s1
      grind
    case cexec_seq => grind [-subset_def] -- TODO: what does wrong?
