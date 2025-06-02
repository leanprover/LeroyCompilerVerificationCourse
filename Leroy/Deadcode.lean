import «Leroy».Sequences
import «Leroy».Imp
import Init.Data.List.Basic
import Std.Data.HashSet
import Std.Data.HashSet.Lemmas
open Classical in
-- From Coq Require Import Arith ZArith Psatz Bool String List FSets Program.Equality.
-- Require Import Sequences IMP Constprop.

-- Local Open Scope string_scope.
-- Local Open Scope Z_scope.
-- Local Open Scope list_scope.

-- (** * 10.  Liveness analysis and dead code elimination *)

-- Module IdentSet := FSetWeakList.Make(Ident_Decidable).
-- Module ISFact := FSetFacts.WFacts(IdentSet).
-- Module ISProp := FSetProperties.WProperties(IdentSet).
-- Module ISDecide := FSetDecide.Decide(IdentSet).
-- Import ISDecide.

@[grind] def IdentSet := Std.HashSet ident
  deriving Membership, Union, EmptyCollection
-- (** ** 10.1 Liveness analysis *)

-- (** Computation of the set of variables appearing in an expression or command. *)


@[grind] instance : HasSubset IdentSet where
  Subset (a b : IdentSet) := ∀ x ∈ a, x ∈ b

@[grind] noncomputable instance (a b : IdentSet) : Decidable (a ⊆ b) := Classical.propDecidable (a ⊆ b)

@[grind] noncomputable instance (x : ident) (a: IdentSet) : Decidable (x ∈ a) := Classical.propDecidable (x ∈ a)

@[grind] instance : EmptyCollection IdentSet where
  emptyCollection := Std.HashSet.emptyWithCapacity

@[grind] theorem union_characterisation (a b : IdentSet) (x : ident) : x ∈ (a ∪ b) ↔ x ∈ a ∨ x ∈ b := by
  sorry

@[grind] theorem union_characterisation2 (a b c : IdentSet) : a ⊆ (b ∪ c) ↔ a ⊆ b ∨ a ⊆ c  := by
  sorry

@[grind] theorem insert_characterisation (a : IdentSet) (x : ident) : x ∈ a.insert x := by sorry

@[grind] def fv_aexp (a: aexp) : IdentSet :=
  match a with
  | .CONST _ => ∅
  | .VAR v => Std.HashSet.instSingleton.singleton v
  | .PLUS a1 a2 =>  (fv_aexp a1) ∪ (fv_aexp a2)
  | .MINUS a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)

@[grind] def fv_bexp (b: bexp) : IdentSet :=
  match b with
  | .TRUE => ∅
  | .FALSE => ∅
  | .EQUAL a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)
  | .LESSEQUAL a1 a2 => (fv_aexp a1) ∪ (fv_aexp a2)
  | .NOT b1 => fv_bexp b1
  | .AND b1 b2 => (fv_bexp b1) ∪ (fv_bexp b2)

@[grind] def fv_com (c: com) : IdentSet :=
  match c with
  | .SKIP => ∅
  | .ASSIGN x a => fv_aexp a
  | .SEQ c1 c2 => (fv_com c1) ∪ (fv_com c2)
  | .IFTHENELSE b c1 c2 => (fv_bexp b) ∪ ((fv_com c1) ∪ (fv_com c2))
  | .WHILE b c => (fv_bexp b) ∪ (fv_com c)


-- (** To analyze loops, we will need, again!, to compute post-fixpoints
--   of a function from sets of variables to sets of variables.
--   We reuse the ``engineer's approach'' from file [Constprop.v]. *)

-- Section FIXPOINT.

@[grind] noncomputable def fixpoint_rec (F : IdentSet → IdentSet) (default : IdentSet) (fuel: Nat) (x: IdentSet) : IdentSet :=
  match fuel with
  | 0 => default
  | fuel + 1 =>
      let x' := F x
      if x' ⊆ x then x else fixpoint_rec F default fuel x'

@[grind] noncomputable def fixpoint (F : IdentSet → IdentSet) (default : IdentSet): IdentSet :=
  fixpoint_rec F default 20 ∅

@[grind] theorem  fixpoint_charact' (n : Nat) (x : IdentSet)  (F : IdentSet → IdentSet) (default : IdentSet):
  ((F (fixpoint_rec F default n x)) ⊆ (fixpoint_rec F default n x)) ∨ (fixpoint_rec F default n x = default) := by
    induction n generalizing x <;> grind

theorem fixpoint_charact (F : IdentSet → IdentSet) (default : IdentSet) :
    ((F (fixpoint F default)) ⊆ (fixpoint F default)) ∨ (fixpoint F default = default) := by grind

theorem fixpoint_upper_bound (F : IdentSet → IdentSet) (default : IdentSet) (F_stable : ∀ x , x ⊆ default -> (F x) ⊆ default): fixpoint F default ⊆ default := by
  have : ∀ n : Nat, ∀ x : IdentSet, x ⊆ default → (fixpoint_rec F default n x) ⊆ default := by
    intro n
    induction n
    case zero =>
      intro x contained
      simp [fixpoint_rec]
      unfold Subset
      unfold instHasSubsetIdentSet
      grind
    case succ n ih =>
      unfold fixpoint_rec
      simp
      intro x hyp
      split
      case isTrue => grind
      case isFalse => grind
  apply this
  unfold Subset
  unfold instHasSubsetIdentSet
  grind

@[grind] noncomputable def live (c: com) (L: IdentSet) : IdentSet :=
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
      fixpoint (fun x => L' ∪ (live c x)) default

theorem live_upper_bound:
  forall c L,
   (live c L) ⊆ ((fv_com c) ∪  L) := by
    intro c
    induction c
    case SKIP =>
      intro L
      simp [fv_com, live]
      unfold Subset
      unfold instHasSubsetIdentSet
      grind
    case ASSIGN x a =>
      intro L
      simp [fv_com, live]
      split
      case isTrue h =>
        unfold Subset
        unfold instHasSubsetIdentSet
        grind
      case isFalse h =>
        unfold Subset
        unfold instHasSubsetIdentSet
        grind
    case SEQ c1 c2 c1_ih c2_ih =>
      intro L
      simp [live, fv_com]
      unfold Subset at *
      unfold instHasSubsetIdentSet at *
      simp at *
      intro x contained
      specialize c1_ih (live c2 L) x contained
      grind
    case IFTHENELSE b c1 c2 c1_ih c2_ih =>
      unfold Subset at *
      unfold instHasSubsetIdentSet at *
      simp at *
      grind
    case WHILE b c1 c1_ih =>
      simp [live, fv_com]
      intro L
      apply fixpoint_upper_bound
      intro x hyp
      intro y hyp2
      have : y ∈ fv_bexp b ∨ y ∈ L ∨ y ∈ live c1 x := by grind
      apply Or.elim this
      next =>
        intro hyp3
        grind
      next =>
        intro hyp3
        apply Or.elim hyp3
        next => grind
        next =>
          clear hyp3
          intro hyp3
          specialize c1_ih x y hyp3
          have : y ∈ fv_com c1 ∨ y ∈ x := by grind
          apply Or.elim this
          next => intros; grind
          next =>
            intro hyp4
            specialize hyp y hyp4
            grind

theorem live_while_charact (b : bexp) (c : com) (L L' : IdentSet)
  (eq : L' = live (.WHILE b c) L) :
  (fv_bexp b) ⊆ L' ∧ L ⊆ L' ∧ (live c L') ⊆ L' := by
    have hyp := fixpoint_charact (fun x : IdentSet => (fv_bexp b) ∪ L ∪ (live c x)) ((fv_bexp b) ∪ (fv_com c) ∪ L)
    apply Or.elim hyp
    case left =>
      intro included
      constructor
      case left =>
        intro y contained
        specialize included y (by grind)
        grind
      case right =>
        constructor
        case left =>
          intro y mem
          specialize included y (by grind)
          grind
        case right =>
          intro y mem
          rw [eq]
          specialize included y (by grind)
          grind
    case right =>
      intro equal
      constructor
      case left =>
        intro y mem
        grind
      case right =>
        constructor
        case left =>
          intro y mem
          grind
        case right =>
          intro y mem
          have := live_upper_bound c L' y mem
          grind

-- (** Dead code elimination turns assignments [x := a] to dead variables [x]
--   into [SKIP] statements. *)

@[grind] noncomputable def dce (c: com) (L: IdentSet): com :=
  match c with
  | .SKIP => .SKIP
  | .ASSIGN x a => if x ∈ L then .ASSIGN x a else .SKIP
  | .SEQ c1 c2 => .SEQ (dce c1 (live c2 L)) (dce c2 L)
  | .IFTHENELSE b c1 c2 => .IFTHENELSE b (dce c1 L) (dce c2 L)
  | .WHILE b c => .WHILE b (dce c (live (.WHILE b c) L))

-- (** Example of optimization. *)

-- Compute (dce Euclidean_division (IdentSet.singleton "r")).

-- (** Result is:
-- <<
--    r := a;                 ===>   r := a;
--    q := 0;                        skip;
--    while b <= r do                while b <= r do
--      r := r - b;                    r := r - b;
--      q := q + 1;                    skip;
--    done                           done
-- >>
-- *)

-- Compute (dce Euclidean_division (IdentSet.singleton "q")).

-- (** Program is unchanged. *)

-- (** ** 10.3  Correctness of the optimization *)

-- (** Two stores agree on a set [L] of live variables if they assign
--   the same values to each live variable. *)

@[grind] def agree (L: IdentSet) (s1 s2: store) : Prop :=
  forall x, x  ∈ L -> s1 x = s2 x

-- (** Monotonicity property. *)

@[grind] theorem agree_mon:
  forall L L' s1 s2,
  agree L' s1 s2 -> L ⊆ L' -> agree L s1 s2 := by
    intro L L' s1 s2 AG sub
    unfold agree at *
    intro x inL
    specialize sub x inL
    specialize AG x sub
    exact AG


-- (** Agreement on the free variables of an expression implies that this
--     expression evaluates identically in both stores. *)

@[grind] theorem aeval_agree:
  forall L s1 s2, agree L s1 s2 ->
  forall a, (fv_aexp a) ⊆ L -> aeval s1 a = aeval s2 a := by
    intro L s1 s2 AG a
    induction a
    any_goals grind
    case VAR x =>
      simp [fv_aexp]
      intro mem
      have : x ∈ L := by
        have := insert_characterisation ∅ x
        specialize mem x this
        exact mem
      simp [aeval]
      unfold agree at AG
      specialize AG x this
      exact AG
    case PLUS a1 a2 a1_ih a2_ih =>
      intro contained
      simp [aeval]
      congr 1
      next =>
        apply a1_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained
      next =>
        apply a2_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained
    case MINUS a1 a2 a1_ih a2_ih =>
      intro contained
      simp [aeval]
      congr 1
      next =>
        apply a1_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained
      next =>
        apply a2_ih
        simp [fv_aexp] at contained
        intro y mem
        specialize contained y (by grind)
        exact contained


theorem beval_agree:
  ∀ L s1 s2, agree L s1 s2 ->
  forall b, (fv_bexp b) ⊆ L -> beval s1 b = beval s2 b := by
    intro L s1 s2 AG b
    induction b
    any_goals grind
    case EQUAL a1 a2 =>
      intro cont
      unfold agree at AG
      simp [fv_bexp] at cont
      have aeval_lemma := aeval_agree L s1 s2 AG
      have subgoal1 : fv_aexp a1 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have subgoal2 : fv_aexp a2 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have eq1 := aeval_lemma a1 subgoal1
      have eq2 := aeval_lemma a2 subgoal2
      grind
    case LESSEQUAL a1 a2 =>
      intro cont
      unfold agree at AG
      simp [fv_bexp] at cont
      have aeval_lemma := aeval_agree L s1 s2 AG
      have subgoal1 : fv_aexp a1 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have subgoal2 : fv_aexp a2 ⊆ L := by
        intro y mem
        specialize cont y (by grind)
        exact cont
      have eq1 := aeval_lemma a1 subgoal1
      have eq2 := aeval_lemma a2 subgoal2
      grind
    case AND b1 b2 b1_ih b2_ih =>
      intro cont
      simp [fv_bexp] at cont
      have : fv_bexp b1 ⊆ L ∧ fv_bexp b2 ⊆ L := by
        constructor
        case left =>
          intro y mem
          specialize cont y (by grind)
          exact cont
        case right =>
          intro y mem
          specialize cont y (by grind)
          exact cont
      specialize b1_ih (by grind)
      specialize b2_ih (by grind)
      grind











--   induction b; simpl; intros.
-- - auto.
-- - auto.
-- - rewrite ! (aeval_agree L s1 s2); auto; fsetdec.
-- - rewrite ! (aeval_agree L s1 s2); auto; fsetdec.
-- - f_equal; apply IHb; auto.
-- - f_equal. apply IHb1; fsetdec. apply IHb2; fsetdec.
-- Qed.

-- (** Agreement is preserved by simultaneous assignment to a live variable. *)

-- Lemma agree_update_live:
--   forall s1 s2 L x v,
--   agree (IdentSet.remove x L) s1 s2 ->
--   agree L (update x v s1) (update x v s2).
-- Proof.
--   intros; red; intros. unfold update. destruct (string_dec x x0).
-- - auto.
-- - apply H. apply IdentSet.remove_2. auto. auto.
-- Qed.

-- (** Agreement is also preserved by unilateral assignment to a dead variable. *)

-- Lemma agree_update_dead:
--   forall s1 s2 L x v,
--   agree L s1 s2 -> ~IdentSet.In x L ->
--   agree L (update x v s1) s2.
-- Proof.
--   intros; red; intros. unfold update. destruct (string_dec x x0).
-- - subst x0. contradiction.
-- - apply H; auto.
-- Qed.

-- (** We now show that dead code elimination preserves semantics for terminating
--   source program.  We use big-step semantics to show the following diagram:
-- <<
--                 agree (live c L) s s1
--      c / s ----------------------------- dce C L / s1
--        |                                          |
--        |                                          |
--        |                                          |
--        v                                          v
--       s' -------------------------------------- s1'
--                     agree L s' s1'
-- >>
--   The proof is a simple induction on the big-step evaluation derivation on the left. *)

-- Theorem dce_correct_terminating:
--   forall s c s', cexec s c s' ->
--   forall L s1, agree (live c L) s s1 ->
--   exists s1', cexec s1 (dce c L) s1' /\ agree L s' s1'.
-- Proof.
--   induction 1; intros; cbn [dce].

-- - (* skip *)
--   exists s1; split. apply cexec_skip. auto.

-- - (* assign *)
--   cbn in H. destruct (IdentSet.mem x L) eqn:LIVE_AFTER.
--   + (* x is live after *)
--     assert (EQ: aeval s a = aeval s1 a).
--     { eapply aeval_agree. eauto. fsetdec. }
--     exists (update x (aeval s1 a) s1); split.
--     apply cexec_assign.
--     rewrite EQ. apply agree_update_live. eapply agree_mon. eauto. fsetdec.
--   + (* x is dead after *)
--     exists s1; split.
--     apply cexec_skip.
--     apply agree_update_dead. auto.
--     rewrite ISFact.mem_iff. congruence.

-- - (* seq *)
--   cbn in H1.
--   destruct (IHcexec1 _ _ H1) as [s1' [E1 A1]].
--   destruct (IHcexec2 _ _ A1) as [s2' [E2 A2]].
--   exists s2'; split.
--   apply cexec_seq with s1'; auto.
--   auto.

-- - (* ifthenelse *)
--   cbn in H0.
--   assert (EQ: beval s b = beval s1 b).
--   { eapply beval_agree. eauto. fsetdec. }
--   destruct (IHcexec L s1) as [s1' [E A]].
--     eapply agree_mon; eauto. destruct (beval s b); fsetdec.
--   exists s1'; split.
--   apply cexec_ifthenelse. rewrite <- EQ. destruct (beval s b); auto.
--   auto.

-- - (* while done *)
--   destruct (live_while_charact b c L) as [P [Q R]].
--   assert (beval s1 b = false).
--   { rewrite <- H. symmetry. eapply beval_agree; eauto. }
--   exists s1; split.
--   apply cexec_while_done. auto.
--   eapply agree_mon; eauto.

-- - (* while loop *)
--   destruct (live_while_charact b c L) as [P [Q R]].
--   assert (beval s1 b = true).
--   { rewrite <- H. symmetry. eapply beval_agree; eauto. }
--   destruct (IHcexec1 (live (WHILE b c) L) s1) as [s2 [E1 A1]].
--     eapply agree_mon; eauto.
--   destruct (IHcexec2 L s2) as [s3 [E2 A2]].
--     auto.
--   exists s3; split.
--   apply cexec_while_loop with s2; auto.
--   auto.
-- Qed.
