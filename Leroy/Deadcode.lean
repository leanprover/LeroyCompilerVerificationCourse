import «Leroy».Sequences
import «Leroy».Imp
import Init.Data.List.Basic
import Std.Data.HashSet
import Std.Data.HashSet.Lemmas

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

def IdentSet := Std.HashSet ident

-- (** ** 10.1 Liveness analysis *)

-- (** Computation of the set of variables appearing in an expression or command. *)

@[grind] def fv_aexp (a: aexp) : IdentSet :=
  match a with
  | .CONST _ => Std.HashSet.emptyWithCapacity
  | .VAR v => Std.HashSet.instSingleton.singleton v
  | .PLUS a1 a2 => Std.HashSet.union (fv_aexp a1) (fv_aexp a2)
  | .MINUS a1 a2 => Std.HashSet.union (fv_aexp a1) (fv_aexp a2)


@[grind] def fv_bexp (b: bexp) : IdentSet :=
  match b with
  | .TRUE => Std.HashSet.emptyWithCapacity
  | .FALSE => Std.HashSet.emptyWithCapacity
  | .EQUAL a1 a2 => Std.HashSet.union (fv_aexp a1) (fv_aexp a2)
  | .LESSEQUAL a1 a2 => Std.HashSet.union (fv_aexp a1) (fv_aexp a2)
  | .NOT b1 => fv_bexp b1
  | .AND b1 b2 => Std.HashSet.union  (fv_bexp b1) (fv_bexp b2)

@[grind] def fv_com (c: com) : IdentSet :=
  match c with
  | .SKIP => Std.HashSet.emptyWithCapacity
  | .ASSIGN x a => fv_aexp a
  | .SEQ c1 c2 => Std.HashSet.union (fv_com c1) (fv_com c2)
  | .IFTHENELSE b c1 c2 => Std.HashSet.union (fv_bexp b) (Std.HashSet.union (fv_com c1) (fv_com c2))
  | .WHILE b c => Std.HashSet.union (fv_bexp b) (fv_com c)

@[grind] def subset (a b :  IdentSet ): Bool := a.all (b.contains)

@[grind] theorem subset_empty : subset (a) Std.HashSet.emptyWithCapacity → False := by
  sorry

@[grind] theorem subset_idem : subset a a := by sorry

-- (** To analyze loops, we will need, again!, to compute post-fixpoints
--   of a function from sets of variables to sets of variables.
--   We reuse the ``engineer's approach'' from file [Constprop.v]. *)

-- Section FIXPOINT.

def fixpoint_rec (F : IdentSet → IdentSet) (default : IdentSet) (fuel: Nat) (x: IdentSet) : IdentSet :=
  match fuel with
  | 0 => default
  | fuel + 1 =>
      let x' := F x
      if subset x' x then x else fixpoint_rec F default fuel x'


def fixpoint (F : IdentSet → IdentSet) (default : IdentSet)  : IdentSet :=
  fixpoint_rec F default 20 Std.HashSet.emptyWithCapacity

theorem  fixpoint_charact (F : IdentSet → IdentSet) (default : IdentSet):
  (subset (F (fixpoint F default)) (fixpoint F default)) ∨ (fixpoint F default = default) := by
    unfold fixpoint
    generalize heq : 20 = n
    clear heq
    induction n
    case zero =>
      sorry








--   unfold fixpoint. generalize 20%nat, IdentSet.empty. induction n; intros; cbn.
-- - auto.
-- - destruct (IdentSet.subset (F t) t) eqn:SUBSET.
-- + left. apply IdentSet.subset_2; auto.
-- + apply IHn.
-- Qed.

-- Hypothesis F_stable:
--   forall x, IdentSet.Subset x default -> IdentSet.Subset (F x) default.

-- Lemma fixpoint_upper_bound:
--   IdentSet.Subset fixpoint default.
-- Proof.
--   assert (forall n x, IdentSet.Subset x default -> IdentSet.Subset (fixpoint_rec n x) default).
--   { induction n; intros; cbn.
--   - red; auto.
--   - destruct (IdentSet.subset (F x) x) eqn:SUBSET.
--     + auto.
--     + apply IHn; auto.
--   }
--   unfold fixpoint. apply H. apply ISProp.subset_empty.
-- Qed.

-- End FIXPOINT.

-- (** ** Liveness analysis. *)

-- (** [L] is the set of variables live "after" command [c].
--   The result of [live c L] is the set of variables live "before" [c]. *)

-- Fixpoint live (c: com) (L: IdentSet.t) : IdentSet.t :=
--   match c with
--   | SKIP => L
--   | ASSIGN x a =>
--       if IdentSet.mem x L
--       then IdentSet.union (IdentSet.remove x L) (fv_aexp a)
--       else L
--   | SEQ c1 c2 =>
--       live c1 (live c2 L)
--   | IFTHENELSE b c1 c2 =>
--       IdentSet.union (fv_bexp b) (IdentSet.union (live c1 L) (live c2 L))
--   | WHILE b c =>
--       let L' := IdentSet.union (fv_bexp b) L in
--       let default := IdentSet.union (fv_com (WHILE b c)) L in
--       fixpoint (fun x => IdentSet.union L' (live c x)) default
--   end.

-- Lemma live_upper_bound:
--   forall c L,
--   IdentSet.Subset (live c L) (IdentSet.union (fv_com c) L).
-- Proof.
--   induction c; intros; simpl.
-- - fsetdec.
-- - destruct (IdentSet.mem x L) eqn:MEM. fsetdec. fsetdec.
-- - specialize (IHc1 (live c2 L)). specialize (IHc2 L). fsetdec.
-- - specialize (IHc1 L). specialize (IHc2 L). fsetdec.
-- - apply fixpoint_upper_bound. intro x. specialize (IHc x). fsetdec.
-- Qed.

-- Lemma live_while_charact:
--   forall b c L,
--   let L' := live (WHILE b c) L in
--   IdentSet.Subset (fv_bexp b) L' /\ IdentSet.Subset L L' /\ IdentSet.Subset (live c L') L'.
-- Proof.
--   intros.
--   specialize (fixpoint_charact
--     (fun x : IdentSet.t => IdentSet.union (IdentSet.union (fv_bexp b) L) (live c x))
--           (IdentSet.union (IdentSet.union (fv_bexp b) (fv_com c)) L)).
--   simpl in L'. fold L'. intros [A|A].
-- - split. fsetdec. split; fsetdec.
-- - split. rewrite A. fsetdec.
--   split. rewrite A. fsetdec.
--   eapply ISProp.subset_trans. apply live_upper_bound. rewrite A. fsetdec.
-- Qed.

-- (** ** 10.2 The optimization: dead code elimination *)

-- (** Dead code elimination turns assignments [x := a] to dead variables [x]
--   into [SKIP] statements. *)

-- Fixpoint dce (c: com) (L: IdentSet.t): com :=
--   match c with
--   | SKIP => SKIP
--   | ASSIGN x a => if IdentSet.mem x L then ASSIGN x a else SKIP
--   | SEQ c1 c2 => SEQ (dce c1 (live c2 L)) (dce c2 L)
--   | IFTHENELSE b c1 c2 => IFTHENELSE b (dce c1 L) (dce c2 L)
--   | WHILE b c => WHILE b (dce c (live (WHILE b c) L))
--   end.

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

-- Definition agree (L: IdentSet.t) (s1 s2: store) : Prop :=
--   forall x, IdentSet.In x L -> s1 x = s2 x.

-- (** Monotonicity property. *)

-- Lemma agree_mon:
--   forall L L' s1 s2,
--   agree L' s1 s2 -> IdentSet.Subset L L' -> agree L s1 s2.
-- Proof.
--   unfold IdentSet.Subset, agree; intros. auto.
-- Qed.

-- (** Agreement on the free variables of an expression implies that this
--     expression evaluates identically in both stores. *)

-- Lemma aeval_agree:
--   forall L s1 s2, agree L s1 s2 ->
--   forall a, IdentSet.Subset (fv_aexp a) L -> aeval s1 a = aeval s2 a.
-- Proof.
--   induction a; simpl; intros.
-- - auto.
-- - apply H. fsetdec.
-- - f_equal. apply IHa1. fsetdec. apply IHa2. fsetdec.
-- - f_equal. apply IHa1. fsetdec. apply IHa2. fsetdec.
-- Qed.

-- Lemma beval_agree:
--   forall L s1 s2, agree L s1 s2 ->
--   forall b, IdentSet.Subset (fv_bexp b) L -> beval s1 b = beval s2 b.
-- Proof.
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

-- (** *** Exercise (3 stars, optional) *)

-- (** To prove semantic preservation both for terminating and diverging programs.
--   complete the following simulation proof, which uses the small-step semantics
--   of Imp, without continuations. *)

-- Fixpoint measure (c: com) : nat :=
--   match c with
--   | ASSIGN x a => 1%nat
--   | SEQ c1 c2 => measure c1
--   | _ => 0%nat
--   end.

-- Theorem dce_simulation:
--   forall c s c' s',
--   red (c, s) (c', s') ->
--   forall L s1,
--   agree (live c L) s s1 ->
--   (exists s1',
--    red (dce c L, s1) (dce c' L, s1') /\ agree (live c' L) s' s1')
--   \/
--   (measure c' < measure c /\ dce c L = dce c' L /\ agree (live c' L) s' s1)%nat.
-- Proof.
--    intros until s'. intro STEP. dependent induction STEP; intros; cbn [dce].
--   (* FILL IN HERE *)
-- Abort.
