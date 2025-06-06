import «Leroy».Imp
import «Leroy».Constprop
import Init.WF
import Std.Data.HashMap
import Std.Data.HashMap.Lemmas
import Batteries.Data.List.Basic
import Batteries.Data.List.Perm
import Init.Data.List.Pairwise
import Init.Data.List.Sublist
import Init.Data.List.Basic


universe u

set_option grind.warning false

section Fixpoints

@[grind] class OrderStruct (α : Sort u) where
  eq : α → α → Prop
  le : α → α → Prop
  beq : α → α → Bool
  beq_true : ∀ x y : α, beq x y = true → eq x y
  beq_false : ∀ x y : α, beq x y = false → ¬ eq x y
  F : α → α
  F_mon: ∀ x y, le x y -> le (F x) (F y)
  le_trans: ∀ x y z, le x y -> le y z -> le x z
  bot : α
  bot_smallest : ∀ x, le bot x
open OrderStruct

@[grind] def gt {α : Sort u} [OrderStruct α] (x y : α) := le y x ∧ ¬eq y x

@[grind] class WellFoundedOrderStruct (α : Sort u) extends OrderStruct α where
  gt_wf : WellFounded (@gt α _)

variable ( α : Sort u ) [inst:  WellFoundedOrderStruct α]
open WellFoundedOrderStruct

instance : WellFoundedRelation α  where
  rel := gt
  wf := gt_wf

theorem fixpoint_exists_1: ∃ x : α, eq x (F x) := by
  have REC : forall x : α, le x (F x) -> exists y : α , eq y (F y) := by
    intro x
    induction x using @WellFounded.induction α gt gt_wf
    case h x ih =>
      intro h
      by_cases (beq x (F x))
      case pos isTrue =>
        exists x
        grind [OrderStruct.beq_true]
      case neg isFalse =>
        specialize ih (F x)
        grind [OrderStruct.beq_false, gt, OrderStruct.F_mon]
  specialize REC bot
  apply REC
  apply bot_smallest

@[grind] def iterate (x : α) (PRE: le x (F x)) (SMALL: forall z, le (F z) z -> le x z) : α :=
  if beq x (F x) then x else iterate (F x) (by apply OrderStruct.F_mon; exact PRE) (by intro z hyp; specialize SMALL z hyp; apply le_trans; apply F_mon; exact SMALL; exact hyp)
termination_by x
decreasing_by
  rename_i h
  unfold gt
  grind [OrderStruct.beq_false]

@[grind] theorem iterate_correct (x : α) (PRE: le x (F x)) (SMALL: forall z, le (F z) z -> le x z) (heq : y = iterate _ x PRE SMALL ) : eq y (F y) ∧ ∀ z, le (F z) z → le y z := by
  fun_induction iterate
  case case1 x' PRE SMALL isTrue  =>
    constructor
    . rw [←heq] at PRE
      grind [OrderStruct.beq_true]
    . intro z hyp
      specialize SMALL z hyp
      grind
  case case2 ih =>
    have := @ih heq
    grind

@[grind] def fixpoint' : α := iterate α bot (by apply bot_smallest) (by intro z pre; apply bot_smallest)

theorem fixpoint_correct : inst.eq (@fixpoint' α _) (F (@fixpoint' _ _)) /\ forall z : α , le (F z) z -> le (@fixpoint' _ _) z := by
  unfold fixpoint'
  have PRE : inst.le (bot) (F bot) := by apply bot_smallest
  have SMALL : ∀ z, le (F z) z -> inst.le bot z := by
    intro z hyp
    apply le_trans
    rotate_left
    . exact hyp
    . apply bot_smallest
  have := @iterate_correct α inst (iterate α bot PRE SMALL) bot PRE SMALL (rfl)
  grind

end Fixpoints

@[grind] def Eq' (S1 S2 : Store) : Prop := Equal S1 S2

def Eq'_sym : ∀ S1 S2, Eq' S1 S2 → Eq' S2 S1 := by
  intro S1 S2 hyp
  unfold Eq' Equal at *
  grind [Std.HashMap.Equiv.symm]

@[grind] theorem Equal_Eq' : ∀ S1 S2, (Equal S1 S2 == true) → Eq' S1 S2 := by grind

@[grind] theorem Equal_nEq : ∀ S1 S2, (Equal S1 S2 == false) → ¬Eq' S1 S2 := by grind

@[grind] theorem Eq_Le : ∀ S1 S2, Eq' S1 S2 → Le S1 S2 := by
  intro S1 S2 heq
  unfold Le
  intro x n heq2
  unfold Eq' Equal  at heq
  simp at *
  grind [Std.HashMap.Equiv.getElem?_eq]

@[grind] theorem Le_trans : ∀ S1 S2 S3, Le S1 S2 → Le S2 S3 → Le S1 S3 := by grind

@[grind] def Gt (S1 S2 : Store) := Le S2 S1 ∧ ¬ Eq' S2 S1

@[grind] def Increasing (F : Store → Store) := ∀ x y, Le x y → Le (F x) (F y)

theorem hash_set_incl_size_leq (S1 S2 : Store) : Le S2 S1 → List.Subperm (S1.toList) (S2.toList) := by
  intro LE
  unfold Le at LE
  apply List.subperm_of_subset
  . apply List.Pairwise.imp
    rotate_left
    . exact Std.HashMap.distinct_keys_toList
    . grind
  . intro (k,v) mem
    specialize LE k v (by grind)
    grind

@[grind] theorem Le_cardinal:
  ∀ S T : Store,
  Le T S ->
  S.size <= T.size ∧ (S.size = T.size → Equal S T) := by
    intro S T hyp
    have size_eq : ∀ (S : Store), S.size = S.toList.length := by grind [Std.HashMap.length_toList]
    rw [size_eq S, size_eq T]
    constructor
    case left =>
      exact List.Subperm.length_le (hash_set_incl_size_leq S T hyp)
    case right =>
      intro eqLen
      unfold Equal
      apply Std.HashMap.Equiv.of_toList_perm
      apply List.Subperm.perm_of_length_le (hash_set_incl_size_leq S T hyp)
      grind

@[grind] theorem Gt_cardinal:
  forall S S', Gt S S' -> S.size < S'.size := by
    intro S S' hyp
    unfold Gt at hyp
    have ⟨ t₁, t₂ ⟩ := @Le_cardinal S S' (hyp.1)
    apply Nat.lt_of_le_of_ne
    case h₁ => exact t₁
    case h₂ =>
      apply Classical.byContradiction
      intro h
      simp at h
      grind

theorem Gt_wf : WellFounded Gt := by
  have := @InvImage Store Nat Nat.lt fun x => x.size
  have : ∀ (x y : Store), Gt x y → @InvImage Store Nat Nat.lt (fun x => x.size) x y := by
    intro x y heq
    unfold InvImage
    simp
    apply Gt_cardinal
    exact heq
  have subrel : Subrelation Gt (InvImage Nat.lt (fun x : Store => x.size)) := by
    intro x y gt; grind
  apply @Subrelation.wf Store (InvImage Nat.lt (fun x : Store => x.size)) Gt subrel
  exact InvImage.wf (fun x : Store => x.size) (Nat.lt_wfRel.wf)


-- Section FIXPOINT_JOIN.

-- Variable Init: Store.
-- Variable F: Store -> Store.
-- Hypothesis F_incr: Increasing F.

-- instance : WellFoundedOrderStruct Store where
--   eq := Eq'
--   le := Le
--   beq := fun x y => decide (Equal x y)
--   beq_true := fun x y hyp => Equal_Eq' x y (by grind)
--   beq_false := fun x y hyp => Equal_nEq x y (by grind)
--   bot := sorry
--   bot_smallest := sorry
--   F := sorry
--   F_mon := sorry
--   le_trans := Le_trans
--   gt_wf := Gt_wf


-- def fixpoint_join (Init : Store) (F : Store → Store) (F_incr : Increasing F) : Store := by
--   have := @iterate Store

-- Program Definition fixpoint_join : Store :=
--   iterate Store Eq Equal Equal_Eq Equal_nEq Le Le_trans Gt_wf
--           (fun x => Join Init (F x)) _ Init _ _.
-- Next Obligation.
--   unfold Le; intros.
--   apply Join_characterization in H0. destruct H0 as [FIND1 FIND2].
--   apply Join_characterization. split; auto. apply (F_incr _ _ H). auto.
-- Qed.
-- Next Obligation.
--   apply Le_Join_l.
-- Qed.
-- Next Obligation.
--   eapply Le_trans. apply Le_Join_l. eauto.
-- Qed.

-- Lemma fixpoint_join_eq:
--   Eq (Join Init (F fixpoint_join)) fixpoint_join.
-- Proof.
--   apply Eq_sym. unfold fixpoint_join.
--   destruct iterate as (X & EQ & SMALL). auto.
-- Qed.

-- Lemma fixpoint_join_sound:
--   Le Init fixpoint_join /\ Le (F fixpoint_join) fixpoint_join.
-- Proof.
--   assert (LE: Le (Join Init (F fixpoint_join)) fixpoint_join).
--   { apply Eq_Le. apply fixpoint_join_eq. }
--   split.
-- - eapply Le_trans. apply Le_Join_l. eauto.
-- - eapply Le_trans. apply Le_Join_r. eauto.
-- Qed.

-- Lemma fixpoint_join_smallest:
--   forall S, Le (Join Init (F S)) S -> Le fixpoint_join S.
-- Proof.
--   unfold fixpoint_join. destruct iterate as (X & EQ & SMALL).
--   auto.
-- Qed.

-- End FIXPOINT_JOIN.

-- (** Now we can try to use the [fixpoint_join] function above in the [Cexec]
--   static analyzer.  But we are in for a surprise!
-- *)

theorem Join_increasing:
  forall S1 S2 S3 S4,
  Le S1 S2 -> Le S3 S4 -> Le (Join S1 S3) (Join S2 S4) := by
    intros
    grind

@[grind] theorem Aeval_increasing: ∀ S1 S2, Le S1 S2 ->
  forall a n, Aeval S2 a = .some n -> Aeval S1 a =.some n := by
    intro S1 S2 LE a
    induction a <;> grind

theorem Beval_increasing : ∀ S1 S2, Le S1 S2 ->
  forall b n, Beval S2 b = .some n -> Beval S1 b = .some n := by
    intro S1 S2 LE b
    induction b
    any_goals grind
    case NOT b1 b1_ih =>
      intro n ev
      simp [Beval, lift1] at ev
      grind

theorem Update_increasing:
  forall S1 S2 x a,
  Le S1 S2 ->
  Le (Update x (Aeval S1 a) S1) (Update x (Aeval S2 a) S2) := by
    intros; grind


-- Lemma fixpoint_Join_increasing:
--   forall F (F_incr: Increasing F) S1 S2,
--   Le S1 S2 -> Le (fixpoint_join S1 F F_incr) (fixpoint_join S2 F F_incr).
-- Proof.
--   intros. apply fixpoint_join_smallest.
--   set (fix2 := fixpoint_join S2 F F_incr).
--   assert (Le (Join S2 (F fix2)) fix2) by (apply Eq_Le; apply fixpoint_join_eq).
--   eapply Le_trans; eauto.
--   apply Join_increasing; auto. unfold Le; auto.
-- Qed.

-- (** At long last, we can define [Cexec] while at the same time showing that
--   it is increasing. *)

-- Program Fixpoint Cexec (c: com) : { F: Store -> Store | Increasing F } :=
--   match c with
--   | SKIP => fun S => S
--   | ASSIGN x a => fun S => Update x (Aeval S a) S
--   | SEQ c1 c2 => compose (Cexec c2) (Cexec c1)
--   | IFTHENELSE b c1 c2 =>
--       fun S =>
--       match Beval S b return _ with
--       | Some true => Cexec c1 S
--       | Some false => Cexec c2 S
--       | None => Join (Cexec c1 S) (Cexec c2 S)
--       end
--   | WHILE b c1 =>
--       fun S => fixpoint_join S (fun S => Cexec c1 S) _
--   end.
-- Next Obligation.
--   unfold Increasing. auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. apply Update_increasing; auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. unfold compose. auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. destruct (Beval z b) as [bz|] eqn:BEV.
--   erewrite Beval_increasing by eauto. destruct bz; auto.
--   destruct (Beval y b) as [[]|].
--   apply Le_trans with (x z). auto. apply Le_Join_l.
--   apply Le_trans with (x0 z). auto. apply Le_Join_r.
--   apply Join_increasing; auto.
-- Defined.
-- Next Obligation.
--   intros y z LE. apply fixpoint_Join_increasing. auto.
-- Defined.
